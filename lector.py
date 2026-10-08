#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
=============================================================================
 LECTOR DE FACTURAS DE PROVEEDORES — Lucciano's
 Corre en GitHub Actions cada 15 minutos (o a mano: python lector.py).

 Para cada factura "recibida" en el Worker:
   1. Baja el PDF y lee el QR de ARCA (sin IA): CUIT, tipo, PV, número,
      fecha, total, CAE y receptor.
   2. Saca el texto del PDF y arma pares "etiqueta → importe".
   3. Si el proveedor tiene CONFIGURACIÓN (plantilla) → la aplica. Sin IA.
      Si no cuadra al centavo con el total del QR → "el formato cambió".
   4. Si el proveedor es NUEVO → prueba el lector de reglas generales;
      si no alcanza, lee con Gemini. Una persona confirma esa primera
      factura y el Worker guarda la configuración del proveedor.
   5. Le devuelve el resultado al Worker, que imputa, constata en ARCA y valida.

 Variables de entorno (en GitHub: Settings → Secrets and variables → Actions):
   WORKER_URL       https://facturas-api.<subdominio>.workers.dev
   LECTOR_SECRET    mismo valor que LECTOR_SECRET en el Worker
   GEMINI_API_KEY   key de Google AI Studio (solo se usa con proveedores nuevos)
   GEMINI_MODEL     opcional, default gemini-2.5-pro
=============================================================================
"""
from __future__ import annotations

import base64
import io
import itertools
import json
import os
import re
import sys
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request

import pymupdf
import zxingcpp
from PIL import Image

VERSION = '1.0.0'
RATES = [21.0, 10.5, 27.0, 5.0, 2.5]
TOL = 0.02

# ---------------------------------------------------------------------------
#  Comunicación con el Worker
# ---------------------------------------------------------------------------
def _req(method, path, body=None, raw=False, timeout=90):
    url = os.environ['WORKER_URL'].rstrip('/') + path
    data = json.dumps(body).encode('utf-8') if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers={
        'Content-Type': 'application/json', 'X-Lector-Secret': os.environ['LECTOR_SECRET'],
        'User-Agent': f'facturas-lector/{VERSION}'})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            contenido = r.read()
    except urllib.error.HTTPError as e:
        raise RuntimeError(f'Worker {method} {path} → HTTP {e.code}: {e.read().decode("utf-8", "replace")[:300]}')
    return contenido if raw else json.loads(contenido.decode('utf-8'))


# ---------------------------------------------------------------------------
#  Utilidades de texto y números
# ---------------------------------------------------------------------------
def norm(s):
    return re.sub(r'\s+', ' ', unicodedata.normalize('NFD', str(s or '')).encode('ascii', 'ignore').decode().upper()).strip()


def clave_etiqueta(label):
    """Forma canónica de una etiqueta: es lo que se guarda en la configuración del proveedor."""
    s = norm(label)
    s = re.sub(r'[^A-Z0-9%.,/() ]', ' ', s)
    s = re.sub(r'\s+', ' ', s).strip(' .:,')
    return s


MONEY = re.compile(r'^-?\d{1,3}(?:[.,]\d{3})+[.,]\d{2}$|^-?\d+[.,]\d{2}$')


def money(tok):
    t = str(tok).replace('ARS', '').replace('USD', '').strip().lstrip('$').strip()
    if not MONEY.match(t):
        return None
    ent = t[:-3].replace('.', '').replace(',', '')
    return round(float(ent + '.' + t[-2:]), 2)


def cuit_valido(c):
    s = re.sub(r'\D', '', str(c or ''))
    if len(s) != 11:
        return False
    w = [5, 4, 3, 2, 7, 6, 5, 4, 3, 2]
    dv = 11 - sum(int(s[i]) * w[i] for i in range(10)) % 11
    dv = 0 if dv == 11 else (9 if dv == 10 else dv)
    return dv == int(s[10])


def fecha_iso(s):
    s = str(s or '').strip()
    m = re.match(r'^(\d{4})-(\d{1,2})-(\d{1,2})', s)
    if m:
        return f'{m.group(1)}-{int(m.group(2)):02d}-{int(m.group(3)):02d}'
    m = re.search(r'(\d{1,2})\s*[/.\-]\s*(\d{1,2})\s*[/.\-]\s*(\d{2,4})', s)
    if m:
        y = int(m.group(3)); y = y + 2000 if y < 100 else y
        return f'{y}-{int(m.group(2)):02d}-{int(m.group(1)):02d}'
    m = re.search(r'\b(20\d{2})(\d{2})(\d{2})\b', s)
    if m:
        return f'{m.group(1)}-{m.group(2)}-{m.group(3)}'
    return None


# ---------------------------------------------------------------------------
#  PDF: texto por renglones (columnas separadas por 2+ espacios) y QR
# ---------------------------------------------------------------------------
def texto_pdf(doc):
    lineas = []
    for page in doc:
        words = page.get_text('words')
        filas = []
        for w in sorted(words, key=lambda w: ((w[1] + w[3]) / 2, w[0])):
            yc = (w[1] + w[3]) / 2
            if filas and abs(filas[-1][0] - yc) < 3.5:
                filas[-1][1].append(w)
            else:
                filas.append([yc, [w]])
        for _, ws in filas:
            ws.sort(key=lambda w: w[0])
            s, prev = '', None
            for w in ws:
                if prev is not None:
                    s += '   ' if w[0] - prev > 6 else ' '
                s += w[4]
                prev = w[2]
            lineas.append(s)
        lineas.append('')
    return '\n'.join(lineas)


def _decodificar_qr(texto):
    m = re.search(r'[?&]p=([^&\s]+)', texto or '')
    if not m:
        return None
    b = urllib.parse.unquote(m.group(1)).replace('-', '+').replace('_', '/')
    b += '=' * (-len(b) % 4)
    try:
        q = json.loads(base64.b64decode(b).decode('utf-8'))
    except Exception:
        return None
    return {
        'fecha': fecha_iso(q.get('fecha')),
        'cuit_emisor': re.sub(r'\D', '', str(q.get('cuit', ''))),
        'pto_vta': int(q['ptoVta']) if q.get('ptoVta') is not None else None,
        'tipo': int(q['tipoCmp']) if q.get('tipoCmp') is not None else None,
        'numero': int(q['nroCmp']) if q.get('nroCmp') is not None else None,
        'total': round(float(q.get('importe', 0)), 2),
        'moneda': q.get('moneda') or 'PES',
        'cotizacion': float(q.get('ctz') or 1),
        'doc_receptor': re.sub(r'\D', '', str(q.get('nroDocRec', ''))),
        'tipo_autorizacion': 'CAEA' if q.get('tipoCodAut') == 'A' else 'CAE',
        'cae': re.sub(r'\D', '', str(q.get('codAut', ''))),
    }


def leer_qr(doc):
    # 1) links embebidos
    for page in doc:
        for l in page.get_links():
            q = _decodificar_qr(l.get('uri', ''))
            if q:
                return q, 'link'
    # 2) imágenes embebidas
    for page in doc:
        for im in page.get_images(full=True):
            try:
                pix = pymupdf.Pixmap(doc, im[0])
                if pix.n - pix.alpha >= 4:
                    pix = pymupdf.Pixmap(pymupdf.csRGB, pix)
                for r in zxingcpp.read_barcodes(Image.open(io.BytesIO(pix.tobytes('png')))):
                    q = _decodificar_qr(r.text)
                    if q:
                        return q, 'imagen'
            except Exception:
                continue
    # 3) página renderizada (QR dibujado con vectores)
    for page in list(doc)[:2]:
        for zoom in (2, 3):
            img = Image.open(io.BytesIO(page.get_pixmap(matrix=pymupdf.Matrix(zoom, zoom)).tobytes('png')))
            for r in zxingcpp.read_barcodes(img):
                q = _decodificar_qr(r.text)
                if q:
                    return q, 'render'
    return None, None


# ---------------------------------------------------------------------------
#  Pares etiqueta → importe
# ---------------------------------------------------------------------------
JURIS = [('CABA', r'CABA|CAPITAL FEDERAL|CAP\.? ?FED|AGIP|C\.A\.B\.A|CIUDAD AUTONOMA'),
         ('BUENOS AIRES', r'ARBA|BUENOS AIRES|\bPBA\b|BS\.? ?AS|PCIA\.? ?BS'),
         ('CORDOBA', r'CORDOBA'), ('SANTA FE', r'SANTA FE'), ('MENDOZA', r'MENDOZA'), ('SALTA', r'SALTA'),
         ('TUCUMAN', r'TUCUMAN'), ('NEUQUEN', r'NEUQUEN'), ('CHACO', r'CHACO'), ('MISIONES', r'MISIONES'),
         ('RIO NEGRO', r'RIO NEGRO'), ('CHUBUT', r'CHUBUT'), ('CORRIENTES', r'CORRIENTES'),
         ('LA PAMPA', r'LA PAMPA'), ('TIERRA DEL FUEGO', r'TIERRA DEL FUEGO')]


def juris(label):
    L = norm(label)
    return next((j for j, rx in JURIS if re.search(rx, L)), None)


def clasif(label):
    L = norm(label)
    if not L or re.search(r'TOTAL (IMPUESTOS|UNIDADES|BULTOS|KILOS)|CANTIDAD TOTAL|^SON\b|IVA CONTENIDO|TRANSPARENCIA', L):
        return None
    if re.search(r'PERC|RG ?5329|RG ?2408|RG ?3337', L) and re.search(r'I\.?V\.?A|5329|2408|3337', L):
        return 'PERC_IVA'
    if re.search(r'PERC.*GANAN', L):
        return 'PERC_GAN'
    if re.search(r'PERC|IIBB|INGRESOS BRUTOS|AGIP|ARBA|\bIB\b|\bII\.?BB', L):
        return 'PERC_IIBB' if (re.search(r'IIBB|INGRESOS BRUTOS|AGIP|ARBA|\bIB\b|II\.?BB', L) or juris(label)) else 'PERC_GEN'
    if re.search(r'EXENTO', L) and not re.search(r'NO GRAVADO', L):
        return 'EXENTO'
    if re.search(r'NO GRAVADO|EXENTO', L):
        return 'NOGRAV'
    if re.search(r'OTROS TRIBUTOS|IMP\.? INT|IMPUESTOS? INTERNOS', L):
        return 'OTROS'
    if re.search(r'\bI\.?V\.?A\.?\b|IVA INSC', L):
        return 'IVA'
    if re.search(r'NETO|SUBTOTAL|SUB TOTAL|GRAVADO|BASE (IMPONIBLE|GRAV)', L):
        return 'NETO'
    if re.search(r'\bTOTAL\b', L):
        return 'TOTAL'
    return None


def rate_in(label):
    for m in re.finditer(r'(\d{1,2}(?:[.,]\d{1,2})?)\s*%', str(label)):
        r = float(m.group(1).replace(',', '.'))
        if r in RATES:
            return r
    return None


def candidatos(texto):
    """Lista de {cls, val, rate, label, clave, modo}. modo: linea | columna."""
    lines = [l for l in texto.splitlines() if l.strip()]
    out, prev_segs = [], None
    for l in lines:
        l2 = re.sub(r'\$', ' $ ', l)
        l2 = re.sub(r':(?=\S)', ': ', l2)
        segs = [s.strip() for s in re.split(r'\s{2,}', l2.strip()) if s.strip() and s.strip() != '$']
        vals = [money(s) for s in segs]
        # Fila de valores debajo de una fila de encabezados con la misma cantidad de columnas
        if prev_segs and len(vals) >= 3 and all(v is not None for v in vals) and len(prev_segs) == len(vals) \
                and all(money(s) is None for s in prev_segs):
            for h, v in zip(prev_segs, vals):
                c = clasif(h)
                if c:
                    out.append(dict(cls=c, val=v, rate=rate_in(h), label=h, clave=clave_etiqueta(h), modo='columna'))
        # Pares etiqueta → importe dentro del renglón
        toks = l2.split()
        label, pend_rate, hubo_num = [], None, False
        for t in toks:
            if t in ('$', 'ARS', ':', 'USD'):
                continue
            v = money(t)
            if v is None:
                if re.match(r'^\d{1,2}(?:[.,]\d+)?%$', t) or t == '%':
                    r = rate_in(t if t != '%' else ((label[-1] + '%') if label else ''))
                    if r:
                        pend_rate = r
                    if t == '%' and label and re.match(r'^\d', label[-1]):
                        label.pop()
                    continue
                if hubo_num:
                    label, pend_rate, hubo_num = [], None, False
                label.append(t)
                continue
            lab = ' '.join(label)
            c = clasif(lab)
            if c in ('IVA', 'PERC_IIBB', 'PERC_IVA', 'PERC_GEN') and not hubo_num and pend_rate is None \
                    and (v in RATES or (c != 'IVA' and v < 10)):
                pend_rate = v      # "I.V.A. 21.00 base monto" / "Perc IIBB CABA 0.50 1.118,08"
                continue
            if c:
                rate = pend_rate if c == 'IVA' and pend_rate in RATES else rate_in(lab)
                out.append(dict(cls=c, val=v, rate=rate, label=lab, clave=clave_etiqueta(lab), modo='linea'))
            hubo_num = True
        prev_segs = segs
    return out


def fechas_etiquetadas(texto):
    """Pares etiqueta → fecha (para aprender dónde está el vencimiento de pago)."""
    out, prev = [], ''
    for l in texto.splitlines():
        cerca_cae = bool(re.search(r'C\.?\s?A\.?\s?E\b', l + ' ' + prev, re.I))
        if l.strip():
            prev = l
        for m in re.finditer(r'([A-Za-zÁÉÍÓÚáéíóúñÑ.°º ]{3,60}?)[:\s]+(\d{1,2}\s*[/.\-]\s*\d{1,2}\s*[/.\-]\s*\d{2,4}|20\d{2}-\d{2}-\d{2}|20\d{6})', l):
            f = fecha_iso(m.group(2))
            if f:
                out.append(dict(clave=clave_etiqueta(m.group(1)), fecha=f, cerca_cae=cerca_cae))
    return out


def buscar_vto(texto, clave=None):
    fe = fechas_etiquetadas(texto)
    if clave:
        for x in fe:
            if x['clave'] == clave:
                return x['fecha']
    for x in fe:
        if re.search(r'VTO|VENC', x['clave']) and not re.search(r'C\.?A\.?E', x['clave']) and not x.get('cerca_cae'):
            return x['fecha']
    return None


def buscar_cbu(texto):
    for l in texto.splitlines():
        if re.search(r'CBU', l, re.I):
            m = re.search(r'(?<!\d)(\d{22})(?!\d)', l.replace(' ', ''))
            if m:
                return m.group(1)
    return None


# ---------------------------------------------------------------------------
#  Resolución: qué importes son neto, IVA y percepciones
#  Una solución solo vale si IVA = neto × alícuota y todo suma el total al centavo.
# ---------------------------------------------------------------------------
EXTRA_CLS = ('PERC_IVA', 'PERC_IIBB', 'PERC_GAN', 'PERC_GEN', 'NOGRAV', 'EXENTO', 'OTROS')


def _dedup(lst):
    seen, r = set(), []
    for c in lst:
        k = (c['cls'], c['val'], c['clave'][:30])
        if k not in seen:
            seen.add(k); r.append(c)
    return r


def _tol_iva(n):
    return max(0.05, n * 0.0001)


def _extras_score(S):
    return sum(2 if x['cls'] in ('PERC_IVA', 'PERC_GAN') or (x['cls'] == 'PERC_IIBB' and juris(x['label'])) else
               (1 if x['cls'] in ('NOGRAV', 'EXENTO', 'OTROS') else 0) for x in S)


def _subsets_extras(extras, resto):
    out = []
    for k in range(0, min(5, len(extras)) + 1):
        for S in itertools.combinations(extras, k):
            if len({x['val'] for x in S}) < len(S):
                continue
            if abs(sum(x['val'] for x in S) - resto) <= TOL:
                out.append(S)
    return out


def resolver(cands, total, texto=None, cuadre=False):
    netos = _dedup([c for c in cands if c['cls'] == 'NETO' and c['val'] > 0])
    ivas = _dedup([c for c in cands if c['cls'] == 'IVA' and c['val'] > 0])
    extras = _dedup([c for c in cands if c['cls'] in EXTRA_CLS and c['val'] > 0])
    if cuadre:
        vals = sorted({v for v in (money(t) for t in re.sub(r'\$', ' ', texto).split()) if v and v > 0})
        netos = [dict(cls='NETO', val=v, rate=None, label='', clave='', modo='cuadre') for v in vals]
        ivas = [dict(cls='IVA', val=v, rate=None, label='', clave='', modo='cuadre') for v in vals]
    sols = []
    # A) una alícuota
    for n in netos:
        for iv in ivas:
            rates = [iv['rate']] if iv['rate'] else ([n['rate']] if n.get('rate') else RATES)
            r = next((r for r in rates if r and abs(n['val'] * r / 100 - iv['val']) <= _tol_iva(n['val'])), None)
            if r is None:
                continue
            for S in _subsets_extras(extras, round(total - n['val'] - iv['val'], 2)):
                sols.append(dict(gravado=[dict(alicuota=r, neto=n['val'], iva=iv['val'], c_neto=n, c_iva=iv)],
                                 extras=list(S), score=_extras_score(S) + (1 if iv['rate'] else 0)))
    # B) varias alícuotas (solo con etiquetas, nunca por cuadre)
    if not cuadre:
        con_rate = [iv for iv in ivas if iv['rate']]
        for k in (2, 3):
            for G in itertools.combinations(con_rate, k):
                if len({g['rate'] for g in G}) < k:
                    continue
                # B1: netos por alícuota
                grav, ok = [], True
                for g in G:
                    n = next((n for n in netos if abs(n['val'] * g['rate'] / 100 - g['val']) <= _tol_iva(n['val'])), None)
                    if not n:
                        ok = False; break
                    grav.append(dict(alicuota=g['rate'], neto=n['val'], iva=g['val'], c_neto=n, c_iva=g))
                if not ok:
                    # B2: un neto total que se reparte según cada IVA
                    for n in netos:
                        parciales = [round(g['val'] * 100 / g['rate'], 2) for g in G]
                        if abs(sum(parciales) - n['val']) <= 0.05 * k + n['val'] * 0.0001:
                            parciales[-1] = round(n['val'] - sum(parciales[:-1]), 2)
                            grav = [dict(alicuota=g['rate'], neto=p, iva=g['val'], c_neto=n, c_iva=g, neto_total=True)
                                    for g, p in zip(G, parciales)]
                            ok = True
                            break
                if not ok:
                    continue
                base = sum(g['neto'] + g['iva'] for g in grav)
                for S in _subsets_extras(extras, round(total - base, 2)):
                    sols.append(dict(gravado=grav, extras=list(S), score=_extras_score(S) + k))
    if not sols:
        return []
    uniq = {}
    for s in sols:
        key = json.dumps([[(g['alicuota'], g['neto'], g['iva']) for g in s['gravado']],
                          sorted((x['cls'], x['val'], juris(x['label'])) for x in s['extras'])])
        uniq.setdefault(key, s)
    best = max(s['score'] for s in uniq.values())
    return [s for s in uniq.values() if s['score'] == best]


def _extra_a_datos(x, d):
    if x['cls'] in ('NOGRAV',):
        d['importes']['no_gravado'] = round(d['importes']['no_gravado'] + x['val'], 2)
    elif x['cls'] == 'EXENTO':
        d['importes']['exento'] = round(d['importes']['exento'] + x['val'], 2)
    elif x['cls'] == 'OTROS':
        d['importes']['otros_tributos'] = round(d['importes']['otros_tributos'] + x['val'], 2)
    else:
        tipo = {'PERC_IVA': 'IVA', 'PERC_IIBB': 'IIBB', 'PERC_GAN': 'GANANCIAS'}.get(x['cls'], 'OTRO')
        d['percepciones'].append(dict(tipo=tipo, jurisdiccion=juris(x['label']) if tipo == 'IIBB' else None,
                                      importe=x['val'], descripcion=x['label'][:80]))


def solucion_a_datos(sol, d):
    d['importes']['gravado'] = [dict(alicuota=g['alicuota'], neto=g['neto'], iva=g['iva']) for g in sol['gravado']]
    for x in sol['extras']:
        _extra_a_datos(x, d)
    return d


# ---------------------------------------------------------------------------
#  Configuración (plantilla) del proveedor: aplicar
#  La plantilla la arma el Worker cuando una persona confirma la primera factura.
# ---------------------------------------------------------------------------
def _buscar(cands, clave, clases):
    if not clave:
        return []
    exact = [c for c in cands if c['clave'] == clave and c['cls'] in clases]
    if not exact:
        exact = [c for c in cands if c['cls'] in clases and len(clave) >= 4 and (clave in c['clave'] or (len(c['clave']) >= 4 and c['clave'] in clave))]
    vals = []
    for c in exact:
        if c['val'] not in vals:
            vals.append(c['val'])
    return vals


def aplicar_plantilla(pl, cands, texto, d):
    """Devuelve (datos, problemas). problemas vacío = la factura respeta la configuración."""
    total = d['importes']['total']
    problemas = []
    letra = d['comprobante'].get('letra')
    if pl.get('sin_iva') or letra in ('B', 'C'):
        extras = []
        for e in pl.get('extras', []):
            v = _buscar(cands, e.get('clave'), EXTRA_CLS)
            if v:
                extras.append(dict(cls=e['cls'], val=v[0], label=e.get('etiqueta') or e.get('clave') or '', clave=e.get('clave')))
        for x in extras:
            _extra_a_datos(x, d)
        d['importes']['sin_discriminar'] = round(total - sum(x['val'] for x in extras), 2)
        return d, problemas

    grav = []
    if pl.get('modo') == 'cuadre':
        sols = resolver(cands, total, texto, cuadre=True)
        if len(sols) != 1:
            return d, ['La configuración del proveedor lee los importes por cuadre aritmético y esta vez no hubo una única solución.']
        return solucion_a_datos(sols[0], d), []

    netos_total = _buscar(cands, pl.get('neto_total'), ('NETO',)) if pl.get('neto_total') else None
    for g in pl.get('gravado', []):
        iv = _buscar(cands, g.get('clave_iva'), ('IVA',))
        if not iv:
            problemas.append(f"No encontré el IVA {g['alicuota']}% (“{g.get('etiqueta_iva') or g.get('clave_iva')}”).")
            continue
        if g.get('clave_neto'):
            nv = _buscar(cands, g['clave_neto'], ('NETO',))
            if not nv:
                problemas.append(f"No encontré el neto {g['alicuota']}% (“{g.get('etiqueta_neto') or g['clave_neto']}”).")
                continue
            # Elegimos el par (neto, IVA) que cumple neto × alícuota (hay renglones con base y monto juntos)
            par = next(((n, i) for n in nv for i in iv if abs(n * g['alicuota'] / 100 - i) <= _tol_iva(n)), None)
            neto, iva = par if par else (nv[-1], next((v for v in iv if v > 0), iv[0]))
        else:
            neto, iva = None, iv
        grav.append(dict(alicuota=g['alicuota'], neto=neto, iva=iva))
    if netos_total is not None:
        if not netos_total:
            problemas.append(f"No encontré el neto gravado (“{pl.get('etiqueta_neto_total') or pl.get('neto_total')}”).")
        else:
            # Cada IVA puede tener varios candidatos: buscamos la combinación que reparte exacto el neto total
            listas = [g['iva'] if isinstance(g['iva'], list) else [g['iva']] for g in grav]
            elegido = None
            for N in netos_total:
                for combo in itertools.product(*listas):
                    act = [(g, i) for g, i in zip(grav, combo) if i > 0]
                    if abs(sum(i * 100 / g['alicuota'] for g, i in act) - N) <= 0.05 * max(1, len(act)) + N * 0.0001:
                        elegido = (N, combo); break
                if elegido:
                    break
            N, combo = elegido if elegido else (netos_total[-1], [l[0] for l in listas])
            for g, i in zip(grav, combo):
                g['iva'] = i
            activos = [g for g in grav if g['iva'] > 0]
            parciales = [round(g['iva'] * 100 / g['alicuota'], 2) for g in activos]
            if activos:
                parciales[-1] = round(N - sum(parciales[:-1]), 2)
                for g, p in zip(activos, parciales):
                    g['neto'] = p
            for g in grav:
                if g['neto'] is None:
                    g['neto'] = 0.0
    for g in grav:
        if isinstance(g['iva'], list):
            g['iva'] = next((v for v in g['iva'] if v > 0), g['iva'][0])
        if g['neto'] is None:
            g['neto'] = 0.0
    grav = [g for g in grav if (g['neto'] or 0) > 0 or g['iva'] > 0]
    if problemas:
        return d, problemas
    for g in grav:
        if abs(g['neto'] * g['alicuota'] / 100 - g['iva']) > _tol_iva(g['neto']):
            problemas.append(f"El IVA {g['alicuota']}% ({g['iva']:.2f}) no corresponde al neto {g['neto']:.2f}.")
    extras, claves_usadas = [], set()
    for e in pl.get('extras', []):
        v = _buscar(cands, e.get('clave'), EXTRA_CLS)
        if v:
            extras.append(dict(cls=e['cls'], val=v[0], label=e.get('etiqueta') or e.get('clave'), clave=e.get('clave'),
                               jurisdiccion=e.get('jurisdiccion')))
            claves_usadas.add(e.get('clave'))
    suma = round(sum(g['neto'] + g['iva'] for g in grav) + sum(x['val'] for x in extras), 2)
    if abs(suma - total) > TOL:
        # ¿Apareció un concepto nuevo (percepción, no gravado) que no estaba en la configuración?
        nuevos = _dedup([c for c in cands if c['cls'] in EXTRA_CLS and c['val'] > 0 and c['clave'] not in claves_usadas])
        arreglo = next((S for S in _subsets_extras(nuevos, round(total - suma, 2)) if S), None)
        if arreglo:
            extras += list(arreglo)
            problemas.append('Apareció un concepto nuevo que no estaba en la configuración: '
                             + ', '.join(f"“{x['label']}” {x['val']:.2f}" for x in arreglo) + '.')
        else:
            problemas.append(f'Con la configuración del proveedor los importes suman {suma:.2f} y el total del QR es {total:.2f}.')
    d['importes']['gravado'] = [dict(alicuota=g['alicuota'], neto=round(g['neto'], 2), iva=g['iva']) for g in grav]
    for x in extras:
        if x.get('jurisdiccion') and x['cls'] == 'PERC_IIBB':
            d['percepciones'].append(dict(tipo='IIBB', jurisdiccion=x['jurisdiccion'], importe=x['val'], descripcion=(x['label'] or '')[:80]))
        else:
            _extra_a_datos(x, d)
    return d, problemas


# ---------------------------------------------------------------------------
#  Gemini (solo proveedores nuevos o cuando se fuerza)
# ---------------------------------------------------------------------------
def _S(desc): return {'type': 'STRING', 'nullable': True, 'description': desc}
def _N(desc): return {'type': 'NUMBER', 'nullable': True, 'description': desc}


ESQUEMA_GEMINI = {
    'type': 'OBJECT',
    'properties': {
        'es_comprobante_fiscal': {'type': 'BOOLEAN', 'description': 'true si es factura, nota de crédito o débito argentina'},
        'emisor_cuit': _S('CUIT del emisor, 11 dígitos'), 'emisor_razon_social': _S('Razón social del emisor'),
        'emisor_condicion_iva': _S('Condición IVA del emisor'),
        'receptor_cuit': _S('CUIT del receptor'),
        'tipo_comprobante_arca': {'type': 'INTEGER', 'nullable': True, 'description': 'Código ARCA: 1 FA, 2 NDA, 3 NCA, 6 FB, 11 FC, 51 FM, 201 FCE A...'},
        'punto_venta': {'type': 'INTEGER', 'nullable': True}, 'numero': {'type': 'INTEGER', 'nullable': True},
        'fecha_emision': _S('YYYY-MM-DD'), 'fecha_vencimiento_pago': _S('YYYY-MM-DD (no el vencimiento del CAE)'),
        'cae': _S('CAE de 14 dígitos'),
        'neto_gravado': {'type': 'ARRAY', 'description': 'Una entrada por alícuota de IVA discriminada',
                         'items': {'type': 'OBJECT', 'properties': {'alicuota': {'type': 'NUMBER'}, 'neto': {'type': 'NUMBER'}, 'iva': {'type': 'NUMBER'}},
                                   'required': ['alicuota', 'neto', 'iva']}},
        'importe_sin_discriminar': _N('Comprobantes B/C: subtotal sin IVA discriminado'),
        'no_gravado': _N('Importe no gravado'), 'exento': _N('Importe exento'),
        'otros_tributos': _N('Otros tributos que no son percepciones (impuestos internos, tasas)'),
        'percepciones': {'type': 'ARRAY', 'items': {'type': 'OBJECT', 'properties': {
            'tipo': {'type': 'STRING', 'enum': ['IVA', 'IIBB', 'GANANCIAS', 'MUNICIPAL', 'OTRO']},
            'jurisdiccion': _S('Provincia para IIBB'), 'importe': {'type': 'NUMBER'}, 'descripcion': _S('Texto tal como figura')},
            'required': ['tipo', 'importe']}},
        'total': _N('Importe total'), 'cbu': _S('CBU de 22 dígitos si figura'),
        'local_detectado': _S('Local / sucursal / dirección de entrega del receptor si figura'),
        'detalle_resumen': _S('Qué se factura, en una línea'),
        'cuenta_sugerida': {'type': 'INTEGER', 'nullable': True, 'description': 'codigo_concepto sugerido del plan de cuentas provisto'},
        'motivo_cuenta': _S('Por qué esa cuenta'),
        'observaciones': _S('Cualquier cosa rara del comprobante'),
    },
    'required': ['es_comprobante_fiscal', 'neto_gravado', 'percepciones'],
}


def gemini_leer(pdf_bytes, cuentas):
    key = os.environ.get('GEMINI_API_KEY')
    if not key:
        raise RuntimeError('Falta GEMINI_API_KEY para leer un proveedor nuevo.')
    model = os.environ.get('GEMINI_MODEL') or 'gemini-2.5-pro'
    listado = '\n'.join(f"{c['codigo_concepto']} — {c['denominacion']}" for c in cuentas[:400])
    prompt = ('Sos un analista contable argentino. Extraé los datos de este comprobante de proveedor recibido por Lucciano\'s. '
              'Importes como número con punto decimal. No inventes: si algo no figura, null. Leé una sola copia si hay original/duplicado. '
              'Neto + IVA + no gravado + exento + otros tributos + percepciones debe dar el total.'
              + (f'\n\nPlan de cuentas para sugerir imputación:\n{listado}' if listado else ''))
    body = {'contents': [{'role': 'user', 'parts': [{'inline_data': {'mime_type': 'application/pdf', 'data': base64.b64encode(pdf_bytes).decode()}}, {'text': prompt}]}],
            'generationConfig': {'responseMimeType': 'application/json', 'responseSchema': ESQUEMA_GEMINI, 'temperature': 0}}
    base = os.environ.get('GEMINI_BASE', 'https://generativelanguage.googleapis.com')
    req = urllib.request.Request(f'{base}/v1beta/models/{model}:generateContent?key={key}', data=json.dumps(body).encode(),
                                 headers={'Content-Type': 'application/json'}, method='POST')
    try:
        with urllib.request.urlopen(req, timeout=180) as r:
            data = json.loads(r.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        raise RuntimeError(f'Gemini HTTP {e.code}: {e.read().decode("utf-8", "replace")[:300]}')
    txt = ''.join(p.get('text', '') for p in data.get('candidates', [{}])[0].get('content', {}).get('parts', []))
    return json.loads(txt), model


def gemini_a_datos(g, d):
    num = lambda v: round(float(v or 0), 2)
    d['importes']['gravado'] = [dict(alicuota=float(x['alicuota']), neto=num(x['neto']), iva=num(x['iva']))
                                for x in g.get('neto_gravado') or [] if num(x.get('neto')) or num(x.get('iva'))]
    d['importes']['sin_discriminar'] = num(g.get('importe_sin_discriminar'))
    d['importes']['no_gravado'] = num(g.get('no_gravado'))
    d['importes']['exento'] = num(g.get('exento'))
    d['importes']['otros_tributos'] = num(g.get('otros_tributos'))
    for p in g.get('percepciones') or []:
        if num(p.get('importe')):
            tipo = str(p.get('tipo') or 'OTRO').upper()
            d['percepciones'].append(dict(tipo=tipo, jurisdiccion=juris(p.get('jurisdiccion') or p.get('descripcion') or '') if tipo == 'IIBB' else None,
                                          importe=num(p['importe']), descripcion=p.get('descripcion')))
    d['es_comprobante_fiscal'] = g.get('es_comprobante_fiscal', True) is not False
    d['emisor']['razon_social'] = d['emisor'].get('razon_social') or g.get('emisor_razon_social')
    d['emisor']['condicion_iva'] = g.get('emisor_condicion_iva')
    d['comprobante']['fecha_vto_pago'] = d['comprobante'].get('fecha_vto_pago') or fecha_iso(g.get('fecha_vencimiento_pago'))
    d['pago']['cbu'] = d['pago'].get('cbu') or (re.sub(r'\D', '', g.get('cbu') or '') or None)
    d['local_detectado'] = g.get('local_detectado')
    d['detalle_resumen'] = g.get('detalle_resumen')
    d['ia'] = dict(cuenta_sugerida=g.get('cuenta_sugerida'), motivo_cuenta=g.get('motivo_cuenta'), observaciones=g.get('observaciones'))
    # Si no hubo QR, el encabezado sale de Gemini (y se marcará para revisar)
    c = d['comprobante']
    if not d['emisor'].get('cuit'):
        d['emisor']['cuit'] = re.sub(r'\D', '', g.get('emisor_cuit') or '') or None
    if not d['receptor'].get('cuit'):
        d['receptor']['cuit'] = re.sub(r'\D', '', g.get('receptor_cuit') or '') or None
    c['tipo_arca'] = c.get('tipo_arca') or g.get('tipo_comprobante_arca')
    c['pto_vta'] = c.get('pto_vta') or g.get('punto_venta')
    c['numero'] = c.get('numero') or g.get('numero')
    c['fecha_emision'] = c.get('fecha_emision') or fecha_iso(g.get('fecha_emision'))
    c['cae'] = c.get('cae') or (re.sub(r'\D', '', g.get('cae') or '') or None)
    if not d['importes']['total']:
        d['importes']['total'] = num(g.get('total'))
    return d


def suma_componentes(d):
    im = d['importes']
    s = sum(g['neto'] + g['iva'] for g in im['gravado']) + im['sin_discriminar'] + im['no_gravado'] + im['exento'] + im['otros_tributos']
    return round(s + sum(p['importe'] for p in d['percepciones']), 2)


# ---------------------------------------------------------------------------
#  Encabezado sin QR (respaldo por texto)
# ---------------------------------------------------------------------------
LETRA = {1: 'A', 2: 'A', 3: 'A', 6: 'B', 7: 'B', 8: 'B', 11: 'C', 12: 'C', 13: 'C', 51: 'M', 52: 'M', 53: 'M',
         201: 'A', 202: 'A', 203: 'A', 206: 'B', 207: 'B', 208: 'B', 211: 'C', 212: 'C', 213: 'C'}


def encabezado_texto(texto, empresas):
    h = {}
    cuits = []
    for m in re.finditer(r'(?<!\d)(\d{2})[\s\-.]?(\d{8})[\s\-.]?(\d)(?!\d)', texto):
        c = ''.join(m.groups())
        if cuit_valido(c) and c not in cuits:
            cuits.append(c)
    h['cuit_emisor'] = next((c for c in cuits if c not in empresas), None)
    h['doc_receptor'] = next((c for c in cuits if c in empresas), None)
    m = re.search(r'C\.?\s?A\.?\s?E\.?\s*(?:N[°º.o]*)?\s*:?\s*(\d{14})', texto, re.I)
    h['cae'] = m.group(1) if m else None
    m = re.search(r'(?<!\d)(\d{4,5})\s*-\s*(\d{8})(?!\d)', texto)
    if m:
        h['pto_vta'], h['numero'] = int(m.group(1)), int(m.group(2))
    m = re.search(r'C[OÓ]D(?:IGO)?\.?\s*N?[°º]?\s*:?\s*0*(\d{1,3})\b', texto, re.I)
    h['tipo'] = int(m.group(1)) if m and int(m.group(1)) in LETRA else None
    m = re.search(r'Fecha(?:\s+de)?(?:\s+Emisi[oó]n)?\s*:?\s*(\d{1,2}\s*[/.\-]\s*\d{1,2}\s*[/.\-]\s*\d{2,4})', texto, re.I)
    h['fecha'] = fecha_iso(m.group(1)) if m else None
    tot = [c['val'] for c in candidatos(texto) if c['cls'] == 'TOTAL']
    h['total'] = max(tot) if tot else None
    return h


# ---------------------------------------------------------------------------
#  Proceso de una factura
# ---------------------------------------------------------------------------
def datos_base(qr, h):
    src = qr or h
    tipo = src.get('tipo')
    return {
        'es_comprobante_fiscal': True,
        'emisor': {'cuit': src.get('cuit_emisor'), 'razon_social': None, 'condicion_iva': None},
        'receptor': {'cuit': src.get('doc_receptor') or None, 'razon_social': None},
        'comprobante': {'tipo_arca': tipo, 'letra': LETRA.get(tipo), 'pto_vta': src.get('pto_vta'), 'numero': src.get('numero'),
                        'fecha_emision': src.get('fecha'), 'fecha_vto_pago': None, 'moneda': (qr or {}).get('moneda', 'PES'),
                        'cotizacion': (qr or {}).get('cotizacion'), 'tipo_autorizacion': (qr or {}).get('tipo_autorizacion', 'CAE'),
                        'cae': src.get('cae'), 'cae_vto': None, 'orden_compra': None},
        'importes': {'gravado': [], 'sin_discriminar': 0.0, 'no_gravado': 0.0, 'exento': 0.0, 'otros_tributos': 0.0,
                     'total': round(float(src.get('total') or 0), 2)},
        'percepciones': [], 'pago': {'cbu': None, 'alias': None},
        'local_detectado': None, 'detalle_resumen': None, 'ia': {}, 'imputacion': {}, 'overrides': {}, 'items_manual': None,
    }


def procesar(f, ctx):
    pdf = _req('GET', f"/api/lector/pdf/{f['id']}", raw=True, timeout=120)
    doc = pymupdf.open(stream=pdf, filetype='pdf')
    texto = texto_pdf(doc)
    empresas = set(ctx.get('empresas') or [])
    qr, qr_via = leer_qr(doc)
    h = encabezado_texto(texto, empresas) if not qr else {}
    d = datos_base(qr, h)
    cands = candidatos(texto)
    cuit = d['emisor']['cuit']
    pl = (ctx.get('plantillas') or {}).get(cuit) if cuit else None
    problemas, metodo, modelo = [], None, None
    sin_texto = len(texto.strip()) < 40

    faltan = [k for k, v in (('CUIT emisor', cuit), ('tipo', d['comprobante']['tipo_arca']), ('número', d['comprobante']['numero']),
                             ('total', d['importes']['total'])) if not v]
    if pl and not f.get('forzar_ia') and not sin_texto:
        metodo = 'plantilla' if pl['estado'] == 'activa' else 'plantilla_pendiente'
        d, problemas = aplicar_plantilla(pl['config'], cands, texto, d)
        if problemas and abs(suma_componentes(d) - d['importes']['total']) > TOL and not faltan:
            # El formato cambió: precompletamos con las reglas generales para que la persona solo revise
            sols = resolver(cands, d['importes']['total'])
            if len(sols) != 1:
                sols = resolver(cands, d['importes']['total'], texto, cuadre=True)
            if len(sols) == 1:
                d = solucion_a_datos(sols[0], datos_base(qr, h))
                problemas.append('Los importes se precompletaron con las reglas generales (cuadran con el QR): revisalos y confirmá.')
        d['comprobante']['fecha_vto_pago'] = buscar_vto(texto, pl['config'].get('vto_clave'))
        d['emisor']['razon_social'] = pl.get('razon_social')
    else:
        sols = []
        if not f.get('forzar_ia') and not sin_texto and not faltan:
            if d['comprobante']['letra'] in ('B', 'C'):
                d['importes']['sin_discriminar'] = d['importes']['total']
                sols = [None]
            else:
                sols = resolver(cands, d['importes']['total'])
                if len(sols) != 1:
                    s2 = resolver(cands, d['importes']['total'], texto, cuadre=True)
                    if len(s2) == 1:
                        sols = s2
        if len(sols) == 1:
            metodo = 'reglas'
            if sols[0]:
                d = solucion_a_datos(sols[0], d)
            d['comprobante']['fecha_vto_pago'] = buscar_vto(texto)
        else:
            metodo = 'ia'
            g, modelo = gemini_leer(pdf, ctx.get('cuentas') or [])
            d = gemini_a_datos(g, d)
            if abs(suma_componentes(d) - d['importes']['total']) > TOL:
                problemas.append(f"La lectura de Gemini no cuadra: componentes {suma_componentes(d):.2f} vs total {d['importes']['total']:.2f}.")
            if not qr:
                problemas.append('Sin QR legible: el encabezado (CUIT, número, CAE) lo leyó Gemini. Verificalo contra el PDF.')
    if not d['pago']['cbu']:
        d['pago']['cbu'] = buscar_cbu(texto)
    if faltan and metodo != 'ia':
        problemas.append('No pude leer del PDF: ' + ', '.join(faltan) + '.')
    if sin_texto and metodo != 'ia':
        problemas.append('El PDF no tiene texto (¿escaneado?).')
    d['lectura'] = {'metodo': metodo, 'qr': qr_via, 'modelo': modelo, 'plantilla_id': pl['id'] if pl else None,
                    'plantilla_version': pl.get('version') if pl else None, 'lector_version': VERSION}
    return {
        'datos': d, 'qr': qr, 'metodo': metodo, 'problemas': problemas,
        'candidatos': [{k: c[k] for k in ('cls', 'val', 'rate', 'label', 'clave', 'modo')} for c in _dedup(cands)][:400],
        'fechas': fechas_etiquetadas(texto)[:80],
        'texto': texto[:20000],
    }


def main():
    ctx = _req('GET', '/api/lector/trabajo')
    facturas = ctx.get('facturas') or []
    print(f'Lector {VERSION}: {len(facturas)} factura(s) para leer')
    for f in facturas:
        try:
            res = procesar(f, ctx)
            r = _req('POST', f"/api/lector/resultado/{f['id']}", res)
            print(f"  #{f['id']} {f.get('archivo_nombre') or ''}: {res['metodo']} → {r.get('estado')}"
                  + (f" ({'; '.join(res['problemas'])})" if res['problemas'] else ''))
        except Exception as e:
            traceback.print_exc()
            try:
                _req('POST', f"/api/lector/resultado/{f['id']}", {'error': f'{type(e).__name__}: {e}'[:800]})
            except Exception as e2:
                print(f'  #{f["id"]}: no pude informar el error al Worker: {e2}', file=sys.stderr)
            print(f"  #{f['id']}: ERROR {e}")


if __name__ == '__main__':
    main()
