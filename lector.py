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
   GEMINI_MODEL     opcional; si no está, se elige solo el mejor Flash disponible
=============================================================================
"""
from __future__ import annotations

import base64
import io
import itertools
import json
import time
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

VERSION = '1.0.13'
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


def _dig(v):
    """Dígitos de un campo del QR. Algunos sistemas mandan números como float (3.0713263008e10):
    str() daría '30713263008.0' y quedaría un 0 de más."""
    if isinstance(v, bool) or v is None:
        return ''
    if isinstance(v, float):
        return str(int(round(v)))
    if isinstance(v, int):
        return str(v)
    t = str(v).strip()
    if re.match(r'^\d+\.0+$', t):
        t = t.split('.')[0]
    elif re.match(r'^\d+(\.\d+)?[eE]\+?\d+$', t):
        t = str(int(round(float(t))))
    return re.sub(r'\D', '', t)


def _decodificar_qr(texto):
    # Algunos emisores parten el base64 en renglones: se quitan los espacios/saltos antes de buscar
    m = re.search(r'[?&]p=([^&]+)', re.sub(r'\s+', '', texto or ''))
    if not m:
        return None
    b = urllib.parse.unquote(m.group(1)).replace('-', '+').replace('_', '/')
    b += '=' * (-len(b) % 4)
    try:
        raw = base64.b64decode(b).decode('utf-8', 'replace')
    except Exception:
        return None
    try:
        q = json.loads(raw)
    except Exception:
        # JSON mal armado por el emisor, p. ej. "importe":19545715,27 (coma decimal)
        fix = re.sub(r'("(?:importe|ctz)"\s*:\s*-?\d+),(\d+)', r'\1.\2', raw, flags=re.I)
        try:
            q = json.loads(fix)
        except Exception:
            return None
    if not isinstance(q, dict):
        return None
    # Claves sin importar mayúsculas ("Cuit", "PtoVta"...) y alias usados por algunos sistemas
    q = {k.lower(): v for k, v in q.items()}
    if q.get('nrocmp') is None and q.get('nrocomp') is not None:
        q['nrocmp'] = q['nrocomp']
    q = {'fecha': q.get('fecha'), 'cuit': q.get('cuit'), 'ptoVta': q.get('ptovta'), 'tipoCmp': q.get('tipocmp'),
         'nroCmp': q.get('nrocmp'), 'importe': q.get('importe'), 'moneda': q.get('moneda'), 'ctz': q.get('ctz'),
         'nroDocRec': q.get('nrodocrec'), 'tipoCodAut': q.get('tipocodaut'), 'codAut': q.get('codaut')}
    if not _dig(q.get('cuit')):
        return None
    return {
        'fecha': fecha_iso(q.get('fecha')),
        'cuit_emisor': _dig(q.get('cuit')),
        'pto_vta': int(q['ptoVta']) if q.get('ptoVta') is not None else None,
        'tipo': int(q['tipoCmp']) if q.get('tipoCmp') is not None else None,
        'numero': int(q['nroCmp']) if q.get('nroCmp') is not None else None,
        'total': round(float(q.get('importe', 0)), 2),
        'moneda': q.get('moneda') or 'PES',
        'cotizacion': float(q.get('ctz') or 1),
        'doc_receptor': _dig(q.get('nroDocRec')),
        'tipo_autorizacion': 'CAEA' if q.get('tipoCodAut') == 'A' else 'CAE',
        'cae': _dig(q.get('codAut')),
    }


def _qr_por_redireccion(urls):
    """Algunos sistemas (p. ej. Koobiko / quieromifactura) ponen en el QR un link propio que redirige al de ARCA."""
    for u in urls[:2]:
        try:
            req = urllib.request.Request(u, headers={'User-Agent': 'Mozilla/5.0 (lector facturas)'})
            with urllib.request.urlopen(req, timeout=8) as r:
                q = _decodificar_qr(r.geturl())
                if q:
                    return q
                q = _decodificar_qr(r.read(300000).decode('utf-8', 'replace').replace('&amp;', '&'))
                if q:
                    return q
        except Exception:
            continue
    return None


def _decodificar_barras(t):
    """Código de barras ARCA (RG 1702, Interleaved 2 of 5): CUIT(11) + tipo(2/3) + PV(4/5) + CAE(14) + vto(8) + DV(1)."""
    t = re.sub(r'\D', '', t or '')
    if len(t) not in (40, 41, 42):
        return None
    b = t[:-1]
    if (10 - (sum(int(x) for x in b[0::2]) * 3 + sum(int(x) for x in b[1::2])) % 10) % 10 != int(t[-1]):
        return None
    for lt, lp in ((2, 4), (3, 4), (2, 5), (3, 5)):
        if 11 + lt + lp + 14 + 8 + 1 != len(t):
            continue
        cuit, tipo = t[:11], int(t[11:11 + lt])
        pv = int(t[11 + lt:11 + lt + lp]); cae = t[11 + lt + lp:25 + lt + lp]; vto = t[25 + lt + lp:33 + lt + lp]
        if cuit_valido(cuit) and tipo in LETRA and re.match(r'20\d{6}$', vto):
            return {'cuit_emisor': cuit, 'tipo': tipo, 'pto_vta': pv, 'cae': cae, 'cae_vto': fecha_iso(vto)}
    return None


def leer_barras(doc):
    """Respaldo cuando no hay QR: el código de barras de ARCA (sobre todo en PDFs que son una imagen)."""
    for page in list(doc)[:2]:
        fuentes = []
        for im in page.get_images(full=True):
            try:
                pix = pymupdf.Pixmap(doc, im[0])
                if pix.n - pix.alpha >= 4:
                    pix = pymupdf.Pixmap(pymupdf.csRGB, pix)
                fuentes.append(Image.open(io.BytesIO(pix.tobytes('png'))))
            except Exception:
                continue
        try:
            fuentes.append(Image.open(io.BytesIO(page.get_pixmap(matrix=pymupdf.Matrix(2, 2)).tobytes('png'))))
        except Exception:
            pass
        for img in fuentes:
            for esc in (1, 2, 3):
                try:
                    i2 = img if esc == 1 else img.resize((img.width * esc, img.height * esc))
                    for r in zxingcpp.read_barcodes(i2):
                        b = _decodificar_barras(r.text)
                        if b:
                            return b
                except Exception:
                    continue
    return None


def leer_qr(doc):
    q, via, externos = _leer_qr(doc)
    if q:
        return q, via
    q = _qr_por_redireccion(externos)
    return (q, 'link_emisor') if q else (None, None)


def _leer_qr(doc):
    externos = []
    def _ext(t):
        t = (t or '').strip()
        if re.match(r'^https?://', t, re.I) and 'tcpdf.org' not in t.lower() and t not in externos:
            externos.append(t)
    # 1) links embebidos
    for page in doc:
        for l in page.get_links():
            q = _decodificar_qr(l.get('uri', ''))
            if q:
                return q, 'link', externos
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
                        return q, 'imagen', externos
                    _ext(r.text)
            except Exception:
                continue
    # 3) página renderizada (QR dibujado con vectores)
    for page in list(doc)[:2]:
        for zoom in (2, 3):
            img = Image.open(io.BytesIO(page.get_pixmap(matrix=pymupdf.Matrix(zoom, zoom)).tobytes('png')))
            for r in zxingcpp.read_barcodes(img):
                q = _decodificar_qr(r.text)
                if q:
                    return q, 'render', externos
                _ext(r.text)
    return None, None, externos


def corregir_tipo_qr(qr, texto):
    """Algunos sistemas (Nestlé) ponen en el QR tipo 81 (Tique Factura A) en una Factura A con CAE.
    Los tiques de controlador fiscal no tienen CAE: si hay CAE y el PDF dice "Cód. 01", vale lo impreso."""
    if not qr or qr.get('tipo') not in (81, 82, 83) or not qr.get('cae'):
        return None
    for m in re.finditer(r'C[OÓ]D(?:IGO)?\.?\s*N?[°º]?\s*:?\s*0*(\d{1,3})\b', texto, re.I):
        t = int(m.group(1))
        if t in LETRA and t not in (81, 82, 83):
            ant = qr['tipo']
            qr['tipo'] = t
            return f'El QR del emisor dice tipo {ant} (tique) pero el comprobante tiene CAE e impreso “Cód. {t:02d}”: se tomó tipo {t}.'
    return None


def corregir_escala_qr(qr, texto):
    """Algunos emisores arman el QR con el importe sin la coma decimal (ej. 680008366 en vez de 6800083.66).
    Si el total del QR no aparece en el PDF pero sí aparece dividido por 100 o por 1000, se corrige."""
    if not qr or not qr.get('total'):
        return None
    montos = set()
    for tok in re.split(r'[\s$]+', texto or ''):
        v = money(tok.strip(':;'))
        if v:
            montos.add(round(v, 2))
    if round(qr['total'], 2) in montos:
        return None
    for f in (100, 1000):
        cand = round(qr['total'] / f, 2)
        if cand in montos:
            orig = qr['total']
            qr['total'] = cand
            ar = lambda v: f'{v:,.2f}'.replace(',', 'X').replace('.', ',').replace('X', '.')
            return (f'El QR del emisor trae el importe mal armado ({orig:.0f}, sin la coma decimal): '
                    f'se tomó $ {ar(cand)}, que es el total impreso en la factura. Verificalo.')
    return None


def corregir_escala_total(d):
    """Si el total es exactamente 100 o 1000 veces la suma de los componentes, el error está en la coma del total."""
    s, t = suma_componentes(d), d['importes']['total']
    if not s or not t or abs(s - t) <= TOL:
        return None
    for f in (100, 1000):
        if abs(t / f - s) <= TOL:
            d['importes']['total'] = s
            return f'El total leído ({t:.2f}) era {f} veces la suma de los componentes: se corrigió a {s:.2f}. Verificalo contra el PDF.'
    return None


# ---------------------------------------------------------------------------
#  Pares etiqueta → importe
# ---------------------------------------------------------------------------
# Jurisdicciones: nombre, siglas y código de Convenio Multilateral (901 CABA … 924 Tucumán, p. ej. "913-MZA", "915-NEU")
JURIS = [('CABA', r'CABA|CAPITAL FEDERAL|CAP\.? ?FED|AGIP|C\.A\.B\.A|CIUDAD AUTONOMA|\b901\b'),
         ('BUENOS AIRES', r'ARBA|BUENOS AIRES|\bPBA\b|BS\.? ?AS|PCIA\.? ?BS|\b902\b'),
         ('CATAMARCA', r'CATAMARCA|\bCAT\b|\b903\b'),
         ('CORDOBA', r'CORDOBA|\bCBA\b|\bCOR\b|PERCCBA|\b904\b'), ('CORRIENTES', r'CORRIENTES|\bCTES\b|\b905\b'),
         ('CHACO', r'CHACO|\bCHA\b|\b906\b'), ('CHUBUT', r'CHUBUT|\bCHU\b|\b907\b'),
         ('ENTRE RIOS', r'ENTRE RIOS|\bE\.? ?RIOS\b|\bER\b|\b908\b'), ('FORMOSA', r'FORMOSA|\bFSA\b|\b909\b'),
         ('JUJUY', r'JUJUY|\bJUJ\b|\b910\b'), ('LA PAMPA', r'LA PAMPA|\bLPA\b|\b911\b'), ('LA RIOJA', r'LA RIOJA|\bLRJ\b|\b912\b'),
         ('MENDOZA', r'MENDOZA|\bMZA\b|\bMEN\b|\b913\b'), ('MISIONES', r'MISIONES|\bMIS\b|\b914\b'),
         ('NEUQUEN', r'NEUQUEN|\bNEU\b|\bNQN\b|\b915\b'), ('RIO NEGRO', r'RIO NEGRO|\bRNE?\b|\b916\b'),
         ('SALTA', r'SALTA|\bSAL\b|\b917\b'), ('SAN JUAN', r'SAN JUAN|\bSJU?\b|\b918\b'), ('SAN LUIS', r'SAN LUIS|\bSLU?\b|\b919\b'),
         ('SANTA CRUZ', r'SANTA CRUZ|\bSCR?\b|\b920\b'), ('SANTA FE', r'SANTA FE|\bSFE?\b|\b921\b'),
         ('SANTIAGO DEL ESTERO', r'SANTIAGO DEL ESTERO|S\.? ?DEL ESTERO|\bSDE\b|\bSGO\b|\b922\b'),
         ('TIERRA DEL FUEGO', r'TIERRA DEL FUEGO|\bTDF\b|\b923\b'), ('TUCUMAN', r'TUCUMAN|TUC\b|\b924\b')]


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
    if re.search(r'PERC|IIBB|INGRESOS BRUTOS|AGIP|ARBA|\bIB\b|\bII\.?BB|\bPIB\b', L):
        return 'PERC_IIBB' if (re.search(r'IIBB|INGRESOS BRUTOS|AGIP|ARBA|\bIB\b|II\.?BB|\bPIB\b', L) or juris(label)) else 'PERC_GEN'
    if re.search(r'EXENTO', L) and not re.search(r'NO GRAVADO', L):
        return 'EXENTO'
    if re.search(r'NO GRAVADO|EXENTO', L):
        return 'NOGRAV'
    if re.search(r'OTROS TRIBUTOS|IMP\.? INT|IMPUESTOS? INTERNOS', L):
        return 'OTROS'
    if re.search(r'^LEY\b|\bLEY (PROV|\d)', L):   # tributos de servicios públicos: "LEY 11769 ART 75", "LEY PROV. 7290"
        return 'OTROS'
    if re.search(r'\bI\.?V\.?A\.?\b|IVA INSC', L):
        return 'IVA'
    if re.search(r'NETO|SUBTOTAL|SUB TOTAL|GRAVADO|BASE (IMPONIBLE|GRAV)', L):
        return 'NETO'
    if re.search(r'\bTOTAL\b', L):
        if re.search(r'\b2\s*[°º]?\s*\.?\s*DO\b|SEGUNDO|RECARGO|ANTERIOR', L):   # "Total al 2do. vencimiento" (con recargo)
            return None
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
        vals = [0.0 if re.match(r'^-?0+(?:[.,]0+)?$|^-$', s) else money(s) for s in segs]   # celdas "0" o "-" = cero
        # Fila de valores debajo de una fila de encabezados con la misma cantidad de columnas
        if prev_segs and len(vals) >= 3 and all(v is not None for v in vals) and len(prev_segs) == len(vals) \
                and all(money(s) is None for s in prev_segs):
            for h, v in zip(prev_segs, vals):
                c = clasif(h)
                if c and v:
                    out.append(dict(cls=c, val=v, rate=rate_in(h), label=h, clave=clave_etiqueta(h), modo='columna'))
        # Pares etiqueta → importe dentro del renglón
        toks = l2.split()
        label, pend_rate, hubo_num = [], None, False
        pend_val = None   # número chico tomado como alícuota: si no viene otro importe atrás, era el importe
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
            if c in ('IVA', 'PERC_IIBB', 'PERC_IVA', 'PERC_GEN', 'OTROS') and not hubo_num and pend_rate is None \
                    and (v in RATES or (c != 'IVA' and v < 10)):
                pend_rate = v      # "I.V.A. 21.00 base monto" / "Perc IIBB CABA 0.50 1.118,08"
                pend_val = dict(cls=c, val=v, rate=None, label=lab, clave=clave_etiqueta(lab), modo='linea')
                continue
            pend_val = None
            if c:
                rate = pend_rate if c == 'IVA' and pend_rate in RATES else rate_in(lab)
                out.append(dict(cls=c, val=v, rate=rate, label=lab, clave=clave_etiqueta(lab), modo='linea'))
            hubo_num = True
        if pend_val and pend_val['cls'] != 'IVA':   # "PERCEP. IB Tucuman .01 % 3.12"
            out.append(pend_val)
        prev_segs = segs
    return out


def fechas_etiquetadas(texto):
    """Pares etiqueta → fecha (para aprender dónde está el vencimiento de pago)."""
    out, prev = [], ''
    for l in texto.splitlines():
        cerca_cae = bool(re.search(r'C\.?\s?A\.?\s?E\b|C\.?\s?E\.?\s?S\.?\s?P\b', l + ' ' + prev, re.I))
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
        if re.search(r'VTO|VENC', x['clave']) and not re.search(r'C\.?A\.?E|C\.?E\.?S\.?P|PROXIM|\bDO\b|SEGUNDO|RECARGO', x['clave']) \
                and not x.get('cerca_cae'):
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


def _subsets_extras_libre(extras):
    for k in range(0, min(6, len(extras)) + 1):
        for S in itertools.combinations(extras, k):
            if len({x['val'] for x in S}) == len(S):
                yield S


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
    # A2) por cuadre, cuando el IVA no se puede leer del PDF (p. ej. "1.848.919," cortado):
    #     se calcula neto × alícuota y tiene que cerrar al centavo con el total del QR
    if cuadre and not sols:
        for n in netos:
            for r in RATES:
                teorico = n['val'] * r / 100
                for S in _subsets_extras(extras, round(total - n['val'] - teorico, 2)):
                    iv = round(total - n['val'] - sum(x['val'] for x in S), 2)   # el IVA que cierra exacto con el QR
                    if iv <= 0 or abs(iv - teorico) > 0.015:
                        continue
                    c_iva = dict(cls='IVA', val=iv, rate=r, label='', clave='', modo='calculado')
                    sols.append(dict(gravado=[dict(alicuota=r, neto=n['val'], iva=iv, c_neto=n, c_iva=c_iva, iva_calculado=True)],
                                     extras=list(S), score=_extras_score(S)))
    # A3) neto por diferencia: el neto no figura como un solo importe (luz: "Subtotal costo energía" + cargos aparte)
    #     pero el IVA trae su alícuota impresa. neto = total − IVA − extras y tiene que dar el IVA al centavo.
    if not cuadre and not sols:
        for iv in ivas:
            if not iv['rate']:
                continue
            for S in _subsets_extras_libre(extras):
                n = round(total - iv['val'] - sum(x['val'] for x in S), 2)
                if n > 0 and abs(n * iv['rate'] / 100 - iv['val']) <= 0.02:
                    sols.append(dict(gravado=[dict(alicuota=iv['rate'], neto=n, iva=iv['val'], c_neto=None, c_iva=iv, neto_calculado=True)],
                                     extras=list(S), score=_extras_score(S)))
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
    extras, claves_usadas = [], set()
    for e in pl.get('extras', []):
        v = _buscar(cands, e.get('clave'), EXTRA_CLS)
        if v:
            extras.append(dict(cls=e['cls'], val=v[0], label=e.get('etiqueta') or e.get('clave'), clave=e.get('clave'),
                               jurisdiccion=e.get('jurisdiccion')))
            claves_usadas.add(e.get('clave'))
    if len(grav) == 1 and abs(grav[0]['neto'] * grav[0]['alicuota'] / 100 - grav[0]['iva']) > _tol_iva(grav[0]['neto']):
        # El neto impreso no es toda la base (luz: cargos que se suman aparte). Si total − IVA − extras da
        # exactamente el IVA con la alícuota impresa, ese es el neto.
        g = grav[0]
        n2 = round(total - g['iva'] - sum(x['val'] for x in extras), 2)
        if n2 > 0 and abs(n2 * g['alicuota'] / 100 - g['iva']) <= 0.02:
            g['neto'] = n2
    for g in grav:
        if abs(g['neto'] * g['alicuota'] / 100 - g['iva']) > _tol_iva(g['neto']):
            problemas.append(f"El IVA {g['alicuota']}% ({g['iva']:.2f}) no corresponde al neto {g['neto']:.2f}.")
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
        'tipo_comprobante_arca': {'type': 'INTEGER', 'nullable': True, 'description': 'Código ARCA: 1 FA, 2 NDA, 3 NCA, 6 FB, 11 FC, 51 FM, 201 FCE A, 17 Liquidación de Servicios Públicos A, 18 Liquidación de Servicios Públicos B, 81 Tique Factura A...'},
        'tipo_autorizacion': {'type': 'STRING', 'nullable': True, 'enum': ['CAE', 'CAEA', 'CAI', 'CESP'],
                              'description': 'Qué código de autorización trae: CAE (lo normal), CAEA, CAI, o CESP (C.E.S.P., facturas de luz/gas/agua)'},
        'punto_venta': {'type': 'INTEGER', 'nullable': True}, 'numero': {'type': 'INTEGER', 'nullable': True},
        'fecha_emision': _S('YYYY-MM-DD'), 'fecha_vencimiento_pago': _S('YYYY-MM-DD (no el vencimiento del CAE)'),
        'cae': _S('Código de autorización de 14 dígitos (CAE, CAEA, CAI o C.E.S.P.)'),
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


def gemini_leer(pdf_bytes, cuentas, empresas=None):
    key = os.environ.get('GEMINI_API_KEY')
    if not key:
        raise RuntimeError('Falta GEMINI_API_KEY para leer un proveedor nuevo.')
    model = (os.environ.get('GEMINI_MODEL') or '').strip()
    listado = '\n'.join(f"{c['codigo_concepto']} — {c['denominacion']}" for c in cuentas[:400])
    prompt = ('Sos un analista contable argentino. Extraé los datos de este comprobante de proveedor recibido por Lucciano\'s. '
              'Importes como número con punto decimal. No inventes: si algo no figura, null. Leé una sola copia si hay original/duplicado. '
              'Neto + IVA + no gravado + exento + otros tributos + percepciones debe dar el total. '
              'Las facturas de luz, gas o agua suelen ser "Liquidación de Servicios Públicos" (tipo 17 si es A, 18 si es B) '
              'y traen C.E.S.P. en lugar de CAE: en ese caso tipo_autorizacion = CESP.'
              + (('\nEl receptor (cliente) es una de estas sociedades del grupo, buscá su CUIT en el bloque del cliente: '
                  + ', '.join(sorted(empresas)) + '.') if empresas else '')
              + (f'\n\nPlan de cuentas para sugerir imputación:\n{listado}' if listado else ''))
    body = {'contents': [{'role': 'user', 'parts': [{'inline_data': {'mime_type': 'application/pdf', 'data': base64.b64encode(pdf_bytes).decode()}}, {'text': prompt}]}],
            'generationConfig': {'responseMimeType': 'application/json', 'responseSchema': ESQUEMA_GEMINI, 'temperature': 0}}
    base = os.environ.get('GEMINI_BASE', 'https://generativelanguage.googleapis.com')

    def llamar(m):
        req = urllib.request.Request(f'{base}/v1beta/models/{m}:generateContent?key={key}', data=json.dumps(body).encode(),
                                     headers={'Content-Type': 'application/json'}, method='POST')
        with urllib.request.urlopen(req, timeout=180) as r:
            return json.loads(r.read().decode('utf-8'))

    # Primero el modelo fijado en GEMINI_MODEL (si hay); si da 404 (no disponible) o 429 (sin cupo en el
    # plan gratuito), se prueban los demás modelos que tiene habilitados la clave, del más conveniente al menos.
    probar = ([model] if model else []) + [m for m in gemini_modelos(base, key) if m != model]
    errores = []
    for m in probar[:5]:
        data = None
        for intento in range(3):
            try:
                data = llamar(m)
                break
            except urllib.error.HTTPError as e:
                if e.code in (500, 502, 503, 504) and intento < 2:   # Gemini saturado: se espera y se reintenta
                    time.sleep(10 * (intento + 1))
                    continue
                errores.append(f'{m}: HTTP {e.code}')
                if e.code in (404, 429, 500, 502, 503, 504):        # no disponible / sin cupo / caído: el próximo modelo
                    break
                raise RuntimeError(f'Gemini HTTP {e.code} ({m}): {e.read().decode("utf-8", "replace")[:300]}')
        if data is None:
            continue
        if errores:
            print(f'  Gemini: usé {m} (antes fallaron: {", ".join(errores)}). Conviene fijar GEMINI_MODEL={m} en GitHub.')
        txt = ''.join(p.get('text', '') for p in data.get('candidates', [{}])[0].get('content', {}).get('parts', []))
        return json.loads(txt), m
    raise RuntimeError('Ningún modelo de Gemini respondió: ' + '; '.join(errores or ['la clave no tiene modelos habilitados']))


_MODELOS = []


def gemini_modelos(base, key):
    """Modelos de la clave, ordenados: Flash estable más nuevo, Pro estable, Flash preview, Pro preview.
    Flash primero porque el plan gratuito de la API le da cupo; a los Pro muchas veces no."""
    if _MODELOS:
        return _MODELOS
    nombres, token = [], ''
    for _ in range(10):
        url = f'{base}/v1beta/models?pageSize=200&key={key}' + (f'&pageToken={token}' if token else '')
        with urllib.request.urlopen(url, timeout=60) as r:
            j = json.loads(r.read().decode('utf-8'))
        for m in j.get('models', []):
            if 'generateContent' in (m.get('supportedGenerationMethods') or []):
                nombres.append(m['name'].split('/')[-1])
        token = j.get('nextPageToken')
        if not token:
            break

    def puntaje(n):
        mm = re.match(r'^gemini-(\d+(?:\.\d+)?)-(pro|flash)(-latest|-preview(?:-\d{2}-\d{4}|-\d{2}-\d{2})?)?$', n)
        if not mm:
            return None
        estable = mm.group(3) in (None, '-latest')
        es_flash = mm.group(2) == 'flash'
        return (2 if estable else 0) + (1 if es_flash else 0), float(mm.group(1)), mm.group(3) is None

    puntuados = [(puntaje(n), n) for n in nombres]
    _MODELOS.extend(n for p, n in sorted([x for x in puntuados if x[0] is not None], reverse=True))
    return _MODELOS
    nombres, token = [], ''
    for _ in range(10):
        url = f'{base}/v1beta/models?pageSize=200&key={key}' + (f'&pageToken={token}' if token else '')
        with urllib.request.urlopen(url, timeout=60) as r:
            j = json.loads(r.read().decode('utf-8'))
        for m in j.get('models', []):
            if 'generateContent' in (m.get('supportedGenerationMethods') or []):
                nombres.append(m['name'].split('/')[-1])
        token = j.get('nextPageToken')
        if not token:
            break

    def puntaje(n):
        mm = re.match(r'^gemini-(\d+(?:\.\d+)?)-(pro|flash)(.*)$', n)
        if not mm or n == excluir or re.search(r'lite|image|tts|audio|live|thinking|computer|embedding|exp', mm.group(3)):
            return None
        estable = mm.group(3) in ('', '-latest')
        return (1 if mm.group(2) == 'pro' else 0, 1 if estable else 0, float(mm.group(1)), mm.group(3) == '')

    cands = sorted((p, n) for n in nombres if (p := puntaje(n)) is not None)
    _MODELO_ELEGIDO['m'] = cands[-1][1] if cands else None
    return _MODELO_ELEGIDO['m']


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
    ta = str(g.get('tipo_autorizacion') or '').upper()
    if ta in ('CAEA', 'CAI', 'CESP') and c.get('tipo_autorizacion', 'CAE') == 'CAE':
        c['tipo_autorizacion'] = ta
    # Servicios públicos (C.E.S.P.): son tipo 17/18 aunque Gemini diga "Factura A"
    if c.get('tipo_autorizacion') == 'CESP' and c.get('tipo_arca') in (1, 6, None):
        c['tipo_arca'] = 18 if c.get('tipo_arca') == 6 else 17
        c['letra'] = LETRA.get(c['tipo_arca'])
    if not d['importes']['total']:
        d['importes']['total'] = num(g.get('total'))
    c['letra'] = c.get('letra') or LETRA.get(c.get('tipo_arca'))
    return d


def reclasificar_percepcion_iva(d, texto):
    """Algunos emisores ponen la percepción de IVA (RG 5329/3337/2408) en el renglón "Importe otros tributos".
    Si el mismo importe aparece en un renglón de percepción de IVA, va como percepción (es crédito fiscal, no costo)."""
    ot = round(d['importes'].get('otros_tributos') or 0, 2)
    if ot <= 0:
        return None
    lineas = [l for l in texto.splitlines() if l.strip()]
    for i, l in enumerate(lineas):
        ctx = norm(l + ' ' + (lineas[i - 1] if i else ''))
        if not (re.search(r'PERC', ctx) and re.search(r'\bI\.?V\.?A\b|5329|3337|2408', ctx)):
            continue
        vals = [money(t) for t in re.sub(r'\$', ' ', l).split()]
        if any(v is not None and abs(v - ot) < 0.01 for v in vals):
            d['importes']['otros_tributos'] = 0.0
            d['percepciones'].append(dict(tipo='IVA', jurisdiccion=None, importe=ot, descripcion='Percepción de IVA (figuraba como otros tributos)'))
            return f'La percepción de IVA ({ot:.2f}) figuraba como “otros tributos”: se cargó como percepción de IVA.'
    return None


def suma_componentes(d):
    im = d['importes']
    s = sum(g['neto'] + g['iva'] for g in im['gravado']) + im['sin_discriminar'] + im['no_gravado'] + im['exento'] + im['otros_tributos']
    return round(s + sum(p['importe'] for p in d['percepciones']), 2)


# ---------------------------------------------------------------------------
#  Encabezado sin QR (respaldo por texto)
# ---------------------------------------------------------------------------
LETRA = {1: 'A', 2: 'A', 3: 'A', 6: 'B', 7: 'B', 8: 'B', 11: 'C', 12: 'C', 13: 'C', 51: 'M', 52: 'M', 53: 'M', 17: 'A', 18: 'B',
         81: 'A', 82: 'B', 83: 'B',
         201: 'A', 202: 'A', 203: 'A', 206: 'B', 207: 'B', 208: 'B', 211: 'C', 212: 'C', 213: 'C'}


# Emisores que NO imprimen su CUIT en el PDF: se reconocen por la razón social (Edenor, p. ej.)
EMISORES_SIN_CUIT = [('30656516514', r'EDENOR|EMPRESA DISTRIBUIDORA Y COMERCIALIZADORA NORTE')]

# Liquidación de Servicios Públicos (luz, gas, agua): tipo ARCA 17 (A) / 18 (B), autorizada con C.E.S.P.
RX_LSP = r'LIQUIDACI[OÓ]N DE SERVICIOS? P[UÚ]BLICOS?'


def emisor_por_texto(texto, plantillas=None):
    T = norm(texto)
    for cuit, rx in EMISORES_SIN_CUIT:
        if re.search(rx, T):
            return cuit
    # Proveedor ya confirmado cuya razón social aparece en el PDF (al menos 2 palabras significativas)
    for cuit, pl in (plantillas or {}).items():
        rs = re.sub(r'\b(S\.?A\.?|S\.?R\.?L\.?|SAS|SOCIEDAD ANONIMA)\b', '', norm(pl.get('razon_social') or '')).strip(' .,')
        if len(rs) >= 8 and len(rs.split()) >= 2 and rs in T:
            return cuit
    return None


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
    if not h['cae']:
        m = re.search(r'C\.?\s?E\.?\s?S\.?\s?P\.?\s*(?:N[°º.o]*)?\s*:?\s*(\d{14})', texto, re.I)
        if m:
            h['cae'], h['tipo_autorizacion'] = m.group(1), 'CESP'
    # Liquidación de servicios públicos: la letra va antes o después ("B Liquidación…" / "…Públicos A 0099-0078286335")
    T = texto.upper()
    m = re.search(r'(?<![A-Z.])([AB])\s+' + RX_LSP, T) or re.search(RX_LSP + r'\s+([AB])\b', T)
    lsp = bool(m)
    if m:
        h['tipo'] = 17 if m.group(1) == 'A' else 18
    # Número: primero el que está junto a "Liquidación de servicios públicos" (las facturas de luz traen otros números sueltos)
    m = (re.search(RX_LSP + r'[^\n]{0,25}?(?<!\d)(\d{4,5})\s*-\s*(\d{8,10})(?!\d)', T) if lsp else None) \
        or re.search(r'(?<!\d)(\d{4,5})\s*-\s*(\d{8})(?!\d)', texto) \
        or re.search(r'(?<!\d)(\d{4,5})\s*-\s*(0{1,2}\d{8})(?!\d)', texto)
    if m and int(m.group(2)) < 10 ** 8:
        h['pto_vta'], h['numero'] = int(m.group(1)), int(m.group(2))
    if not lsp:
        m = re.search(r'C[OÓ]D(?:IGO)?\.?\s*N?[°º]?\s*:?\s*0*(\d{1,3})\b', texto, re.I)
        h['tipo'] = int(m.group(1)) if m and int(m.group(1)) in LETRA else None
    m = re.search(r'Fecha(?:\s+de)?(?:\s+Emisi[oó]n)?\s*:?\s*(\d{1,2}\s*[/.\-]\s*\d{1,2}\s*[/.\-]\s*\d{2,4})', texto, re.I) \
        or re.search(r'Emisi[oó]n\s*:?\s*(\d{1,2}\s*/\s*\d{1,2}\s*/\s*\d{4})', texto, re.I)
    h['fecha'] = fecha_iso(m.group(1)) if m else None
    if not h['fecha']:   # "FECHA DE EMISION" con la fecha en otra columna o renglón
        m = re.search(r'FECHA\s+DE\s+EMISI[OÓ]N[\s\S]{0,250}?(\d{2}/\d{2}/\d{4})', texto, re.I)
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
                        'cotizacion': (qr or {}).get('cotizacion'), 'tipo_autorizacion': src.get('tipo_autorizacion') or 'CAE',
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
    aviso_qr = corregir_escala_qr(qr, texto)
    aviso_tipo = corregir_tipo_qr(qr, texto)
    if aviso_tipo:
        aviso_qr = (aviso_qr + ' ' if aviso_qr else '') + aviso_tipo
    h = encabezado_texto(texto, empresas) if not qr else {}
    d = datos_base(qr, h)
    if not d['receptor']['cuit']:   # QR sin receptor: se busca un CUIT del grupo en el texto
        d['receptor']['cuit'] = encabezado_texto(texto, empresas).get('doc_receptor')
    if not d['emisor']['cuit']:   # el PDF no trae el CUIT del emisor (Edenor) o vino en otro formato
        d['emisor']['cuit'] = emisor_por_texto(texto, ctx.get('plantillas'))
    cands = candidatos(texto)
    cuit = d['emisor']['cuit']
    pl = (ctx.get('plantillas') or {}).get(cuit) if cuit else None
    problemas, metodo, modelo = ([aviso_qr] if aviso_qr else []), None, None
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
                if any(g.get('neto_calculado') for g in sols[0]['gravado']):
                    problemas.append('El neto no figura como un solo importe en el PDF: se calculó como total − IVA − otros conceptos '
                                     'y cierra al centavo con la alícuota impresa. Revisalo.')
                if any(g.get('iva_calculado') for g in sols[0]['gravado']):
                    problemas.append('El IVA no se pudo leer del PDF: se calculó (neto × alícuota) y cierra con el total del QR. Revisalo.')
            d['comprobante']['fecha_vto_pago'] = buscar_vto(texto)
        elif not os.environ.get('GEMINI_API_KEY'):
            # Sin Gemini configurado: no se traba, va a la bandeja para completarla a mano
            metodo = 'manual'
            problemas.append('Las reglas generales no alcanzaron para leer esta factura y Gemini no está configurado: '
                             'completá los datos a mano mirando el PDF y confirmá el proveedor.')
            d['comprobante']['fecha_vto_pago'] = buscar_vto(texto)
        else:
            metodo = 'ia'
            g, modelo = gemini_leer(pdf, ctx.get('cuentas') or [], empresas)
            d = gemini_a_datos(g, d)
            rc = d['receptor'].get('cuit')
            if rc and (not cuit_valido(rc) or (empresas and rc not in empresas)):
                # Gemini leyó mal un dígito: si hay una sola sociedad del grupo que difiere en 1-2 dígitos, es esa
                cerca = [e for e in empresas if len(e) == len(rc) and sum(a != b for a, b in zip(e, rc)) <= 2]
                if len(cerca) == 1:
                    problemas.append(f'El CUIT del receptor leído ({rc}) no era válido: se tomó {cerca[0]} (sociedad del grupo). Verificalo.')
                    d['receptor']['cuit'] = cerca[0]
            if not d['receptor'].get('cuit'):
                problemas.append('No se pudo leer el CUIT del receptor: completalo en la pestaña Datos (sin él ARCA no puede constatar).')
            aviso = corregir_escala_total(d) if not qr else None   # con QR el total es el del QR (ya validado contra el PDF)
            if aviso:
                problemas.append(aviso)
            if abs(suma_componentes(d) - d['importes']['total']) > TOL:
                problemas.append(f"La lectura de Gemini no cuadra: componentes {suma_componentes(d):.2f} vs total {d['importes']['total']:.2f}.")
            if not qr:
                problemas.append('Sin QR legible: el encabezado (CUIT, número, CAE) lo leyó Gemini. Verificalo contra el PDF.')
    if not qr:
        bar = leer_barras(doc)
        if bar:
            c = d['comprobante']
            dif = [k for k, a, b in (('CUIT emisor', d['emisor'].get('cuit'), bar['cuit_emisor']), ('tipo', c.get('tipo_arca'), bar['tipo']),
                                     ('punto de venta', c.get('pto_vta'), bar['pto_vta']), ('CAE', c.get('cae'), bar['cae'])) if a and str(a) != str(b)]
            d['emisor']['cuit'] = bar['cuit_emisor']
            c['tipo_arca'], c['letra'], c['pto_vta'], c['cae'] = bar['tipo'], LETRA.get(bar['tipo']), bar['pto_vta'], bar['cae']
            c['cae_vto'] = c.get('cae_vto') or bar['cae_vto']
            qr_via = 'barras'
            if dif:
                problemas.append('Se corrigió con el código de barras de ARCA: ' + ', '.join(dif) + '.')
    aviso_perc = reclasificar_percepcion_iva(d, texto)
    if aviso_perc:
        problemas.append(aviso_perc)
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
