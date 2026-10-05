#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CAZAOFERTAS CHILE — Monitor de ofertas y errores de precio
Falabella · Ripley · Paris · Hites · Abcdin (abc.cl) · y cualquier tienda que agregues

Qué hace:
  - Revisa cada X minutos búsquedas/categorías de cada tienda (con navegador real, Playwright).
  - Guarda el historial de precios de cada producto (SQLite, archivo precios.db).
  - Detecta 3 cosas:
      1) OFERTA: descuento grande vs. precio normal publicado.
      2) POSIBLE ERROR: descuento extremo o caída brusca vs. su propio historial.
      3) REVISAR: precio absurdamente bajo comparado con productos de la misma búsqueda.
  - Te avisa por Telegram (al celular) con nombre, precio, % y LINK directo. Nunca repite la misma alerta.

Instalación (una sola vez):
    pip install playwright requests
    python -m playwright install chromium

Configurar Telegram (5 minutos):
    1) En Telegram habla con @BotFather -> /newbot -> copia el TOKEN abajo.
    2) Escríbele cualquier cosa a tu bot nuevo.
    3) Ejecuta:  python cazaofertas.py --chatid   -> copia el número en TELEGRAM_CHAT_ID.
    4) Prueba:   python cazaofertas.py --test

Uso:
    python cazaofertas.py          -> monitoreo continuo (déjalo corriendo)
    python cazaofertas.py --once   -> una sola pasada
"""

import argparse
import os
import random
import re
import sqlite3
import statistics
import sys
import time
from datetime import datetime
from urllib.parse import quote_plus

import requests
from playwright.sync_api import sync_playwright

# ════════════════════════════════════════════════════════════════════
# CONFIGURACIÓN — edita solo esta sección
# ════════════════════════════════════════════════════════════════════

# En la nube (GitHub) estos datos se leen de los "Secrets"; en tu PC puedes pegarlos aquí.
TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN") or ""        # ej: "7123456789:AAH...."
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID") or ""    # ej: "123456789"

MODO_NUBE = os.getenv("MODO_NUBE") == "1"
INTERVALO_MIN = 15                 # minutos entre rondas completas (solo modo PC)
PAUSA_ENTRE_PAGINAS = (2, 5) if MODO_NUBE else (6, 14)   # segundos entre páginas
HEADLESS = os.getenv("HEADLESS", "1") != "0"   # 0 = navegador "visible" (ayuda contra bloqueos)
MAX_SEGUNDOS_RONDA = int(os.getenv("MAX_SEGUNDOS", "0")) or None   # corta la ronda a tiempo en la nube
LATIDO_DIARIO = True               # 1 mensaje al día confirmando que sigue funcionando

# Umbrales de detección
DESCUENTO_OFERTA = 0.50            # 50%+ de descuento -> OFERTA
DESCUENTO_ERROR = 0.75             # 75%+ de descuento -> POSIBLE ERROR
CAIDA_HISTORICA_ERROR = 0.60       # cae 60%+ bajo su mediana histórica -> POSIBLE ERROR
ANOMALIA_VS_BUSQUEDA = 0.20        # cuesta < 20% de la mediana de su búsqueda -> REVISAR
PRECIO_NORMAL_MINIMO = 30000       # ignora productos cuyo precio normal sea menor (ruido)

# Qué buscar en todas las tiendas (cámbialo a gusto)
TERMINOS = [
    "notebook",
    "televisor",
    "consola",
    "tarjeta de video",
    "celular",
    "monitor gamer",
]
# Desde el celular: variable TERMINOS en GitHub, separada por comas (reemplaza la lista de arriba)
if os.getenv("TERMINOS"):
    TERMINOS = [t.strip() for t in os.getenv("TERMINOS").split(",") if t.strip()]

# Palabras que descartan un producto (accesorios, usados, etc.)
PALABRAS_EXCLUIDAS = [
    "reacondicionado", "usado", "funda", "carcasa", "lámina", "lamina",
    "cable", "soporte", "protector", "mica", "skin", "repuesto",
]

# Solo avisar si el nombre contiene alguna de estas palabras (vacío = avisar todo)
PALABRAS_OBLIGATORIAS = []
if os.getenv("SOLO_CON"):   # variable SOLO_CON en GitHub, ej: "ps5,rtx,oled"
    PALABRAS_OBLIGATORIAS = [t.strip() for t in os.getenv("SOLO_CON").split(",") if t.strip()]

# Patrón genérico para reconocer links de producto (VTEX "/p", ".html", "/product/", códigos largos)
PATRON_GENERICO = r"(/p(\?|$)|\.html|/product/|-\d{6,}p|/\d{6,})"

TIENDAS = {
    "Falabella": {
        "busqueda": "https://www.falabella.com/falabella-cl/search?Ntt={q}",
        "patron": r"/falabella-cl/product/\d+",
        "urls_extra": [],
    },
    "Ripley": {
        "busqueda": "https://simple.ripley.cl/search/{q}",
        "patron": r"ripley\.cl/[^?#]*-\d{6,}p|mpm\d+",
        "urls_extra": [],
    },
    "Paris": {
        "busqueda": "https://www.paris.cl/search/?q={q}",
        "patron": PATRON_GENERICO,
        "urls_extra": [],
    },
    "Hites": {
        "busqueda": "https://www.hites.com/search?q={q}",
        "patron": PATRON_GENERICO,
        "urls_extra": [],
    },
    "Abcdin": {
        "busqueda": "https://www.abc.cl/search?q={q}",
        "patron": PATRON_GENERICO,
        "urls_extra": [],
    },
}
# TIP: si una búsqueda no funciona, abre la categoría en tu navegador (ej. "Liquidación" u
# "Ofertas tecnología"), copia la URL y pégala en "urls_extra" de esa tienda.

DB_PATH = "precios.db"

# ════════════════════════════════════════════════════════════════════
# Extracción (JavaScript dentro del navegador): link + nombre + precios de cada tarjeta
# ════════════════════════════════════════════════════════════════════

JS_EXTRAER = r"""
(patronSrc) => {
  const re = new RegExp(patronSrc, 'i');
  const priceRe = /\$\s?\d{1,3}(?:\.\d{3})+|\$\s?\d{4,}/g;
  const limpia = h => h.split('#')[0].split('?')[0];
  const out = {};
  const links = [...document.querySelectorAll('a[href]')].filter(a => re.test(a.href));
  for (const a of links) {
    const key = limpia(a.href);
    if (out[key]) continue;
    // subir hasta la "tarjeta" del producto (contenedor con un solo producto)
    let el = a;
    for (let i = 0; i < 8 && el.parentElement; i++) {
      const p = el.parentElement;
      const hrefs = new Set([...p.querySelectorAll('a[href]')]
        .filter(x => re.test(x.href)).map(x => limpia(x.href)));
      if (hrefs.size > 1) break;
      el = p;
    }
    // precios del texto, ignorando cuotas/ahorro/despacho
    const precios = [];
    const walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT);
    let n;
    while ((n = walker.nextNode())) {
      const t = n.textContent || '';
      const m = t.match(priceRe);
      if (!m) continue;
      const ctx = ((n.parentElement && n.parentElement.textContent) || t).toLowerCase();
      if (/cuota|\/mes|mensual|ahorr|despacho|env[ií]o|desde \$/.test(ctx)) continue;
      for (const s of m) {
        const v = parseInt(s.replace(/\D/g, ''), 10);
        if (v >= 1000) precios.push(v);
      }
    }
    if (!precios.length) continue;
    let nombre = (a.getAttribute('title') || '').trim();
    if (!nombre) {
      const img = el.querySelector('img[alt]');
      if (img && img.alt && img.alt.length > 5) nombre = img.alt.trim();
    }
    if (!nombre) {
      const lineas = (el.innerText || '').split('\n').map(s => s.trim())
        .filter(s => s.length > 8 && !s.includes('$'));
      nombre = lineas.sort((x, y) => y.length - x.length)[0] || key;
    }
    out[key] = { url: key, nombre: nombre.slice(0, 160), precios };
  }
  return Object.values(out);
}
"""

# ════════════════════════════════════════════════════════════════════
# Utilidades
# ════════════════════════════════════════════════════════════════════

def log(msg):
    print(f"[{datetime.now():%H:%M:%S}] {msg}", flush=True)


def clp(n):
    return "$" + f"{n:,}".replace(",", ".")


def html_escape(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def enviar_telegram(texto):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return False
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": texto,
                  "parse_mode": "HTML", "disable_web_page_preview": False},
            timeout=20,
        )
        return r.ok
    except requests.RequestException as e:
        log(f"Error Telegram: {e}")
        return False


def beep():
    try:
        import winsound
        winsound.Beep(1200, 400)
    except Exception:
        print("\a", end="", flush=True)

# ════════════════════════════════════════════════════════════════════
# Base de datos
# ════════════════════════════════════════════════════════════════════

def db_init():
    con = sqlite3.connect(DB_PATH)
    con.executescript("""
        CREATE TABLE IF NOT EXISTS precios(
            url TEXT, tienda TEXT, nombre TEXT, precio INTEGER, normal INTEGER, ts TEXT);
        CREATE INDEX IF NOT EXISTS ix_precios_url ON precios(url);
        CREATE TABLE IF NOT EXISTS alertas(
            url TEXT, precio INTEGER, nivel TEXT, ts TEXT, PRIMARY KEY(url, precio));
        CREATE TABLE IF NOT EXISTS avisos(clave TEXT, dia TEXT, PRIMARY KEY(clave, dia));
        CREATE TABLE IF NOT EXISTS config(k TEXT PRIMARY KEY, v TEXT);
    """)
    con.commit()
    return con


def cfg_get(con, k, defecto=None):
    r = con.execute("SELECT v FROM config WHERE k=?", (k,)).fetchone()
    return r[0] if r else defecto


def cfg_set(con, k, v):
    con.execute("INSERT OR REPLACE INTO config VALUES(?,?)", (k, str(v)))
    con.commit()

# ════════════════════════════════════════════════════════════════════
# Control desde Telegram (comandos al bot)
# ════════════════════════════════════════════════════════════════════

AYUDA = (
    "<b>Comandos de Cazaofertas</b>\n"
    "/lista — ver qué estoy buscando\n"
    "/buscar ps5 — agregar búsqueda\n"
    "/quitar ps5 — quitar búsqueda\n"
    "/solo rtx, oled — avisar solo si el nombre tiene esas palabras\n"
    "/solo — quitar ese filtro\n"
    "/descuento 60 — % mínimo para avisar ofertas\n"
    "/pausa — dejar de buscar\n"
    "/activar — volver a buscar\n"
    "/estado — resumen\n"
    "(Respondo en la próxima ronda, máx. ~15 min)"
)


def tg_updates(offset):
    try:
        r = requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
                         params={"offset": offset, "timeout": 0}, timeout=20)
        return r.json().get("result", []) if r.ok else []
    except requests.RequestException:
        return []


def cargar_config(con):
    """Aplica la configuración guardada (la que cambias por Telegram)."""
    global TERMINOS, PALABRAS_OBLIGATORIAS, DESCUENTO_OFERTA, TELEGRAM_CHAT_ID
    t = cfg_get(con, "terminos")
    if t is not None:
        TERMINOS = [x for x in t.split("|") if x]
    s = cfg_get(con, "solo_con")
    if s is not None:
        PALABRAS_OBLIGATORIAS = [x for x in s.split("|") if x]
    d = cfg_get(con, "descuento")
    if d:
        DESCUENTO_OFERTA = float(d)
    if not TELEGRAM_CHAT_ID:
        TELEGRAM_CHAT_ID = cfg_get(con, "chat_id", "")


def procesar_comandos(con):
    """Lee los mensajes nuevos del bot: detecta tu chat y ejecuta comandos."""
    global TELEGRAM_CHAT_ID
    if not TELEGRAM_TOKEN:
        return
    offset = int(cfg_get(con, "offset", "0"))
    for u in tg_updates(offset):
        cfg_set(con, "offset", u["update_id"] + 1)
        msg = u.get("message") or {}
        chat = str((msg.get("chat") or {}).get("id", ""))
        texto = (msg.get("text") or "").strip()
        if not chat:
            continue
        if not TELEGRAM_CHAT_ID:                      # primer mensaje = dueño del bot
            TELEGRAM_CHAT_ID = chat
            cfg_set(con, "chat_id", chat)
            enviar_telegram("✅ <b>Cazaofertas conectado.</b> Desde ahora te aviso aquí.\n\n" + AYUDA)
            continue
        if chat != str(TELEGRAM_CHAT_ID):             # ignora a desconocidos
            continue
        cmd, _, arg = texto.partition(" ")
        cmd, arg = cmd.lower().split("@")[0], arg.strip()
        if cmd == "/buscar" and arg:
            if arg.lower() not in [t.lower() for t in TERMINOS]:
                TERMINOS.append(arg)
            cfg_set(con, "terminos", "|".join(TERMINOS))
            enviar_telegram(f"➕ Agregado: <b>{html_escape(arg)}</b>")
        elif cmd == "/quitar" and arg:
            TERMINOS[:] = [t for t in TERMINOS if t.lower() != arg.lower()]
            cfg_set(con, "terminos", "|".join(TERMINOS))
            enviar_telegram(f"➖ Quitado: <b>{html_escape(arg)}</b>")
        elif cmd == "/lista":
            enviar_telegram("🔍 Buscando:\n• " + "\n• ".join(map(html_escape, TERMINOS)))
        elif cmd == "/solo":
            PALABRAS_OBLIGATORIAS[:] = [x.strip() for x in arg.split(",") if x.strip()]
            cfg_set(con, "solo_con", "|".join(PALABRAS_OBLIGATORIAS))
            enviar_telegram("🎯 Filtro: " + (", ".join(PALABRAS_OBLIGATORIAS) or "sin filtro"))
        elif cmd == "/descuento" and arg.rstrip("%").isdigit():
            cfg_set(con, "descuento", int(arg.rstrip("%")) / 100)
            cargar_config(con)
            enviar_telegram(f"📉 Aviso ofertas desde {arg.rstrip('%')}% de descuento.")
        elif cmd == "/pausa":
            cfg_set(con, "pausa", "1"); enviar_telegram("⏸️ En pausa. Escribe /activar para seguir.")
        elif cmd == "/activar":
            cfg_set(con, "pausa", "0"); enviar_telegram("▶️ Búsqueda activada.")
        elif cmd == "/estado":
            n = con.execute("SELECT COUNT(DISTINCT url) FROM precios").fetchone()[0]
            a = con.execute("SELECT COUNT(*) FROM alertas").fetchone()[0]
            p = "pausado" if cfg_get(con, "pausa") == "1" else "activo"
            enviar_telegram(f"📊 Estado: {p}\nProductos vigilados: {n}\nAlertas enviadas: {a}\n"
                            f"Búsquedas: {len(TERMINOS)} · Ofertas desde {DESCUENTO_OFERTA:.0%}")
        else:
            enviar_telegram(AYUDA)


def historial(con, url, limite=60):
    rows = con.execute(
        "SELECT precio FROM precios WHERE url=? ORDER BY ts DESC LIMIT ?", (url, limite)
    ).fetchall()
    return [r[0] for r in rows]


def guardar_precio(con, p, tienda):
    previo = con.execute(
        "SELECT precio FROM precios WHERE url=? ORDER BY ts DESC LIMIT 1", (p["url"],)
    ).fetchone()
    if previo is None or previo[0] != p["actual"]:
        con.execute("INSERT INTO precios VALUES(?,?,?,?,?,?)",
                    (p["url"], tienda, p["nombre"], p["actual"], p["normal"],
                     datetime.now().isoformat(timespec="seconds")))


def aviso_diario(con, clave, texto):
    """Envía un mensaje como máximo una vez al día por clave."""
    dia = datetime.now().strftime("%Y-%m-%d")
    if con.execute("SELECT 1 FROM avisos WHERE clave=? AND dia=?", (clave, dia)).fetchone():
        return
    enviar_telegram(texto)
    con.execute("INSERT OR IGNORE INTO avisos VALUES(?,?)", (clave, dia))
    con.commit()


def ya_alertado(con, url, precio):
    return con.execute("SELECT 1 FROM alertas WHERE url=? AND precio=?",
                       (url, precio)).fetchone() is not None


def marcar_alerta(con, url, precio, nivel):
    con.execute("INSERT OR IGNORE INTO alertas VALUES(?,?,?,?)",
                (url, precio, nivel, datetime.now().isoformat(timespec="seconds")))

# ════════════════════════════════════════════════════════════════════
# Detección
# ════════════════════════════════════════════════════════════════════

def nombre_valido(nombre):
    n = nombre.lower()
    if any(w in n for w in PALABRAS_EXCLUIDAS):
        return False
    if PALABRAS_OBLIGATORIAS and not any(w.lower() in n for w in PALABRAS_OBLIGATORIAS):
        return False
    return True


def evaluar(p, hist, mediana_busqueda):
    """Devuelve (nivel, motivos) o (None, [])."""
    actual, normal = p["actual"], p["normal"]
    if normal < PRECIO_NORMAL_MINIMO or not nombre_valido(p["nombre"]):
        return None, []

    nivel, motivos = None, []
    rango = {"OFERTA": 1, "REVISAR": 2, "ERROR": 3}

    def subir(n):
        nonlocal nivel
        if nivel is None or rango[n] > rango[nivel]:
            nivel = n

    desc = 1 - actual / normal if normal > actual else 0
    if desc >= DESCUENTO_ERROR:
        subir("ERROR"); motivos.append(f"{desc:.0%} de descuento vs. precio normal")
    elif desc >= DESCUENTO_OFERTA:
        subir("OFERTA"); motivos.append(f"{desc:.0%} de descuento vs. precio normal")

    if len(hist) >= 3:
        med = statistics.median(hist)
        if actual <= med * (1 - CAIDA_HISTORICA_ERROR):
            subir("ERROR")
            motivos.append(f"cayó {1 - actual / med:.0%} bajo su precio habitual ({clp(int(med))})")

    if mediana_busqueda and actual < mediana_busqueda * ANOMALIA_VS_BUSQUEDA:
        subir("REVISAR")
        motivos.append(f"muy bajo vs. productos similares (mediana {clp(int(mediana_busqueda))})")

    return nivel, motivos


def alertar(con, tienda, p, nivel, motivos):
    if ya_alertado(con, p["url"], p["actual"]):
        return
    titulo = {"ERROR": "🚨 POSIBLE ERROR DE PRECIO",
              "REVISAR": "🔎 PRECIO SOSPECHOSO",
              "OFERTA": "🔥 OFERTA"}[nivel]
    desc = 1 - p["actual"] / p["normal"] if p["normal"] > p["actual"] else 0
    precio_txt = clp(p["actual"])
    if desc > 0:
        precio_txt += f" (antes {clp(p['normal'])}, -{desc:.0%})"
    msg = (f"<b>{titulo}</b>\n"
           f"🏬 {tienda}\n"
           f"📦 {html_escape(p['nombre'])}\n"
           f"💰 {precio_txt}\n"
           f"📌 {html_escape('; '.join(motivos))}\n"
           f"🔗 <a href=\"{p['url']}\">Ver producto</a>\n{p['url']}")
    enviado = enviar_telegram(msg)
    log(f"{titulo} | {tienda} | {p['nombre'][:60]} | {clp(p['actual'])} | {p['url']}"
        + ("" if enviado else "  (Telegram no configurado/falló)"))
    if nivel == "ERROR":
        beep()
    marcar_alerta(con, p["url"], p["actual"], nivel)

# ════════════════════════════════════════════════════════════════════
# Scraping
# ════════════════════════════════════════════════════════════════════

def extraer(page, url, patron):
    page.goto(url, wait_until="domcontentloaded", timeout=60000)
    page.wait_for_timeout(3500)
    for _ in range(7):                      # scroll para cargar productos "lazy"
        page.mouse.wheel(0, 2200)
        page.wait_for_timeout(700)
    crudos = page.evaluate(JS_EXTRAER, patron)
    productos = []
    for c in crudos:
        precios = sorted(set(c["precios"]))
        if not precios:
            continue
        productos.append({"url": c["url"], "nombre": c["nombre"],
                          "actual": precios[0], "normal": precios[-1]})
    return productos


def construir_urls():
    trabajos = []
    for tienda, cfg in TIENDAS.items():
        for t in TERMINOS:
            trabajos.append((tienda, cfg["busqueda"].format(q=quote_plus(t)), cfg["patron"]))
        for u in cfg.get("urls_extra", []):
            trabajos.append((tienda, u, cfg["patron"]))
    random.shuffle(trabajos)
    return trabajos


def ronda(con):
    trabajos = construir_urls()
    total = alertas = 0
    inicio = time.time()
    por_tienda = {t: 0 for t in TIENDAS}
    revisadas = set()
    with sync_playwright() as pw:
        browser = pw.chromium.launch(
            headless=HEADLESS, args=["--disable-blink-features=AutomationControlled"])
        ctx = browser.new_context(
            locale="es-CL", timezone_id="America/Santiago",
            viewport={"width": 1366, "height": 900},
            user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                        "(KHTML, like Gecko) Chrome/129.0 Safari/537.36"))
        page = ctx.new_page()
        for tienda, url, patron in trabajos:
            if MAX_SEGUNDOS_RONDA and time.time() - inicio > MAX_SEGUNDOS_RONDA:
                log("Tiempo de la ronda agotado; el resto se revisa en la próxima.")
                break
            revisadas.add(tienda)
            try:
                productos = extraer(page, url, patron)
            except Exception as e:
                log(f"⚠️  {tienda}: error en {url} -> {str(e)[:120]}")
                continue
            if not productos:
                log(f"⚠️  {tienda}: 0 productos en {url} (revisa URL o usa HEADLESS=False)")
            else:
                log(f"{tienda}: {len(productos)} productos en {url}")
            precios_busqueda = [p["actual"] for p in productos if p["normal"] >= PRECIO_NORMAL_MINIMO]
            mediana = statistics.median(precios_busqueda) if len(precios_busqueda) >= 8 else None
            for p in productos:
                hist = historial(con, p["url"])
                nivel, motivos = evaluar(p, hist, mediana)
                guardar_precio(con, p, tienda)
                if nivel:
                    alertar(con, tienda, p, nivel, motivos)
                    alertas += 1
            con.commit()
            total += len(productos)
            por_tienda[tienda] += len(productos)
            time.sleep(random.uniform(*PAUSA_ENTRE_PAGINAS))
        browser.close()
    log(f"Ronda terminada: {total} productos revisados, {alertas} detecciones.")
    for t in revisadas:
        if por_tienda[t] == 0:
            aviso_diario(con, f"bloqueo-{t}",
                         f"⚠️ {t} no entregó productos hoy (posible bloqueo o cambio en su web). "
                         f"Prueba agregando una URL de categoría en urls_extra.")
    if LATIDO_DIARIO and total:
        aviso_diario(con, "latido",
                     f"✅ Cazaofertas activo. Última ronda: {total} productos revisados.")

# ════════════════════════════════════════════════════════════════════
# Main
# ════════════════════════════════════════════════════════════════════

def main():
    ap = argparse.ArgumentParser(description="Cazaofertas Chile")
    ap.add_argument("--once", action="store_true", help="una sola ronda")
    ap.add_argument("--test", action="store_true", help="mensaje de prueba a Telegram")
    ap.add_argument("--chatid", action="store_true", help="mostrar tu chat_id de Telegram")
    a = ap.parse_args()

    if a.chatid:
        if not TELEGRAM_TOKEN:
            sys.exit("Primero pega tu TELEGRAM_TOKEN en el script.")
        r = requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates", timeout=20).json()
        ids = {u["message"]["chat"]["id"] for u in r.get("result", []) if "message" in u}
        print("Tu CHAT_ID:", ", ".join(map(str, ids)) if ids else
              "ninguno (escríbele algo a tu bot y vuelve a intentar)")
        return

    if a.test:
        ok = enviar_telegram("✅ Cazaofertas conectado. Te avisaré aquí las ofertas y errores de precio.")
        print("Mensaje enviado." if ok else "No se pudo enviar: revisa TOKEN y CHAT_ID.")
        return

    con = db_init()
    log("Cazaofertas iniciado. Ctrl+C para detener.")
    if not TELEGRAM_TOKEN:
        log("Telegram no configurado: las alertas solo se mostrarán en esta ventana.")
    while True:
        try:
            cargar_config(con)
            procesar_comandos(con)
            if not TELEGRAM_CHAT_ID and TELEGRAM_TOKEN:
                log("Esperando que le escribas 'hola' a tu bot de Telegram...")
            if cfg_get(con, "pausa") == "1":
                log("En pausa (/activar en Telegram para seguir).")
            else:
                ronda(con)
        except KeyboardInterrupt:
            break
        except Exception as e:
            log(f"Error en la ronda: {e}")
        if a.once:
            break
        espera = INTERVALO_MIN * 60 + random.randint(-60, 60)
        log(f"Próxima ronda en {espera // 60} min.")
        try:
            time.sleep(espera)
        except KeyboardInterrupt:
            break
    con.close()
    log("Detenido.")


if __name__ == "__main__":
    main()
