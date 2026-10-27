#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Simulador de Gravador (função POS) - par do Simulador de PDV
=============================================================
Recebe pela rede os dados enviados pelo Simulador de PDV e mostra, numa cena de
câmera simulada, a sobreposição (overlay) que um DVR/NVR Intelbras desenharia.

Pareamento de modos (gravador  <->  PDV):

  Gravador TCP          (escuta)    <->  PDV "TCP Cliente"   (conecta no gravador)
  Gravador TCP_CLIENT   (conecta)   <->  PDV "TCP Servidor"  (escuta)
  Gravador UDP          (escuta)    <->  PDV "UDP"

Requer apenas Python 3 padrão (tkinter incluso). Nenhuma dependência externa.
"""

import os
import sys
import json
import math
import queue
import socket
import threading
import time
import datetime
import ipaddress
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, scrolledtext, messagebox

# ============================================================ paleta ===
BG = "#050705"
BG_RAIL = "#090b09"
BG_PANEL = "#0a0d0b"
BG_FIELD = "#000000"
FG = "#d6ded8"
FG_DIM = "#5c655f"
FG_DIMMER = "#3c433e"
ACCENT = "#22e06a"
ACCENT_DIM = "#12472a"
ACCENT_SOFT = "#0c2618"
BORDER = "#1a1f1c"
DANGER = "#ef5350"
WARN = "#f5c542"
INFO = "#5aa7dd"
BTN_DARK = "#101312"
BTN_DARK_HOVER = "#171b19"

MONO = "Courier New"
FONT = (MONO, 10)
FONT_BOLD = (MONO, 10, "bold")
FONT_SMALL = (MONO, 9)
FONT_TINY = (MONO, 8)
FONT_TITLE = (MONO, 13, "bold")
FONT_SECTION = (MONO, 10, "bold")


def _init_fonts():
    global MONO, FONT, FONT_BOLD, FONT_SMALL, FONT_TINY, FONT_TITLE, FONT_SECTION
    try:
        families = set(tkfont.families())
    except Exception:
        families = set()
    for name in ("Cascadia Mono", "Cascadia Code", "Consolas", "JetBrains Mono", "Courier New"):
        if name in families:
            MONO = name
            break
    FONT = (MONO, 10)
    FONT_BOLD = (MONO, 10, "bold")
    FONT_SMALL = (MONO, 9)
    FONT_TINY = (MONO, 8)
    FONT_TITLE = (MONO, 13, "bold")
    FONT_SECTION = (MONO, 10, "bold")


# ============================================================ constantes ===
ENCODINGS = {"Unicode (UTF-8)": "utf-8", "Latin-1 (ISO-8859-1)": "latin-1", "ASCII": "ascii"}
PROTOCOLS = ["POS", "POSUTF8"]
MODES = {
    "TCP (aguardar o PDV conectar)": "TCP",
    "TCP_CLIENT (conectar no PDV)": "TCP_CLIENT",
    "UDP": "UDP",
}
MODE_LABELS = list(MODES.keys())
FONT_SIZES = {"Pequeno": 8, "Médio": 10, "Grande": 13}
OVERLAY_MODES = ["Página", "Lista"]
COLORS = ["#ffffff", "#ffee00", "#22e06a", "#5aa7dd", "#ff9f43", "#ef5350", "#c792ea", "#9aa5a0"]

OVL_X, OVL_Y, OVL_W, OVL_H = 12, 34, 300, 290   # caixa lógica do overlay (px)
FLUSH_IDLE = 0.4          # s sem dados antes de exibir uma linha sem terminador
MAX_LOG_CHARS = 60000

DEFAULT_CFG = {
    "modo": "TCP",
    "ip": "0.0.0.0",
    "porta": 9000,
    "ip_origem": "",
    "protocolo": "POS",
    "converter": "Unicode (UTF-8)",
    "quebra": "",                       # vazio = automático (CRLF, LF ou CR)
    "privacy": ["", "", ""],
    "sinal": "Muito Obrigado!",
    "timeout": 30,                      # s sem dados => próxima venda começa limpa (0 = desliga)
    "display": 10,                      # s de exibição após o último dado (0 = fixo)
    "fonte": "Médio",
    "sobrepor": "Página",
    "cor": "#ffffff",
}


def cfg_path():
    env = os.environ.get("SIMULADOR_GRAVADOR_CONFIG")
    if env:
        return env
    base = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) \
        else os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "gravador_config.json")


def diagnosticar_erro(exc):
    """Traduz uma exceção de rede em (título, solução sugerida)."""
    low = str(exc).lower()
    if isinstance(exc, PermissionError) or "permission" in low or "acesso negado" in low:
        return ("Sem permissão para usar essa porta.",
                "Portas abaixo de 1024 exigem administrador. Use uma porta acima de 1024.")
    if "address already in use" in low or "only one usage" in low or "10048" in low:
        return ("Essa porta já está em uso.",
                "Feche a outra instância (ou programa) que usa a porta, ou escolha outra.")
    if "cannot assign requested address" in low or "10049" in low:
        return ("Esse IP não pertence a este computador.",
                "Para escutar, use 0.0.0.0 ou o IP de uma placa de rede desta máquina.")
    if isinstance(exc, socket.timeout) or "timed out" in low:
        return ("O PDV não respondeu a tempo.",
                "Confira IP, porta e se o modo bate (gravador TCP_CLIENT -> PDV TCP Servidor; "
                "gravador TCP -> PDV TCP Cliente).")
    if "refused" in low or "recusad" in low or "10061" in low:
        return ("Conexão recusada pelo PDV.",
                "Nada escuta nesse IP/porta. Ative o Habilitar no PDV (modo TCP Servidor) primeiro.")
    if "unreachable" in low or "no route" in low or "host is down" in low:
        return ("Rede inacessível.", "Confira se os equipamentos estão na mesma rede e o firewall.")
    return (f"Falha na comunicação: {exc}", "Revise IP, porta e modo de conexão.")


# ============================================================ widgets ===
class ToggleSwitch(tk.Canvas):
    def __init__(self, parent, command=None, value=False, width=46, height=20, bg=BG_PANEL):
        super().__init__(parent, width=width, height=height, bg=bg,
                         highlightthickness=0, cursor="hand2")
        self.command, self.value, self.width, self.height = command, value, width, height
        self.bind("<Button-1>", lambda e: self.set(not self.value, fire=True))
        self._draw()

    def _draw(self):
        self.delete("all")
        on = self.value
        self.create_rectangle(0, 0, self.width, self.height, fill=ACCENT_DIM if on else "#1c211e",
                              outline=ACCENT if on else BORDER)
        kw = self.width // 2 - 2
        x0 = self.width - kw - 2 if on else 2
        col = ACCENT if on else FG_DIM
        self.create_rectangle(x0, 2, x0 + kw, self.height - 2, fill=col, outline=col)
        self.create_text(self.width * (0.27 if on else 0.73), self.height / 2,
                         text="ON" if on else "OFF", fill="#04140a" if on else FG_DIM,
                         font=(MONO, 7, "bold"))

    def set(self, val, fire=False):
        self.value = bool(val)
        self._draw()
        if fire and self.command:
            self.command(self.value)

    def get(self):
        return self.value


def make_button(parent, text, command, primary=False, width=None):
    bg, fg, hover, border = ((ACCENT, "#04140a", "#3dfb8c", ACCENT) if primary
                             else (BTN_DARK, FG, BTN_DARK_HOVER, BORDER))
    btn = tk.Button(parent, text=f"[ {text} ]", command=command, bg=bg, fg=fg,
                    activebackground=hover, activeforeground=fg, relief="flat", bd=0,
                    padx=12, pady=6, font=FONT, cursor="hand2", width=width,
                    highlightthickness=1, highlightbackground=border, highlightcolor=border)
    btn.bind("<Enter>", lambda e: btn.config(bg=hover))
    btn.bind("<Leave>", lambda e: btn.config(bg=bg))
    return btn


def panel(parent, title, desc=None):
    wrap = tk.Frame(parent, bg=BG_PANEL, highlightthickness=1,
                    highlightbackground=BORDER, highlightcolor=BORDER)
    head = tk.Frame(wrap, bg=BG_PANEL)
    head.pack(fill="x", padx=14, pady=(12, 3 if desc else 8))
    tk.Frame(head, bg=ACCENT, width=3, height=14).pack(side="left", padx=(0, 8))
    tk.Label(head, text=title.upper(), bg=BG_PANEL, fg=FG, font=FONT_SECTION).pack(side="left")
    if desc:
        tk.Label(wrap, text=desc, bg=BG_PANEL, fg=FG_DIM, font=FONT_TINY, anchor="w",
                 justify="left", wraplength=360).pack(fill="x", padx=14, pady=(0, 8))
    body = tk.Frame(wrap, bg=BG_PANEL)
    body.pack(fill="both", expand=True, padx=14, pady=(0, 12))
    return wrap, body


# ============================================================ aplicação ===
class GravadorSimulator:
    def __init__(self, root):
        _init_fonts()
        self.root = root
        self.root.title("Simulador de Gravador - POS Overlay (Intelbras)")
        self.root.configure(bg=BG)
        self.root.geometry("1240x800")
        self.root.minsize(1100, 740)

        self.cfg = self._load_cfg()
        self.q = queue.Queue()
        self.stop_evt = threading.Event()
        self.net_thread = None
        self.fonts = {}

        # estado do pipeline
        self.txn_lines = []
        self.rx_buf = b""
        self.last_data_mono = None
        self.view_page = None
        self.txn_done = False
        self._warned_flush = False
        self._last_bad_warn = 0
        self.stat_packets = self.stat_bytes = self.stat_lines = 0

        self._setup_style()
        self._build_ui()
        self._load_ui_from_cfg()
        self._log("Simulador de gravador pronto. Ajuste a conexão e ative o Habilitar.")
        self._loop()

    # --------------------------------------------------------- config ---
    def _load_cfg(self):
        cfg = json.loads(json.dumps(DEFAULT_CFG))
        try:
            with open(cfg_path(), encoding="utf-8") as f:
                saved = json.load(f)
            for k in DEFAULT_CFG:
                if k in saved:
                    cfg[k] = saved[k]
        except Exception:
            pass
        return cfg

    def _save_cfg(self):
        try:
            with open(cfg_path(), "w", encoding="utf-8") as f:
                json.dump(self.cfg, f, ensure_ascii=False, indent=2)
        except Exception as e:
            self._log(f"⚠ Não foi possível salvar a configuração: {e}")

    # ---------------------------------------------------------- estilo ---
    def _setup_style(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except Exception:
            pass
        st.configure("TLabel", background=BG_PANEL, foreground=FG, font=FONT)
        st.configure("Dim.TLabel", background=BG_PANEL, foreground=FG_DIM, font=FONT_SMALL)
        for w in ("TCombobox", "TEntry", "TSpinbox"):
            st.configure(w, fieldbackground=BG_FIELD, background=BG_FIELD, foreground=FG,
                         insertcolor=ACCENT, arrowcolor=FG_DIM, bordercolor=BORDER,
                         lightcolor=BORDER, darkcolor=BORDER, borderwidth=1, font=FONT)
            st.map(w, bordercolor=[("focus", ACCENT)], lightcolor=[("focus", ACCENT)],
                   darkcolor=[("focus", ACCENT)], arrowcolor=[("focus", ACCENT)])
        st.map("TCombobox", fieldbackground=[("readonly", BG_FIELD)],
               selectbackground=[("readonly", BG_FIELD)], selectforeground=[("readonly", FG)])
        self.root.option_add("*TCombobox*Listbox.background", BG_FIELD)
        self.root.option_add("*TCombobox*Listbox.foreground", FG)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT_DIM)
        self.root.option_add("*TCombobox*Listbox.selectForeground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.font", FONT)

    # ------------------------------------------------------------- UI ---
    def _build_ui(self):
        bar = tk.Frame(self.root, bg=BG_RAIL, height=40)
        bar.pack(fill="x")
        bar.pack_propagate(False)
        tk.Label(bar, text="simulador_gravador", bg=BG_RAIL, fg=FG, font=FONT_TITLE).pack(side="left", padx=(14, 0))
        self.cursor_lbl = tk.Label(bar, text="▌", bg=BG_RAIL, fg=ACCENT, font=FONT_TITLE)
        self.cursor_lbl.pack(side="left")
        tk.Label(bar, text="  pos overlay · par do simulador_pdv", bg=BG_RAIL, fg=FG_DIM,
                 font=FONT_TINY).pack(side="left", padx=(10, 0))
        self.clock_var = tk.StringVar(value="--:--:--")
        tk.Label(bar, textvariable=self.clock_var, bg=BG_RAIL, fg=FG_DIMMER,
                 font=FONT_SMALL).pack(side="right", padx=14)
        sb = tk.Frame(bar, bg="#000000", highlightthickness=1, highlightbackground=BORDER)
        sb.pack(side="right")
        inner = tk.Frame(sb, bg="#000000")
        inner.pack(padx=10, pady=4)
        self.status_dot = tk.Label(inner, text="●", bg="#000000", fg=DANGER, font=FONT_SMALL)
        self.status_dot.pack(side="left", padx=(0, 6))
        self.status_var = tk.StringVar(value="DESABILITADO")
        self.status_lbl = tk.Label(inner, textvariable=self.status_var, bg="#000000", fg=DANGER, font=FONT_BOLD)
        self.status_lbl.pack(side="left")
        tk.Frame(self.root, bg=BORDER, height=1).pack(fill="x")

        body = tk.Frame(self.root, bg=BG)
        body.pack(fill="both", expand=True)
        left = tk.Frame(body, bg=BG, width=410)
        left.pack(side="left", fill="y", padx=(14, 8), pady=12)
        left.pack_propagate(False)
        right = tk.Frame(body, bg=BG)
        right.pack(side="left", fill="both", expand=True, padx=(0, 14), pady=12)

        self._build_left(left)
        self._build_right(right)

    def _lbl(self, parent, text, r, c, span=1):
        ttk.Label(parent, text=text, style="Dim.TLabel").grid(row=r, column=c, columnspan=span, sticky="w")

    def _combo(self, parent, var, values, r, c, span=1, last=False):
        cb = ttk.Combobox(parent, textvariable=var, values=values, state="readonly")
        cb.grid(row=r, column=c, columnspan=span, sticky="we", pady=(2, 8), padx=(0, 0 if last or span > 1 else 6))
        return cb

    def _entry(self, parent, var, r, c, span=1, last=False, spin=None):
        if spin:
            e = ttk.Spinbox(parent, from_=spin[0], to=spin[1], textvariable=var, width=6)
        else:
            e = ttk.Entry(parent, textvariable=var)
        e.grid(row=r, column=c, columnspan=span, sticky="we", pady=(2, 8), padx=(0, 0 if last or span > 1 else 6))
        return e

    def _build_left(self, left):
        # ---- conexão ----
        w, f = panel(left, "conexao_de_rede")
        w.pack(fill="x", pady=(0, 10))
        top = tk.Frame(f, bg=BG_PANEL)
        top.pack(fill="x", pady=(0, 8))
        tk.Label(top, text="habilitar", bg=BG_PANEL, fg=FG, font=FONT_BOLD).pack(side="left")
        self.enable_toggle = ToggleSwitch(top, command=self._on_toggle_enable)
        self.enable_toggle.pack(side="left", padx=(14, 0))
        g = tk.Frame(f, bg=BG_PANEL)
        g.pack(fill="x")
        g.grid_columnconfigure(0, weight=1)
        g.grid_columnconfigure(1, weight=1)
        self.v_modo = tk.StringVar()
        self._lbl(g, "modo_de_conexao", 0, 0, 2)
        cb = self._combo(g, self.v_modo, MODE_LABELS, 1, 0, span=2)
        cb.bind("<<ComboboxSelected>>", lambda e: self._on_mode_change())
        self.ip_lbl = ttk.Label(g, text="ip_de_escuta", style="Dim.TLabel")
        self.ip_lbl.grid(row=2, column=0, sticky="w")
        self.v_ip = tk.StringVar()
        self._entry(g, self.v_ip, 3, 0)
        self._lbl(g, "porta", 2, 1)
        self.v_porta = tk.StringVar()
        self._entry(g, self.v_porta, 3, 1, last=True)
        self._lbl(g, "filtrar_ip_origem (opcional)", 4, 0, 2)
        self.v_ip_origem = tk.StringVar()
        self._entry(g, self.v_ip_origem, 5, 0, span=2)

        # ---- POS ----
        w, f = panel(left, "pos_overlay")
        w.pack(fill="x")
        g = tk.Frame(f, bg=BG_PANEL)
        g.pack(fill="x")
        g.grid_columnconfigure(0, weight=1)
        g.grid_columnconfigure(1, weight=1)
        self.v_protocolo, self.v_converter = tk.StringVar(), tk.StringVar()
        self._lbl(g, "protocolo", 0, 0)
        self._combo(g, self.v_protocolo, PROTOCOLS, 1, 0)
        self._lbl(g, "converter", 0, 1)
        self._combo(g, self.v_converter, list(ENCODINGS), 1, 1, last=True)
        self.v_quebra, self.v_sinal = tk.StringVar(), tk.StringVar()
        self._lbl(g, "quebra_de_linha (auto)", 2, 0)
        self._entry(g, self.v_quebra, 3, 0)
        self._lbl(g, "sinal_final_de_pdv", 2, 1)
        self._entry(g, self.v_sinal, 3, 1, last=True)
        self._lbl(g, "privacidade (mascara o texto depois da palavra)", 4, 0, 2)
        pr = tk.Frame(g, bg=BG_PANEL)
        pr.grid(row=5, column=0, columnspan=2, sticky="we", pady=(2, 8))
        self.v_priv = [tk.StringVar() for _ in range(3)]
        for i, v in enumerate(self.v_priv):
            pr.grid_columnconfigure(i, weight=1)
            ttk.Entry(pr, textvariable=v, width=8).grid(row=0, column=i, sticky="we", padx=(0, 6 if i < 2 else 0))
        self.v_timeout, self.v_display = tk.StringVar(), tk.StringVar()
        self._lbl(g, "tempo_limite (s)", 6, 0)
        self._entry(g, self.v_timeout, 7, 0, spin=(0, 3600))
        self._lbl(g, "tempo_de_exibicao (s)", 6, 1)
        self._entry(g, self.v_display, 7, 1, last=True, spin=(0, 3600))
        self.v_fonte, self.v_sobrepor = tk.StringVar(), tk.StringVar()
        self._lbl(g, "fonte", 8, 0)
        self._combo(g, self.v_fonte, list(FONT_SIZES), 9, 0)
        self._lbl(g, "sobrepor", 8, 1)
        self._combo(g, self.v_sobrepor, OVERLAY_MODES, 9, 1, last=True)
        self._lbl(g, "cor_do_texto", 10, 0, 2)
        self.v_cor = tk.StringVar(value=DEFAULT_CFG["cor"])
        self.swatches = tk.Canvas(g, width=len(COLORS) * 22, height=22, bg=BG_PANEL, highlightthickness=0,
                                  cursor="hand2")
        self.swatches.grid(row=11, column=0, columnspan=2, sticky="w", pady=(2, 8))
        self.swatches.bind("<Button-1>", self._pick_color)
        self._draw_swatches()
        btns = tk.Frame(f, bg=BG_PANEL)
        btns.pack(fill="x", pady=(4, 0))
        make_button(btns, "Aplicar", self._apply, primary=True).pack(side="left")
        make_button(btns, "Limpar tela", self._clear_screen).pack(side="left", padx=(8, 0))

    def _build_right(self, right):
        w, f = panel(right, "cena_da_camera (preview do overlay)")
        w.pack(fill="x", pady=(0, 10))
        self.scene = tk.Canvas(f, height=340, bg="#0b0f0c", highlightthickness=1,
                               highlightbackground=BORDER)
        self.scene.pack(fill="x")
        self.scene.bind("<Configure>", lambda e: self._draw())
        nav = tk.Frame(f, bg=BG_PANEL)
        nav.pack(fill="x", pady=(8, 0))
        make_button(nav, "◀", self._page_prev).pack(side="left")
        self.nav_var = tk.StringVar(value="sem dados")
        tk.Label(nav, textvariable=self.nav_var, bg=BG_PANEL, fg=FG, font=FONT, width=13).pack(side="left", padx=6)
        make_button(nav, "▶", self._page_next).pack(side="left")
        self.s_pk, self.s_ln, self.s_last = tk.StringVar(value="0"), tk.StringVar(value="0"), tk.StringVar(value="—")
        for label, var in (("Pacotes", self.s_pk), ("Linhas", self.s_ln), ("Último", self.s_last)):
            b = tk.Frame(nav, bg=BG_PANEL)
            b.pack(side="right", padx=(14, 0))
            tk.Label(b, text=label.lower() + " ", bg=BG_PANEL, fg=FG_DIM, font=FONT_TINY).pack(side="left")
            tk.Label(b, textvariable=var, bg=BG_PANEL, fg=ACCENT, font=FONT_BOLD).pack(side="left")

        w, f = panel(right, "log_de_eventos")
        w.pack(fill="both", expand=True)
        self.log_text = scrolledtext.ScrolledText(f, height=8, bg=BG_FIELD, fg=FG, font=FONT_SMALL,
                                                  borderwidth=0, highlightthickness=1,
                                                  highlightbackground=BORDER, state="disabled", wrap="word")
        self.log_text.pack(fill="both", expand=True)
        for tag, col in (("err", DANGER), ("ok", ACCENT), ("info", INFO), ("warn", WARN)):
            self.log_text.tag_configure(tag, foreground=col)

    # --------------------------------------------------- cores / cfg <-> UI ---
    def _draw_swatches(self):
        c = self.swatches
        c.delete("all")
        for i, col in enumerate(COLORS):
            sel = col == self.v_cor.get()
            x = i * 22
            c.create_rectangle(x + 1, 2, x + 17, 18, fill=col, outline=ACCENT if sel else BORDER, width=2)
            if sel:
                c.create_text(x + 9, 10, text="✓", fill="#111111" if col in ("#ffffff", "#ffee00") else "#ffffff",
                              font=(MONO, 8, "bold"))

    def _pick_color(self, event):
        i = event.x // 22
        if 0 <= i < len(COLORS):
            self.v_cor.set(COLORS[i])
            self._draw_swatches()

    def _load_ui_from_cfg(self):
        c = self.cfg
        self.v_modo.set(next((k for k, v in MODES.items() if v == c["modo"]), MODE_LABELS[0]))
        self.v_ip.set(c["ip"])
        self.v_porta.set(str(c["porta"]))
        self.v_ip_origem.set(c["ip_origem"])
        self.v_protocolo.set(c["protocolo"])
        self.v_converter.set(c["converter"])
        self.v_quebra.set(c["quebra"])
        self.v_sinal.set(c["sinal"])
        for v, t in zip(self.v_priv, list(c["privacy"]) + [""] * 3):
            v.set(t)
        self.v_timeout.set(str(c["timeout"]))
        self.v_display.set(str(c["display"]))
        self.v_fonte.set(c["fonte"])
        self.v_sobrepor.set(c["sobrepor"])
        self.v_cor.set(c["cor"])
        self._draw_swatches()
        self._on_mode_change()

    def _collect_ui(self, strict=False):
        """Lê a interface e devolve um dict de configuração. Com strict=True,
        levanta ValueError (mensagem em português) se algo estiver inválido."""
        def bad(msg):
            if strict:
                raise ValueError(msg)
        c = dict(self.cfg)
        c["modo"] = MODES.get(self.v_modo.get(), "TCP")
        ip = self.v_ip.get().strip()
        try:
            ipaddress.ip_address(ip)
            c["ip"] = ip
        except ValueError:
            bad("IP inválido. Use o formato 192.168.0.10 (ou 0.0.0.0 para escutar em todas as placas).")
        try:
            porta = int(self.v_porta.get().strip())
            if not 1 <= porta <= 65535:
                raise ValueError
            c["porta"] = porta
        except ValueError:
            bad("Porta inválida. Use um número entre 1 e 65535.")
        org = self.v_ip_origem.get().strip()
        if org:
            try:
                ipaddress.ip_address(org)
            except ValueError:
                bad("IP de origem inválido (deixe vazio para aceitar qualquer origem).")
                org = ""
        c["ip_origem"] = org
        c["protocolo"] = self.v_protocolo.get() or "POS"
        c["converter"] = self.v_converter.get() or "Unicode (UTF-8)"
        c["quebra"] = self.v_quebra.get()
        c["sinal"] = self.v_sinal.get()
        c["privacy"] = [v.get().strip() for v in self.v_priv]
        for key, var, nome in (("timeout", self.v_timeout, "Tempo limite"),
                               ("display", self.v_display, "Tempo de exibição")):
            try:
                n = int(var.get().strip())
                if n < 0:
                    raise ValueError
                c[key] = n
            except ValueError:
                bad(f"{nome} inválido. Use segundos inteiros (0 = desligado).")
        c["fonte"] = self.v_fonte.get() or "Médio"
        c["sobrepor"] = self.v_sobrepor.get() or "Página"
        c["cor"] = self.v_cor.get() or "#ffffff"
        return c

    def _on_mode_change(self):
        escuta = MODES.get(self.v_modo.get(), "TCP") != "TCP_CLIENT"
        self.ip_lbl.config(text="ip_de_escuta" if escuta else "ip_do_pdv")

    def _apply(self):
        try:
            self.cfg = self._collect_ui(strict=True)
        except ValueError as e:
            messagebox.showerror("Configuração inválida", str(e))
            return False
        self._save_cfg()
        self._log("Configuração aplicada.")
        if self.enable_toggle.get():
            self._start_net()
        self._draw()
        return True

    def _clear_screen(self):
        self.txn_lines, self.rx_buf, self.view_page, self.txn_done = [], b"", None, False
        self._draw()

    # ----------------------------------------------------------- log/status ---
    def _log(self, msg):
        tag = "err" if msg.startswith("⚠") else "ok" if ("conectou" in msg.lower() or "escutando" in msg.lower()
                                                            or msg.startswith("Conectado")) else "info"
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        t = self.log_text
        t.configure(state="normal")
        t.insert("end", f"[{ts}] {msg}\n", tag)
        if len(t.get("1.0", "end")) > MAX_LOG_CHARS:
            t.delete("1.0", "50.0")
        t.see("end")
        t.configure(state="disabled")

    def _set_status(self, text, level):
        col = {"ok": ACCENT, "wait": WARN, "off": DANGER}[level]
        self.status_var.set(text.upper())
        self.status_lbl.configure(fg=col)
        self.status_dot.configure(fg=col)

    # ============================================== pipeline de dados ===
    @staticmethod
    def _unescape(s):
        return s.replace("\\r", "\r").replace("\\n", "\n").replace("\\t", "\t")

    def _sep(self):
        q = self._unescape(self.cfg.get("quebra") or "")
        return q.encode("latin-1", errors="replace") if q else None

    def _encoding(self):
        if self.cfg.get("protocolo") == "POSUTF8":
            return "utf-8"
        return ENCODINGS.get(self.cfg.get("converter"), "utf-8")

    def _mask(self, line):
        for kw in self.cfg.get("privacy") or []:
            kw = (kw or "").strip()
            if not kw:
                continue
            i = line.upper().find(kw.upper())
            if i >= 0:
                j = i + len(kw)
                line = line[:j] + "".join(ch if ch == " " else "*" for ch in line[j:])
        return line

    def _on_data(self, data, src="?"):
        now = time.monotonic()
        tmo = int(self.cfg.get("timeout") or 0)
        if self.txn_done or (tmo > 0 and self.last_data_mono is not None
                             and now - self.last_data_mono > tmo):
            self.txn_lines, self.rx_buf, self.txn_done = [], b"", False
        self.last_data_mono = now
        self.view_page = None
        self.stat_packets += 1
        self.stat_bytes += len(data)
        self.rx_buf += data
        self._extract_lines()
        self.s_last.set(datetime.datetime.now().strftime("%H:%M:%S"))
        self._after_change()

    def _extract_lines(self):
        buf, out, sep = self.rx_buf, [], self._sep()
        if sep:
            parts = buf.split(sep)
            self.rx_buf = parts.pop()
            out = parts
        else:                                   # automático: CRLF, LF ou CR
            i = start = 0
            n = len(buf)
            while i < n:
                b = buf[i]
                if b == 10:
                    out.append(buf[start:i])
                    i += 1
                    start = i
                elif b == 13:
                    if i + 1 >= n:              # CR no fim: talvez o LF venha no próximo pacote
                        break
                    out.append(buf[start:i])
                    i += 2 if buf[i + 1] == 10 else 1
                    start = i
                else:
                    i += 1
            self.rx_buf = buf[start:]
        for raw in out:
            self._add_line(raw)

    def _add_line(self, raw):
        text = raw.decode(self._encoding(), errors="replace")
        if "\ufffd" in text and time.monotonic() - self._last_bad_warn > 5:
            self._last_bad_warn = time.monotonic()
            self._log("⚠ Caracteres inválidos na decodificação. O PDV e o campo Converter "
                      "precisam usar a mesma codificação (ou use o protocolo POSUTF8).")
        text = "".join("    " if ch == "\t" else ch if ch >= " " else "·" for ch in text)
        text = self._mask(text)
        self.txn_lines.append(text)
        self.stat_lines += 1
        sinal = (self.cfg.get("sinal") or "").strip()
        if sinal and text.strip() == sinal:
            self.txn_done = True

    def _flush_idle(self):
        raw, self.rx_buf = self.rx_buf, b""
        terminated = False
        if not self._sep() and raw.endswith(b"\r"):
            raw, terminated = raw[:-1], True
        if raw and not terminated and not self._warned_flush:
            self._warned_flush = True
            self._log("⚠ Dados sem terminador de linha: exibindo a última linha por ociosidade. "
                      "Confira o terminador no PDV e a Quebra de linha aqui.")
        if raw:
            self._add_line(raw)
        self._after_change()

    # ---------------------------------------------- paginação / overlay ---
    def _font_for(self, name):
        size = FONT_SIZES.get(name, 10)
        if size not in self.fonts:
            self.fonts[size] = tkfont.Font(family=MONO, size=size)
        return self.fonts[size]

    @staticmethod
    def _wrap(line, f, maxw):
        if not line:
            return [""]
        rows, cur = [], ""
        for word in line.split(" "):
            cand = word if not cur else cur + " " + word
            if f.measure(cand) <= maxw:
                cur = cand
                continue
            if cur:
                rows.append(cur)
                cur = ""
            while f.measure(word) > maxw and len(word) > 1:     # palavra maior que a caixa
                k = len(word)
                while k > 1 and f.measure(word[:k]) > maxw:
                    k -= 1
                rows.append(word[:k])
                word = word[k:]
            cur = word
        rows.append(cur)
        return rows

    def _overlay_rows(self):
        f = self._font_for(self.cfg.get("fonte"))
        lh = f.metrics("linespace") + 2
        rows = []
        for line in self.txn_lines:
            rows += self._wrap(line, f, OVL_W - 16)
        cap = max(1, (OVL_H - 12) // lh)
        return f, rows, lh, cap

    def _page_info(self):
        _, rows, _, cap = self._overlay_rows()
        if self.cfg.get("sobrepor") == "Lista":
            return rows[-cap:], 0, 1
        n = max(1, math.ceil(len(rows) / cap))
        idx = n - 1 if self.view_page is None else min(self.view_page, n - 1)
        return rows[idx * cap:(idx + 1) * cap], idx, n

    def _page_prev(self):
        _, idx, _ = self._page_info()
        self.view_page = max(0, idx - 1)
        self._draw()

    def _page_next(self):
        _, idx, n = self._page_info()
        self.view_page = None if idx + 1 >= n - 1 else idx + 1
        self._draw()

    def _after_change(self):
        self.s_pk.set(str(self.stat_packets))
        self.s_ln.set(str(self.stat_lines))
        self._draw()

    # ------------------------------------------------------------ cena ---
    def _draw(self):
        c = self.scene
        c.delete("all")
        w, h = c.winfo_width(), c.winfo_height()
        if w < 50 or h < 50:
            w, h = 700, 340
        c.create_rectangle(0, 0, w, h, fill="#0b0f0c", outline="")
        c.create_rectangle(0, int(h * 0.74), w, h, fill="#111612", outline="")
        for k in range(4):                                       # prateleiras
            x = w * 0.42 + k * w * 0.14
            c.create_rectangle(x, h * 0.18, x + w * 0.11, h * 0.74, fill="#141a15", outline="#1f2a22")
            for s in range(1, 4):
                y = h * 0.18 + s * (h * 0.56 / 4)
                c.create_line(x, y, x + w * 0.11, y, fill="#1f2a22")
        c.create_text(w - 12, 10, anchor="ne", fill="#cfd8d1", font=FONT_SMALL,
                      text=datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
        c.create_text(w - 12, h - 8, anchor="se", fill="#7d8a80", font=FONT_SMALL, text="CAM 01 | CAIXA")
        c.create_text(12, 10, anchor="nw", fill="#ef5350", font=FONT_SMALL, text="● REC")
        vis, idx, n = self._page_info() if self.txn_lines else ([], 0, 1)
        if self.txn_lines:
            f, _, lh, _ = self._overlay_rows()
            c.create_rectangle(OVL_X, OVL_Y, OVL_X + OVL_W, OVL_Y + OVL_H, fill="#000000",
                               stipple="gray75", outline="")
            for i, row in enumerate(vis):
                c.create_text(OVL_X + 8, OVL_Y + 6 + i * lh, anchor="nw", text=row, font=f,
                              fill=self.cfg.get("cor", "#ffffff"))
            self.nav_var.set("lista" if self.cfg.get("sobrepor") == "Lista" else f"pág {idx + 1}/{n}")
        else:
            self.nav_var.set("sem dados")

    # --------------------------------------------------------- relógio/tick ---
    def _loop(self):
        self._tick()
        self.root.after(100, self._loop)

    def _tick(self):
        self._poll_queue()
        now = time.monotonic()
        if self.rx_buf and self.last_data_mono is not None and now - self.last_data_mono > FLUSH_IDLE:
            self._flush_idle()
        disp = int(self.cfg.get("display") or 0)
        if self.txn_lines and disp > 0 and self.last_data_mono is not None and now - self.last_data_mono > disp:
            self.txn_lines, self.view_page, self.txn_done = [], None, False
            self._draw()
        s = int(now) % 2
        self.cursor_lbl.configure(text="▌" if s else " ")
        t = datetime.datetime.now().strftime("%H:%M:%S")
        if t != self.clock_var.get():
            self.clock_var.set(t)
            if self.txn_lines:
                self._draw()                                     # mantém o relógio da cena vivo

    def _poll_queue(self):
        while True:
            try:
                item = self.q.get_nowait()
            except queue.Empty:
                break
            k = item[0]
            if k == "data":
                self._on_data(item[1], item[2])
            elif k == "log":
                self._log(item[1])
            elif k == "status":
                self._set_status(item[1], item[2])
            elif k == "fatal":
                self._log(f"⚠ {item[1]} {item[2]}")
                self._set_status("Erro", "off")
                self.enable_toggle.set(False)
                self._stop_net(silent=True)
                messagebox.showerror(item[1], item[2])

    # =================================================== rede (threads) ===
    def _on_toggle_enable(self, value):
        if not value:
            self._stop_net()
            return
        try:
            self.cfg = self._collect_ui(strict=True)
        except ValueError as e:
            messagebox.showerror("Configuração inválida", str(e))
            self.enable_toggle.set(False)
            return
        self._save_cfg()
        self._start_net()

    def _start_net(self):
        self._stop_net(silent=True)
        c = self.cfg
        self.stop_evt = threading.Event()
        target = {"TCP": self._run_tcp, "TCP_CLIENT": self._run_tcp_client, "UDP": self._run_udp}[c["modo"]]
        self.net_thread = threading.Thread(
            target=target, args=(c["ip"], int(c["porta"]), c.get("ip_origem", "").strip(), self.stop_evt),
            daemon=True)
        self.net_thread.start()

    def _stop_net(self, silent=False):
        self.stop_evt.set()
        t = self.net_thread
        if t and t.is_alive() and t is not threading.current_thread():
            t.join(1.5)
        self.net_thread = None
        keep = []                                   # descarta status velhos da thread que parou
        while True:
            try:
                item = self.q.get_nowait()
            except queue.Empty:
                break
            if item[0] in ("data", "log"):
                keep.append(item)
        for item in keep:
            self.q.put(item)
        if not silent:
            self._set_status("Desabilitado", "off")
            self._log("Recepção desabilitada.")

    def _recv_loop(self, conn, src_ip, flt, stop):
        conn.settimeout(0.5)
        try:
            while not stop.is_set():
                try:
                    data = conn.recv(4096)
                except socket.timeout:
                    continue
                if not data:
                    return False
                if flt and src_ip != flt:
                    continue
                self.q.put(("data", data, src_ip))
        except OSError:
            return False
        finally:
            try:
                conn.close()
            except Exception:
                pass
        return True

    def _run_tcp(self, ip, port, flt, stop):
        srv = None
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            srv.bind((ip, port))
            srv.listen(1)
            srv.settimeout(0.5)
            self.q.put(("status", f"Escutando {ip}:{port}", "wait"))
            self.q.put(("log", f"Gravador TCP escutando em {ip}:{port}"))
            while not stop.is_set():
                try:
                    conn, addr = srv.accept()
                except socket.timeout:
                    continue
                self.q.put(("status", f"PDV conectado: {addr[0]}", "ok"))
                self.q.put(("log", f"PDV conectou de {addr[0]}:{addr[1]}"))
                self._recv_loop(conn, addr[0], flt, stop)
                if not stop.is_set():
                    self.q.put(("status", f"Escutando {ip}:{port}", "wait"))
                    self.q.put(("log", "PDV desconectou. Aguardando nova conexão."))
        except Exception as e:
            self.q.put(("fatal",) + diagnosticar_erro(e))
        finally:
            if srv:
                srv.close()

    def _run_tcp_client(self, ip, port, flt, stop):
        last_err = None
        while not stop.is_set():
            self.q.put(("status", f"Conectando {ip}:{port}", "wait"))
            try:
                s = socket.create_connection((ip, port), timeout=3)
            except Exception as e:
                titulo, solucao = diagnosticar_erro(e)
                if titulo != last_err:
                    last_err = titulo
                    self.q.put(("log", f"⚠ {titulo} {solucao} Tentando de novo a cada 3 s."))
                self.q.put(("status", "Sem conexão (reconectando)", "off"))
                stop.wait(3)
                continue
            last_err = None
            self.q.put(("status", f"Conectado ao PDV {ip}:{port}", "ok"))
            self.q.put(("log", f"Conectado ao PDV em {ip}:{port}"))
            self._recv_loop(s, ip, flt, stop)
            if not stop.is_set():
                self.q.put(("log", "⚠ Conexão com o PDV encerrada. Reconectando..."))
                stop.wait(1)

    def _run_udp(self, ip, port, flt, stop):
        s = None
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind((ip, port))
            s.settimeout(0.5)
            self.q.put(("status", f"UDP escutando {ip}:{port}", "ok"))
            self.q.put(("log", f"Gravador UDP escutando em {ip}:{port}"))
            while not stop.is_set():
                try:
                    data, addr = s.recvfrom(65535)
                except socket.timeout:
                    continue
                if flt and addr[0] != flt:
                    continue
                self.q.put(("data", data, addr[0]))
        except Exception as e:
            self.q.put(("fatal",) + diagnosticar_erro(e))
        finally:
            if s:
                s.close()


def main():
    root = tk.Tk()
    app = GravadorSimulator(root)

    def on_close():
        app._stop_net(silent=True)
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()


if __name__ == "__main__":
    main()
