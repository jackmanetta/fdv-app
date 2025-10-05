# -*- coding: utf-8 -*-
# FDV – Foglio di Viaggio (Kivy + pyfpdf + plyer)

from kivy.app import App
from kivy.uix.screenmanager import ScreenManager, Screen
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.textinput import TextInput
from kivy.uix.button import Button
from kivy.uix.popup import Popup
from kivy.uix.scrollview import ScrollView
from kivy.uix.widget import Widget
from kivy.metrics import dp, sp
from kivy.core.window import Window
from kivy.utils import platform
from kivy.clock import Clock
from kivy.core.clipboard import Clipboard
from kivy.animation import Animation

from datetime import datetime
import os, sys, shutil, subprocess, math, re, json
from math import ceil

try:
    from plyer import share
except Exception:
    share = None

try:
    from plyer import gps as plyer_gps
except Exception:
    plyer_gps = None

if platform == "android":
    try:
        from android.permissions import request_permissions, Permission
        from android.storage import primary_external_storage_path
        from jnius import autoclass
    except Exception:
        request_permissions = None
        Permission = None
        primary_external_storage_path = None
        autoclass = None
else:
    Window.size = (360, 720)

def build_pdf_cartaceo(path_pdf, intest, corse):
    try:
        from fpdf import FPDF
    except Exception as e:
        raise RuntimeError("FPDF non installato (pip install fpdf)") from e

    cols = [
        "Fruitore servizio","Luogo di partenza","Ora di partenza","KM iniziali",
        "Luogo di destinazione","Ora di arrivo","KM finali"
    ]
    widths = [40, 62, 31, 26, 62, 31, 25]
    ROWS_PER_PAGE = 16
    ROW_H = 8

    def _pdf_safe(s: str) -> str:
        if s is None: return ""
        t = str(s)
        t = (t.replace("\u2026", "...").replace("\u2013", "-")
               .replace("\u2014", "-").replace("\u2019", "'")
               .replace("\xa0", " "))
        try:
            t.encode("latin-1")
        except UnicodeEncodeError:
            t = t.encode("latin-1", "ignore").decode("latin-1")
        return t

    def _fit_text_ellipsis(pdf, text, w):
        txt = _pdf_safe(text)
        if pdf.get_string_width(txt) <= w - 2: return txt
        base = txt; ELL = "..."
        while base and pdf.get_string_width(base + ELL) > w - 2:
            base = base[:-1]
        return (base + ELL) if base else ELL

    def _is_centered_col(name):
        return ("Ora" in name) or ("KM" in name)

    all_rows = [{k: str((r or {}).get(k, "")) for k in cols} for r in (corse or [])]
    total_rows = len(all_rows)
    if total_rows == 0:
        pages = 1
    else:
        pages = ceil(total_rows / ROWS_PER_PAGE)

    pdf = FPDF(orientation="L", unit="mm", format="A4")
    pdf.set_auto_page_break(auto=False)

    def header_page():
        pdf.set_font("Helvetica", "B", 16)
        pdf.cell(0, 10, "FOGLIO DI VIAGGIO", ln=1, align="C")
        i = intest or {}
        pdf.set_font("Helvetica", "", 11)
        pdf.ln(2)
        pdf.cell(100, 6, f"Data: {i.get('Data','')}")
        pdf.cell(120, 6, f"Foglio di servizio N°: {i.get('Foglio di servizio N°','')}", ln=1)
        pdf.cell(100, 6, f"Targa: {i.get('Targa','')}")
        pdf.cell(120, 6, f"Nome e Cognome: {i.get('Nome e Cognome','')}", ln=1)
        pdf.cell(100, 6, f"KM iniziali rimessa: {i.get('KM iniziali rimessa','')}")
        pdf.cell(120, 6, f"KM finali rimessa: {i.get('KM finali rimessa','')}", ln=1)
        pdf.ln(4)
        pdf.set_font("Helvetica", "B", 10)
        for w, h in zip(widths, cols):
            pdf.cell(w, ROW_H, h, 1, 0, "C")
        pdf.ln(ROW_H)
        pdf.set_font("Helvetica", "", 10)

    pos = 0
    for p in range(pages):
        pdf.add_page(orientation="L")
        header_page()

        slice_rows = all_rows[pos: pos + ROWS_PER_PAGE]; pos += ROWS_PER_PAGE
        while len(slice_rows) < ROWS_PER_PAGE:
            slice_rows.append({k: "" for k in cols})
        for corsa in slice_rows:
            for w, name in zip(widths, cols):
                raw = corsa.get(name, "")
                txt = _fit_text_ellipsis(pdf, raw, w)
                align = "C" if _is_centered_col(name) else "L"
                pdf.cell(w, ROW_H, txt, border=1, ln=0, align=align)
            pdf.ln(ROW_H)
        pdf.set_y(-10); pdf.set_font("Helvetica", "", 8)
        pdf.cell(0, 6, f"Pagina {p+1}/{pages}", align="R")

    pdf.output(path_pdf)
    return path_pdf

class CorseScreen(Screen):
    COLONNE = [
        "Fruitore servizio","Luogo di partenza","Ora di partenza","KM iniziali",
        "Luogo di destinazione","Ora di arrivo","KM finali"
    ]

    def __init__(self, **kw):
        super().__init__(**kw)
        # Inizializzazione variabili
        self.corse = []
        self.corsa_corrente = None
        self.campi = {}
        self.inputs = []
        self.gps_on = False
        self.track = []
        self.gps_km_raw = 0.0
        self._pickup_set = False
        self._drop_set = False
        self._first_fix = None
        self._still_since = None
        self._km_at_pickup = None
        self.SPEED_STILL_KMH = 15.0
        self.DWELL_S = 10.0
        self.START_RADIUS_M = 50.0
        self.MIN_TRAVEL_KM_FOR_DROP = 0.5
        self._clip_ev = None
        self._last_clip = ""
        self._last_clip_used = ""
        
        # MODIFICA: KM ora sono interi
        self._anchor_value = 0          # ultimo valore confermato (manuale o auto) - INTERO
        self._gps_total = 0.0           # km GPS cumulativi (float per precisione)
        self._gps_total_anchor = 0.0    # cumulativo al momento dell'ultima conferma (float)
        
        # NUOVO: Sistema backup
        self._backup_ev = None
        self._gps_button_anim = None
        
        # UI Setup
        self._setup_ui()
        
        # NUOVO: Carica backup all'avvio
        Clock.schedule_once(lambda dt: self._carica_backup(), 0.5)

    def _setup_ui(self):
        root = BoxLayout(orientation='vertical')
        
        # Form principale
        form = BoxLayout(orientation='vertical', size_hint_y=None, padding=dp(14), spacing=dp(8))
        form.bind(minimum_height=form.setter('height'))
        
        # Creazione campi input
        for campo in self.COLONNE:
            form.add_widget(Label(text=campo, size_hint_y=None, height=dp(22), font_size=sp(15)))
            ti = TextInput(multiline=False, size_hint_y=None, height=dp(44), font_size=sp(16), 
                          background_color=(1, 1, 1, 0.9))  # Font più spesso
            
            # MODIFICA: Per campi KM, solo numeri interi
            if "KM" in campo:
                ti.input_filter = 'int'  # Solo numeri interi
                try:
                    ti.input_type = 'number'
                except Exception:
                    pass
            
            if campo in ("Ora di partenza", "Ora di arrivo"):
                ti.bind(on_text_validate=lambda inst: setattr(inst, "text", datetime.now().strftime("%H:%M")))
            
            # Gestione speciale per campi KM
            if campo == "KM iniziali":
                ti.bind(on_text_validate=self._on_enter_km_ini)
            elif campo == "KM finali":
                ti.bind(on_text_validate=self._on_enter_km_fin)
            
            ti.bind(focus=self._scroll_on_focus)
            self.campi[campo] = ti
            self.inputs.append(ti)
            form.add_widget(ti)

        # Configurazione navigazione tra campi
        for i, ti in enumerate(self.inputs):
            if i < len(self.inputs) - 1:
                nxt = self.inputs[i + 1]
                ti.bind(on_text_validate=lambda inst, n=nxt: setattr(n, 'focus', True))
            else:
                ti.bind(on_text_validate=lambda inst: setattr(inst, 'focus', False))

        self.scroll = ScrollView(size_hint=(1, 1), do_scroll_x=False)
        self.scroll.add_widget(form)
        root.add_widget(self.scroll)

        # Barra pulsanti
        bar = GridLayout(cols=4, size_hint=(1, None), height=dp(230), padding=dp(10), spacing=dp(10))
        
        def mkbtn(txt, cb, color=(0.35,0.35,0.45,1), fz=sp(16)):
            b = Button(text=txt, font_size=fz, background_normal="", background_color=color, color=(1,1,1,1),
                      bold=True)  # Font più spesso
            b.bind(size=lambda inst, _: setattr(inst, 'text_size', inst.size))
            b.halign = 'center'
            b.valign = 'middle'
            b.bind(on_release=cb)
            return b

        bar.add_widget(mkbtn("Intest", self.apri_intestazione_popup))
        bar.add_widget(mkbtn("Nuova", self.nuova_corsa, (0.95,0.60,0.20,1)))
        bar.add_widget(mkbtn("Inizia", self.inizia_corsa, (0.20,0.55,0.20,1)))
        bar.add_widget(mkbtn("Esporta", self.esporta_pdf, (0.20,0.55,0.90,1)))
        bar.add_widget(mkbtn("Elenco", self.popup_elenco))
        bar.add_widget(mkbtn("Completa", self.completa_corsa, (0.85,0.30,0.30,1)))
        bar.add_widget(mkbtn("Salva", self.salva_corsa, (0.30,0.70,0.30,1)))
        
        # NUOVO: Bottone GPS con animazione
        self.gps_btn = mkbtn("GPS\nON/OFF", self.gps_toggle, (0.20,0.45,0.20,1))
        bar.add_widget(self.gps_btn)
        
        bar.add_widget(mkbtn("Importa\nUber", self.importa_da_uber, (0.50,0.40,0.80,1)))
        
        root.add_widget(bar)

        # Etichetta KM GPS
        self.lbl_km = Label(text="KM GPS: 0", size_hint_y=None, height=dp(30), font_size=sp(14), bold=True)
        root.add_widget(self.lbl_km)
        root.add_widget(Widget(size_hint_y=None, height=dp(0)))
        
        self.add_widget(root)
        
        # Avvia watcher clipboard su Android
        if platform == "android":
            self._start_clipboard_watcher()
            
        # NUOVO: Avvia sistema backup
        self._start_backup_system()

    # =========================================================================
    # NUOVO: SISTEMA DI BACKUP AUTOMATICO
    # =========================================================================
    
    def _get_backup_path(self):
        """Restituisce il percorso del file di backup"""
        app = App.get_running_app()
        backup_dir = os.path.join(app.user_data_dir, "backup")
        os.makedirs(backup_dir, exist_ok=True)
        return os.path.join(backup_dir, "app_state.json")
    
    def _salva_backup(self):
        """Salva lo stato corrente dell'app"""
        try:
            stato = {
                'corse': self.corse,
                'corsa_corrente': self.corsa_corrente,
                'campi_correnti': {k: v.text for k, v in self.campi.items()},
                'gps_on': self.gps_on,
                'gps_km_raw': self.gps_km_raw,
                '_anchor_value': self._anchor_value,
                '_gps_total': self._gps_total,
                '_gps_total_anchor': self._gps_total_anchor,
                '_pickup_set': self._pickup_set,
                '_drop_set': self._drop_set,
                'timestamp': datetime.now().isoformat()
            }
            
            with open(self._get_backup_path(), 'w', encoding='utf-8') as f:
                json.dump(stato, f, ensure_ascii=False, indent=2)
                
            print("✅ Backup salvato automaticamente")
            
        except Exception as e:
            print(f"❌ Errore salvataggio backup: {e}")
    
    def _carica_backup(self):
        """Carica lo stato salvato dell'app"""
        try:
            backup_path = self._get_backup_path()
            if not os.path.exists(backup_path):
                print("ℹ️ Nessun backup trovato")
                return
                
            with open(backup_path, 'r', encoding='utf-8') as f:
                stato = json.load(f)
            
            # Ripristina dati
            self.corse = stato.get('corse', [])
            self.corsa_corrente = stato.get('corsa_corrente')
            
            # Ripristina campi correnti
            campi_correnti = stato.get('campi_correnti', {})
            for campo, valore in campi_correnti.items():
                if campo in self.campi:
                    self.campi[campo].text = valore
            
            # Ripristina stato GPS
            self.gps_on = stato.get('gps_on', False)
            self.gps_km_raw = stato.get('gps_km_raw', 0.0)
            self._anchor_value = stato.get('_anchor_value', 0)
            self._gps_total = stato.get('_gps_total', 0.0)
            self._gps_total_anchor = stato.get('_gps_total_anchor', 0.0)
            self._pickup_set = stato.get('_pickup_set', False)
            self._drop_set = stato.get('_drop_set', False)
            
            # Aggiorna UI
            self._aggiorna_ui_da_backup()
            
            print("✅ Backup caricato con successo")
            self._msg("Stato precedente ripristinato", "Backup")
            
        except Exception as e:
            print(f"❌ Errore caricamento backup: {e}")
    
    def _aggiorna_ui_da_backup(self):
        """Aggiorna l'UI dopo il caricamento del backup"""
        # Aggiorna label KM
        km_total_int = int(ceil(self.gps_km_raw))
        km_since_anchor_int = self._km_since_anchor()
        self.lbl_km.text = f"KM GPS: {km_total_int} (+{km_since_anchor_int} dall'ancora)"
        
        # Aggiorna animazione bottone GPS
        if self.gps_on:
            self._start_gps_animation()
        else:
            self._stop_gps_animation()
    
    def _start_backup_system(self):
        """Avvia il sistema di backup automatico"""
        # Backup ogni 30 secondi
        self._backup_ev = Clock.schedule_interval(lambda dt: self._salva_backup(), 30)
        
        # Backup quando l'app va in background (solo Android)
        if platform == "android":
            self._setup_android_lifecycle()
    
    def _setup_android_lifecycle(self):
        """Configura il rilevamento dello stato dell'app su Android"""
        try:
            if autoclass:
                PythonActivity = autoclass('org.kivy.android.PythonActivity')
                activity = PythonActivity.mActivity
                
                # Qui potremmo aggiungere listener per pause/resume
                # Per ora usiamo il backup periodico
                pass
        except Exception as e:
            print(f"⚠️ Impossibile configurare lifecycle Android: {e}")
    
    def _stop_backup_system(self):
        """Ferma il sistema di backup"""
        if self._backup_ev:
            self._backup_ev.cancel()
    
    # =========================================================================
    # NUOVO: ANIMAZIONE BOTTONE GPS
    # =========================================================================
    
    def _start_gps_animation(self):
        """Avvia l'animazione lampeggiante per il bottone GPS"""
        if self._gps_button_anim:
            self._gps_button_anim.cancel(self.gps_btn)
        
        anim = Animation(background_color=(0.0, 0.8, 0.0, 1), duration=0.8) + \
               Animation(background_color=(0.2, 0.45, 0.2, 1), duration=0.8)
        anim.repeat = True
        self._gps_button_anim = anim
        anim.start(self.gps_btn)
    
    def _stop_gps_animation(self):
        """Ferma l'animazione del bottone GPS"""
        if self._gps_button_anim:
            self._gps_button_anim.cancel(self.gps_btn)
            self._gps_button_anim = None
        
        # Ripristina colore normale
        Animation(background_color=(0.20, 0.45, 0.20, 1), duration=0.3).start(self.gps_btn)

    # =========================================================================
    # METODI ESISTENTI (con piccole migliorie)
    # =========================================================================

    def _short(self, s, n=7):
        t = (s or "").strip()
        return (t[:n] + "...") if len(t) > n else t

    def _ui_clean(self, s):
        if s is None: return ""
        t = str(s)
        repl = {
            "\u2026": "...", "\u2013": "-", "\u2014": "-", "\u2019": "'",
            "\xa0": " ", "\u200b": "", "\u200c": "", "\u200d": "", "\ufeff": ""
        }
        for k, v in repl.items(): 
            t = t.replace(k, v)
        t = "".join(ch for ch in t if (ch.isprintable() or ch in " \t"))
        t = " ".join(t.split())
        return t

    def _scroll_on_focus(self, ti, focused):
        if focused and hasattr(self, 'scroll'):
            Clock.schedule_once(lambda dt: self.scroll.scroll_to(ti, padding=dp(90), animate=True), 0)

    def _msg(self, text, title="Info"):
        Popup(title=title, content=Label(text=text), size_hint=(0.9, 0.5)).open()

    # METODI PER GESTIONE KM INTERI
    def _km_since_anchor(self) -> int:
        """Restituisce i KM percorsi dall'ultima ricalibrazione (arrotondati per eccesso)"""
        km_float = max(0.0, float(self._gps_total - self._gps_total_anchor))
        return int(ceil(km_float))  # Arrotonda per eccesso a intero

    def _set_anchor(self, value: int):
        """Imposta nuovo punto di riferimento per la ricalibrazione"""
        try:
            v = int(value)
        except (ValueError, TypeError):
            return
        self._anchor_value = v
        self._gps_total_anchor = self._gps_total
        # NUOVO: Salva backup dopo ricalibrazione
        self._salva_backup()

    def _on_enter_km_ini(self, inst):
        """Gestione INVIO sul campo KM iniziali"""
        txt = (inst.text or "").strip()
        
        if txt:
            # MODALITÀ MANUALE: l'utente ha inserito un valore -> RICALIBRAZIONE
            try:
                val = int(txt)  # Ora usiamo int invece di float
                inst.text = f"{val}"
                self._set_anchor(val)  # Imposta nuovo punto di riferimento
                self._msg(f"Ricalibrato: {val} km")
            except ValueError:
                inst.text = ""
                self._msg("Inserire un numero intero")
        else:
            # MODALITÀ AUTOMATICA: calcola KM attuali basati sull'ultima ricalibrazione + delta GPS
            auto_val = self._anchor_value + self._km_since_anchor()
            inst.text = f"{auto_val}"
            # NON fare _set_anchor qui, mantieni il riferimento precedente

    def _on_enter_km_fin(self, inst):
        """Gestione INVIO sul campo KM finali"""
        txt = (inst.text or "").strip()
        
        if txt:
            # MODALITÀ MANUALE: ricalibrazione
            try:
                val = int(txt)  # Ora usiamo int invece di float
                inst.text = f"{val}"
                self._set_anchor(val)  # Imposta nuovo punto di riferimento
                self._msg(f"Ricalibrato: {val} km")
            except ValueError:
                inst.text = ""
                self._msg("Inserire un numero intero")
        else:
            # MODALITÀ AUTOMATICA: calcola KM finali
            auto_val = self._anchor_value + self._km_since_anchor()
            inst.text = f"{auto_val}"
            # NON fare _set_anchor qui

    def _odometro_delta(self) -> int:
        """Restituisce i KM totali dall'odometro (intero)"""
        return int(ceil(self.gps_km_raw))

    def _open_folder_desktop(self, path):
        try:
            folder = os.path.dirname(path)
            if sys.platform.startswith("win"):
                os.startfile(folder)
            elif sys.platform == "darwin":
                subprocess.call(["open", folder])
            else:
                subprocess.call(["xdg-open", folder])
        except Exception:
            pass

    def clean_address(self, s: str) -> str:
        if not s: return s
        s = re.sub(r'^\s*Cin:\s*[A-Za-z0-9]+,\s*', '', s, flags=re.IGNORECASE)
        s = re.sub(r'(,\s*)?\b\d{5}\b(?=,|$|\s)', '', s)
        s = re.sub(r',\s*(Italia|Italy)\s*$', '', s, flags=re.IGNORECASE)
        s = re.sub(r'\s*,\s*', ', ', s)
        s = re.sub(r'\s{2,}', ' ', s).strip()
        s = re.sub(r'(,\s*){2,}', ', ', s)
        s = re.sub(r',\s*$', '', s)
        return s

    def parse_uber_text(self, txt: str):
        lines = [l.strip() for l in (txt or "").splitlines() if l.strip()]
        kv = {}
        for ln in lines:
            if '\t' in ln:
                k, v = ln.split('\t', 1)
            else:
                parts = re.split(r'\s{2,}|:\s*', ln, maxsplit=1)
                if len(parts) != 2: continue
                k, v = parts
            kv[k.strip().lower()] = v.strip()
        ret = {}
        name = kv.get('passenger name') or kv.get('passeggero') or kv.get('fruitore') or kv.get('rider') or kv.get('cliente')
        if name: ret["Fruitore servizio"] = name.strip()
        frm = kv.get('from') or kv.get('partenza') or kv.get('pickup')
        if frm: ret["Luogo di partenza"] = self.clean_address(frm.strip())
        to = kv.get('destination') or kv.get('destinazione') or kv.get('drop-off') or kv.get('drop off') or kv.get('dropoff')
        if to:  ret["Luogo di destinazione"] = self.clean_address(to.strip())
        return ret

    def import_from_text(self, txt: str, silent=False) -> bool:
        data = self.parse_uber_text(txt or "")
        if not data: return False
        for key in ("Fruitore servizio","Luogo di partenza","Luogo di destinazione"):
            if key in data and key in self.campi:
                self.campi[key].text = data[key]
        if not silent: self._msg("Campi compilati dall'import.", title="Importa")
        # NUOVO: Salva backup dopo import
        self._salva_backup()
        return True

    def importa_da_uber(self, *_):
        root = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(10))
        root.add_widget(Label(text="Incolla qui i dettagli corsa (testo):", size_hint_y=None, height=dp(24)))
        ti = TextInput(multiline=True, size_hint=(1, 1)); root.add_widget(ti)
        btns = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(8))
        b_ok = Button(text="Compila", background_normal="", background_color=(0.30,0.70,0.30,1))
        b_no = Button(text="Annulla")
        btns.add_widget(b_no); btns.add_widget(b_ok)
        root.add_widget(btns)
        pop = Popup(title="Importa da Uber", content=root, size_hint=(0.95, 0.85))
        b_ok.bind(on_release=lambda *_: (self.import_from_text(ti.text), pop.dismiss()))
        b_no.bind(on_release=lambda *_: pop.dismiss())
        pop.open()

    # Metodi GPS (modificati per animazione)
    def gps_toggle(self, *_):
        if not self._gps_available():
            self._msg("GPS non disponibile su questo dispositivo (o permessi mancanti).")
            return
        if self.gps_on: 
            self._gps_stop()
        else: 
            self._gps_start()

    def _gps_available(self):
        return platform == "android" and (plyer_gps is not None)

    def _gps_start(self):
        self._pickup_set = False; self._drop_set = False
        self._first_fix = None; self._still_since = None; self._km_at_pickup = None
        try:
            if request_permissions and Permission:
                request_permissions([Permission.ACCESS_FINE_LOCATION, Permission.ACCESS_COARSE_LOCATION])
        except Exception:
            pass
        try:
            plyer_gps.configure(on_location=self._on_location, on_status=self._on_gps_status)
            plyer_gps.start(minTime=1000, minDistance=5)
            self.gps_on = True
            self._start_gps_animation()  # NUOVO: Avvia animazione
            self._msg("GPS avviato")
            self._salva_backup()  # NUOVO: Salva stato
        except Exception as e:
            self._msg(f"Impossibile avviare GPS:\n{e}")

    def _gps_stop(self):
        try: 
            plyer_gps.stop()
        except Exception: 
            pass
        self.gps_on = False
        self._stop_gps_animation()  # NUOVO: Ferma animazione
        self._msg("GPS fermato")
        self._salva_backup()  # NUOVO: Salva stato

    def _on_gps_status(self, stype, status): 
        pass

    @staticmethod
    def _hav_km(p1, p2):
        R = 6371.0
        lat1, lon1 = map(math.radians, p1)
        lat2, lon2 = map(math.radians, p2)
        dlat = lat2 - lat1; dlon = lon2 - lon1
        a = math.sin(dlat/2)**2 + math.cos(lat1)*math.cos(lat2)*math.sin(dlon/2)**2
        return 2 * R * math.asin(math.sqrt(a))

    def _on_location(self, **kwargs):
        try:
            lat = float(kwargs.get("lat")); lon = float(kwargs.get("lon"))
            acc = float(kwargs.get("accuracy", 9999))
            spd = float(kwargs.get("speed", 0.0))
        except Exception:
            return
        if acc > 100: return

        pt = (lat, lon)
        d = 0.0
        if self.track:
            d = self._hav_km(self.track[-1], pt)
            if 0.0 <= d <= 1.0: 
                self.gps_km_raw += d
                self._gps_total += d  # Aggiorna il totale GPS (float per precisione)
        
        self.track.append(pt)

        # Aggiorna label con valori interi
        km_total_int = int(ceil(self.gps_km_raw))
        km_since_anchor_int = self._km_since_anchor()
        self.lbl_km.text = f"KM GPS: {km_total_int} (+{km_since_anchor_int} dall'ancora)"

        speed_kmh = (spd * 3.6) if spd <= 60 else spd
        is_still = speed_kmh <= self.SPEED_STILL_KMH
        now_ts = datetime.now().timestamp()

        if self._first_fix is None: 
            self._first_fix = pt
        if is_still:
            if self._still_since is None: 
                self._still_since = now_ts
        else:
            self._still_since = None
        dwell_ok = (self._still_since is not None) and ((now_ts - self._still_since) >= self.DWELL_S)

        if not self._pickup_set and dwell_ok and self._first_fix is not None:
            d0_km = self._hav_km(self._first_fix, pt)
            if d0_km * 1000.0 <= self.START_RADIUS_M:
                self.campi["Ora di partenza"].text = datetime.now().strftime("%H:%M")
                self._pickup_set = True; self._km_at_pickup = self.gps_km_raw
                try:
                    if not (self.campi["KM iniziali"].text or "").strip():
                        app = App.get_running_app()
                        if getattr(app, "last_km_final", None) is not None:
                            # MODIFICA: Converti a intero
                            self.campi["KM iniziali"].text = f"{int(app.last_km_final)}"
                        else:
                            # MODIFICA: Usa calcolo con interi
                            auto_val = self._anchor_value + self._km_since_anchor()
                            self.campi["KM iniziali"].text = f"{auto_val}"
                except Exception:
                    pass

        if self._pickup_set and not self._drop_set and dwell_ok:
            if self._km_at_pickup is not None:
                traveled = max(0.0, self.gps_km_raw - self._km_at_pickup)
                if traveled >= self.MIN_TRAVEL_KM_FOR_DROP:
                    self.campi["Ora di arrivo"].text = datetime.now().strftime("%H:%M")
                    self._drop_set = True
                    try:
                        km_ini_txt = (self.campi["KM iniziali"].text or "").strip()
                        km_ini_val = int(km_ini_txt) if km_ini_txt else 0
                        # MODIFICA: Calcola KM finali con interi
                        km_fin_val = km_ini_val + self._km_since_anchor()
                        self.campi["KM finali"].text = f"{km_fin_val}"
                        app = App.get_running_app(); app.last_km_final = km_fin_val
                    except Exception:
                        pass

    def _prep_next_corsa(self, start_gps: bool):
        app = App.get_running_app()
        try:
            app.last_km_final = int((self.campi["KM finali"].text or "").strip())
        except Exception:
            pass
        for t in self.campi.values(): 
            t.text = ""
        self.track = []; self.gps_km_raw = 0.0
        self._pickup_set = False; self._drop_set = False
        self._first_fix = None; self._still_since = None; self._km_at_pickup = None
        self.lbl_km.text = "KM GPS: 0"

        if start_gps and self._gps_available() and not self.gps_on:
            self._gps_start()
        
        # NUOVO: Salva backup dopo preparazione nuova corsa
        self._salva_backup()

    def salva_corsa(self, *_):
        app = App.get_running_app()
        c = {k: (self.campi[k].text or "") for k in self.COLONNE}
        
        # MODIFICA: Logica per calcolo automatico KM finali con interi
        if (not c.get("KM finali")) and c.get("KM iniziali", "").strip():
            try:
                km_ini = int(c["KM iniziali"])
                km_calc = self._km_since_anchor()  # già intero
                c["KM finali"] = f"{km_ini + km_calc}"
                self.campi["KM finali"].text = c["KM finali"]
            except ValueError:
                pass
        
        if any((v or "").strip() for v in c.values()):
            if self.corsa_corrente is None:
                self.corse.append(dict(c))
            else:
                self.corse[self.corsa_corrente] = dict(c); self.corsa_corrente = None
            self._msg("Corsa salvata")
            self._prep_next_corsa(start_gps=False)
            if self.gps_on: 
                self._gps_stop()
            # NUOVO: Salva backup dopo salvataggio corsa
            self._salva_backup()
        else:
            self._msg("Compila almeno un campo")

    def nuova_corsa(self, *_):
        self._prep_next_corsa(start_gps=False)

    def popup_elenco(self, *_):
        box = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(10), size_hint_y=None)
        box.bind(minimum_height=box.setter('height'))
        if not self.corse:
            box.add_widget(Label(text="Nessuna corsa"))
        else:
            for i, corsa in enumerate(self.corse):
                r = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(6))
                part = self._ui_clean(corsa.get('Luogo di partenza',''))
                dest = self._ui_clean(corsa.get('Luogo di destinazione',''))
                desc = f"{i+1}. {part} → {dest}"
                lbl = Label(text=desc, shorten=True, shorten_from='right', size_hint_x=1)
                lbl.bind(size=lambda inst, _v: setattr(inst, "text_size", inst.size))
                r.add_widget(lbl)
                chip_txt = self._short(self._ui_clean(corsa.get('Fruitore servizio','')), 7)
                chip = Button(text=chip_txt or "-", size_hint=(None, 1), width=dp(78),
                              background_normal="", background_color=(0.45,0.45,0.52,1),
                              color=(1,1,1,1), disabled=True)
                r.add_widget(chip)
                b1 = Button(text="Apri", size_hint=(None,1), width=dp(80),
                            background_normal="", background_color=(0.55,0.55,0.60,1))
                b2 = Button(text="Elimina", size_hint=(None,1), width=dp(90),
                            background_normal="", background_color=(0.85,0.30,0.30,1))
                b1.bind(on_release=lambda _w, idx=i: self._carica(idx))
                b2.bind(on_release=lambda _w, idx=i: self._del(idx))
                r.add_widget(b1); r.add_widget(b2)
                box.add_widget(r)
        scr = ScrollView(size_hint=(1,1)); scr.add_widget(box)
        self._p = Popup(title="Elenco corse", content=scr, size_hint=(0.9,0.9)); self._p.open()

    def _carica(self, idx):
        if 0 <= idx < len(self.corse):
            for k, t in self.campi.items():
                t.text = self.corse[idx].get(k, "")
            self.corsa_corrente = idx
        if hasattr(self, '_p'): 
            self._p.dismiss()
        # NUOVO: Salva backup dopo caricamento corsa
        self._salva_backup()

    def _del(self, idx):
        if 0 <= idx < len(self.corse):
            if self.corsa_corrente == idx:
                for t in self.campi.values(): 
                    t.text = ""
                self.corsa_corrente = None
            self.corse.pop(idx)
            if hasattr(self, '_p'): 
                self._p.dismiss()
            self.popup_elenco()
            # NUOVO: Salva backup dopo eliminazione corsa
            self._salva_backup()

    def apri_intestazione_popup(self, *_):
        app = App.get_running_app()
        dati = getattr(app, 'intestazione', {})
        labels = ["Data","Foglio di servizio N°","Targa","Nome e Cognome",
                  "KM iniziali rimessa","KM finali rimessa"]

        cbox = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(10), size_hint_y=None)
        cbox.bind(minimum_height=cbox.setter('height'))
        inputs = {}
        order = []
        for n in labels:
            cbox.add_widget(Label(text=n, size_hint_y=None, height=dp(22)))
            ti = TextInput(text=dati.get(n,""), multiline=False, size_hint_y=None, height=dp(44))
            inputs[n] = ti
            order.append(ti)
            cbox.add_widget(ti)

        for i, ti in enumerate(order):
            if i < len(order)-1:
                nxt = order[i+1]
                ti.bind(on_text_validate=lambda inst, n=nxt: setattr(n, "focus", True))
            else:
                ti.bind(on_text_validate=lambda inst: setattr(inst, "focus", False))

        scr = ScrollView(); scr.add_widget(cbox)
        btn = Button(text="Salva", size_hint_y=None, height=dp(48),
                     background_normal="", background_color=(0.2,0.55,0.9,1))
        root = BoxLayout(orientation='vertical'); root.add_widget(scr); root.add_widget(btn)
        pop = Popup(title="Intestazione", content=root, size_hint=(0.9,0.9))

        def save_and_close(*_):
            app.intestazione = {k:v.text for k,v in inputs.items()}
            self._msg("Intestazione salvata.", title="Intestazione")
            pop.dismiss()
            # NUOVO: Salva backup dopo salvataggio intestazione
            self._salva_backup()

        btn.bind(on_release=save_and_close); pop.open()

    def inizia_corsa(self, *_):
        self.campi["Ora di partenza"].text = datetime.now().strftime("%H:%M")
        self._pickup_set = True
        if not self.gps_on and self._gps_available():
            self._gps_start()
        # NUOVO: Salva backup dopo inizio corsa
        self._salva_backup()

    def completa_corsa(self, *_):
        self.campi["Ora di arrivo"].text = datetime.now().strftime("%H:%M")
        # MODIFICA: Usa calcolo con interi
        auto_val = self._anchor_value + self._km_since_anchor()
        self.campi["KM finali"].text = f"{auto_val}"
        # NON fare _set_anchor qui per non cambiare il riferimento
        try:
            App.get_running_app().last_km_final = auto_val
        except Exception:
            pass
        self._drop_set = True
        # NUOVO: Salva backup dopo completamento corsa
        self._salva_backup()

    def esporta_pdf(self, *_):
        app = App.get_running_app()
        intest = getattr(app, "intestazione", {})
        day = datetime.now().strftime("%Y-%m-%d")
        ts  = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"Foglio_di_Viaggio_{ts}.pdf"

        rows = [dict(r) for r in self.corse]

        base_app = getattr(app, "user_data_dir", ".")
        internal_dir = os.path.join(base_app, "FDV", day)
        os.makedirs(internal_dir, exist_ok=True)

        path_app = os.path.join(internal_dir, filename)

        try:
            build_pdf_cartaceo(path_app, intest, rows)
        except Exception as e:
            self._msg(f"Errore PDF:\n{e}", title="PDF")
            return

        share_path = path_app
        public_copy = None

        if platform == "android":
            try:
                base_ext = primary_external_storage_path() if primary_external_storage_path else "/sdcard"
                public_dir = os.path.join(base_ext, "Download", "FDV", day)
                os.makedirs(public_dir, exist_ok=True)
                public_copy = os.path.join(public_dir, filename)
                shutil.copy(path_app, public_copy)
                share_path = public_copy
            except Exception:
                public_copy = None
                share_path = path_app

        if platform == "android" and share:
            try:
                share.share(
                    title="Foglio di Viaggio",
                    filepath=share_path,
                    mime_type="application/pdf"
                )
            except Exception as e:
                self._msg(f"Condivisione non riuscita:\n{e}\n\nFile in:\n{share_path}", title="PDF")
        else:
            self._open_folder_desktop(path_app)
            self.last_pdf_path = public_copy or path_app

    # Metodi Clipboard 
    def _start_clipboard_watcher(self):
        if self._clip_ev is None:
            self._clip_ev = Clock.schedule_interval(self._check_clipboard, 1.5)

    def _stop_clipboard_watcher(self):
        if self._clip_ev is not None:
            self._clip_ev.cancel()
            self._clip_ev = None

    def _check_clipboard(self, dt):
        try:
            txt = Clipboard.paste() or ""
        except Exception:
            return
        t = (txt or "").strip()
        if not t:
            return
        if t == self._last_clip or t == self._last_clip_used:
            return
        if self._looks_like_uber_text(t):
            self._last_clip = t
            self._show_clip_banner(t)

    def _looks_like_uber_text(self, t: str) -> bool:
        s = t.strip()
        s_l = s.lower()

        must_keys = ["trip #", "passenger name", "from", "destination"]
        score = sum(1 for k in must_keys if k in s_l)

        import re
        has_uuid = bool(re.search(r"trip\s*#\s*[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}", s, re.I))
        has_time = bool(re.search(r"\b\d{2}/\d{2}/\d{2}\s+\d{2}:\d{2}:\d{2}(?:\s+[A-Z]{2,5})?\b", s))
        has_via_uber = ("via\tuber" in s_l) or ("via uber" in s_l)

        return (score >= 3) and (has_uuid or has_time or has_via_uber)

    def _show_clip_banner(self, text: str):
        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(10))
        box.add_widget(Label(text="Trovati dati corsa negli appunti.\nVuoi incollarli qui?", size_hint_y=None, height=dp(44)))

        btns = GridLayout(cols=2, size_hint_y=None, height=dp(48), spacing=dp(8))
        b_no = Button(text="No", background_normal="", background_color=(0.55,0.55,0.60,1))
        b_ok = Button(text="Incolla", background_normal="", background_color=(0.30,0.70,0.30,1))
        btns.add_widget(b_no)
        btns.add_widget(b_ok)
        box.add_widget(btns)

        pop = Popup(title="Appunti rilevati", content=box, size_hint=(0.92, 0.32), auto_dismiss=False)

        def do_paste(*_a):
            ok = self.import_from_text(text, silent=True)
            if ok:
                self._msg("Campi compilati dagli appunti.", title="Importa")
                self._last_clip_used = text
            pop.dismiss()

        def do_cancel(*_a):
            self._last_clip_used = text
            pop.dismiss()

        b_ok.bind(on_release=do_paste)
        b_no.bind(on_release=do_cancel)
        pop.open()

class FDVApp(App):
    def build(self):
        self.intestazione = {}
        self.last_km_final = None
        if platform == "android":
            Window.softinput_mode = "below_target"
            try:
                if request_permissions and Permission:
                    request_permissions([
                        Permission.ACCESS_FINE_LOCATION, Permission.ACCESS_COARSE_LOCATION,
                        Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE
                    ])
            except Exception:
                pass
        sm = ScreenManager()
        self._corse_screen = CorseScreen(name="corse")
        sm.add_widget(self._corse_screen)
        return sm

if __name__ == "__main__":
    FDVApp().run()