#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Conversor de archivos AAF a sesiones de REAPER (.rpp).

Características principales:
- Independiente de la API interna de Reaper (genera el archivo .rpp directamente).
- Comprobación previa de ubicaciones de archivos de audio y video antes de crear
  el .rpp:
    * Verifica si los archivos embebidos (.wav extraídos) o vinculados existen
      realmente en el disco.
    * Si hay archivos vinculados que no se encuentran en su ruta original (por
      ejemplo, AAF exportado en otra PC), permite elegir una carpeta para
      buscarlos y revincularlos automáticamente en subcarpetas.
    * Informa claramente cuántos ítems se detectaron por pista (y avisa si el
      archivo AAF tiene pistas vacías sin clips).
- Dos modos de importación:
    1. Modo Completo (Full): Importa pistas de audio y video, ítems (posición,
       duración, offset, ganancia, paneo, fades, velocidad de reproducción),
       envolventes de automatización (volumen y paneo), marcadores con color,
       offset de código de tiempo (timecode), notas de metadatos y extracción de
       audios embebidos (.wav).
    2. Modo Seguro (SafeMode): Importa únicamente pistas de audio, sus ítems
       (posición, duración, offset, ganancia y fades) y la extracción de audios
       embebidos (.wav).
- Interfaz gráfica (Tkinter) sencilla e intuitiva.

Requisitos:
    python -m pip install pyaaf2
"""

import argparse
import os
import re
import sys
import time
import urllib.parse
import urllib.request
import uuid
import wave

try:
    import aaf2
    HAVE_AAF2 = True
except ModuleNotFoundError:
    aaf2 = None
    HAVE_AAF2 = False

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    HAVE_TK = True
except Exception:
    tk = None
    filedialog = None
    messagebox = None
    ttk = None
    HAVE_TK = False


# Mapa de nombres de colores comunes en marcadores AAF (Avid, Premiere, Resolve, FilmCraft)
NAMED_MARKER_COLORS = {
    "red": {"r": 230, "g": 50, "b": 50},
    "rose": {"r": 235, "g": 95, "b": 155},
    "pink": {"r": 240, "g": 120, "b": 180},
    "magenta": {"r": 210, "g": 60, "b": 210},
    "purple": {"r": 150, "g": 80, "b": 220},
    "violet": {"r": 140, "g": 90, "b": 230},
    "blue": {"r": 60, "g": 110, "b": 230},
    "cerulean": {"r": 45, "g": 165, "b": 225},
    "cyan": {"r": 50, "g": 200, "b": 210},
    "teal": {"r": 40, "g": 170, "b": 150},
    "green": {"r": 65, "g": 190, "b": 85},
    "yellow": {"r": 235, "g": 215, "b": 55},
    "mango": {"r": 245, "g": 155, "b": 45},
    "orange": {"r": 240, "g": 130, "b": 40},
    "brown": {"r": 150, "g": 100, "b": 65},
    "white": {"r": 240, "g": 240, "b": 240},
    "black": {"r": 45, "g": 45, "b": 45},
}


def sanitize_filename(name):
    """Limpia caracteres inválidos para nombres de archivo en Windows/macOS/Linux."""
    if not name:
        return "audio"
    cleaned = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", str(name)).strip(" ._")
    return cleaned if cleaned else "audio"


def new_guid():
    """Genera un GUID en el formato estándar de Reaper: {XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX}."""
    return "{" + str(uuid.uuid4()).upper() + "}"


def rgb_to_reaper_native(r, g, b):
    """
    Convierte valores RGB (0-255) al entero de color nativo de Reaper con el bit
    0x1000000 activado (formato estándar en archivos .rpp).
    """
    r = max(0, min(255, int(r)))
    g = max(0, min(255, int(g)))
    b = max(0, min(255, int(b)))
    return (r | (g << 8) | (b << 16)) | 0x1000000


def format_rpp_str(value):
    """
    Formatea una cadena para ser escrita en un archivo .rpp.
    Si contiene espacios, comillas o está vacía, la encierra entre comillas.
    """
    text = str(value) if value is not None else ""
    if '"' in text:
        text = text.replace('"', "'")
    if not text or any(c.isspace() for c in text) or any(c in text for c in "<>'"):
        return f'"{text}"'
    return text


def format_num(value):
    """Formatea números flotantes o enteros de manera limpia para archivos .rpp."""
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        if value.is_integer():
            return str(int(value))
        return f"{value:.14g}"
    return str(value)


def detect_source_type(filepath):
    """Determina el identificador de bloque <SOURCE ...> de Reaper según la extensión."""
    if not filepath:
        return "WAVE"
    ext = os.path.splitext(filepath)[1].lower()
    if ext in (".wav", ".bwf", ".w64", ".aif", ".aiff"):
        return "WAVE"
    if ext in (".mp3",):
        return "MP3"
    if ext in (".flac",):
        return "FLAC"
    if ext in (".ogg", ".opus"):
        return "VORBIS"
    if ext in (".mp4", ".mov", ".mkv", ".avi", ".mxf", ".webm", ".m4v", ".mpg", ".mpeg"):
        return "VIDEO"
    return "WAVE"


def index_media_directory(root_dir):
    """
    Crea un índice rápido {nombre_archivo_en_minusculas: ruta_absoluta}
    recorriendo recursivamente una carpeta para localizar audios o videos movidos.
    """
    file_index = {}
    if not root_dir or not os.path.isdir(root_dir):
        return file_index
    for dirpath, _, filenames in os.walk(root_dir):
        for fname in filenames:
            lower = fname.lower()
            if lower not in file_index:
                file_index[lower] = os.path.abspath(os.path.join(dirpath, fname))
    return file_index


def verify_and_relink_project_media(project_data, search_dirs=None, log_callback=None):
    """
    Comprueba las ubicaciones de todos los archivos de audio/video en project_data.
    Si un archivo no existe en su ruta original, intenta localizarlo en search_dirs.

    Devuelve un diccionario con el reporte:
        {
            "total_items": int,
            "found_items": list,
            "missing_items": list,
            "relinked_items": list,
        }
    """
    def _log(msg, level="INFO"):
        if log_callback:
            log_callback(f"[{level}] {msg}")
        else:
            print(f"[{level}] {msg}")

    indexes = []
    if search_dirs:
        for sdir in search_dirs:
            if sdir and os.path.isdir(sdir):
                indexes.append(index_media_directory(sdir))

    found_items = []
    missing_items = []
    relinked_items = []
    total_items = 0

    for track in project_data.get("tracks", []):
        track_name = track.get("name", "Track")
        for item in track.get("items", []):
            total_items += 1
            src = (item.get("source") or "").strip()
            item_name = item.get("name") or (os.path.basename(src.replace("\\", "/")) if src else "Clip")

            # 1. Comprobar si ya existe tal cual en el disco
            if src and os.path.isfile(src):
                abs_src = os.path.abspath(src)
                item["source"] = abs_src
                found_items.append(
                    {"track": track_name, "name": item_name, "path": abs_src}
                )
                continue

            # 2. Intentar buscar por nombre de archivo en las carpetas de búsqueda
            candidates = []
            if src:
                basename = os.path.basename(src.replace("\\", "/"))
                if basename:
                    candidates.append(basename.lower())
            if item_name:
                clean_item = os.path.basename(item_name.replace("\\", "/"))
                if clean_item.lower() not in candidates:
                    candidates.append(clean_item.lower())
                # Probar agregando .wav si el nombre del Mob no tenía extensión
                if not os.path.splitext(clean_item)[1]:
                    candidates.append((clean_item + ".wav").lower())

            resolved_path = None
            for idx_map in indexes:
                for cand in candidates:
                    if cand in idx_map and os.path.isfile(idx_map[cand]):
                        resolved_path = idx_map[cand]
                        break
                if resolved_path:
                    break

            if resolved_path:
                old_src = src or item_name
                item["source"] = resolved_path
                relinked_items.append(
                    {
                        "track": track_name,
                        "name": item_name,
                        "old_path": old_src,
                        "new_path": resolved_path,
                    }
                )
                found_items.append(
                    {"track": track_name, "name": item_name, "path": resolved_path}
                )
                _log(f"Archivo relocalizado para '{item_name}': {resolved_path}")
            else:
                missing_items.append(
                    {
                        "track": track_name,
                        "name": item_name,
                        "expected_path": src if src else f"(Sin ruta vinculada: {item_name})",
                        "item_ref": item,
                    }
                )
                _log(
                    f"Archivo NO encontrado en pista '{track_name}' -> '{item_name}' (Ruta esperada: {src or 'ninguna'})",
                    "WARNING",
                )

    return {
        "total_items": total_items,
        "found_items": found_items,
        "missing_items": missing_items,
        "relinked_items": relinked_items,
    }


class AAFParser:
    """Extrae metadatos, pistas, ítems, automatizaciones, marcadores y audios de un archivo AAF."""

    def __init__(self, log_callback=None, extra_search_dirs=None):
        self.aaf = None
        self.encoder = ""
        self.aaf_path = ""
        self.aaf_directory = ""
        self.essence_by_mob_id = {}
        self.essence_by_name = {}
        self.sample_rate = 48000
        self.log_callback = log_callback
        self.extra_search_dirs = list(extra_search_dirs) if extra_search_dirs else []

    def log(self, message, level="INFO"):
        if self.log_callback:
            self.log_callback(f"[{level}] {message}")
        else:
            print(f"[{level}] {message}")

    def open(self, filename):
        if not HAVE_AAF2:
            self.log(
                "No se encontró la librería 'pyaaf2'. Instálala ejecutando: python -m pip install pyaaf2",
                "ERROR",
            )
            return False
        try:
            self.aaf = aaf2.open(filename, "r")
        except Exception as exc:
            self.log(f"No se pudo abrir el archivo AAF: {exc}", "ERROR")
            return False

        self.aaf_path = os.path.abspath(filename)
        self.aaf_directory = os.path.dirname(self.aaf_path)
        self.essence_by_mob_id = {}
        self.essence_by_name = {}
        self.encoder = ""

        try:
            ident = self.aaf.header["IdentificationList"][0]
            if "ProductName" in ident:
                self.encoder = str(ident["ProductName"].value)
        except Exception:
            self.log("No se pudo identificar el software de origen del AAF.", "WARNING")

        self.sample_rate = self._detect_sample_rate()
        return True

    def close(self):
        if self.aaf is not None:
            try:
                self.aaf.close()
            except Exception:
                pass
            self.aaf = None

    @staticmethod
    def rational_to_float(val):
        """Convierte un AAFRational, fracción o número a float."""
        if val is None:
            return 0.0
        if hasattr(val, "numerator") and hasattr(val, "denominator"):
            return float(val.numerator) / float(val.denominator) if val.denominator else 0.0
        try:
            return float(val)
        except Exception:
            return 0.0

    @staticmethod
    def _mob_id_str(mob):
        if mob is None:
            return ""
        mob_id = getattr(mob, "mob_id", None)
        return str(mob_id) if mob_id is not None else str(id(mob))

    def _detect_sample_rate(self):
        """Intenta detectar la frecuencia de muestreo del proyecto AAF."""
        try:
            for comp in self.aaf.content.compositionmobs():
                if "UserComments" in comp:
                    for comment in comp["UserComments"]:
                        name = str(comment["Name"].value) if "Name" in comment else ""
                        val = str(comment["Value"].value) if "Value" in comment else ""
                        if "sample rate" in name.lower() and val.isdigit():
                            return int(val)
                for slot in comp.slots:
                    if str(slot.media_kind) in ("Sound", "LegacySound"):
                        rate = int(round(self.rational_to_float(slot.edit_rate)))
                        if rate in (22050, 44100, 48000, 88200, 96000, 176400, 192000):
                            return rate
        except Exception:
            pass
        return 48000

    def get_aaf_metadata(self):
        """Devuelve un diccionario con los metadatos del encabezado AAF."""
        meta = {
            "company": "Desconocido",
            "product": "Desconocido",
            "version": "",
            "date": "",
            "platform": "",
        }
        try:
            identity = self.aaf.header["IdentificationList"][0]
            if "CompanyName" in identity:
                meta["company"] = str(identity["CompanyName"].value)
            if "ProductName" in identity:
                meta["product"] = str(identity["ProductName"].value)
            if "ProductVersionString" in identity:
                meta["version"] = str(identity["ProductVersionString"].value)
            if "Date" in identity:
                meta["date"] = str(identity["Date"].value)
            if "Platform" in identity:
                meta["platform"] = str(identity["Platform"].value)
        except Exception:
            self.log("No se pudieron leer todos los metadatos de identidad del AAF.", "WARNING")
        return meta

    def get_composition_list(self):
        """Lista los nombres de todas las composiciones (CompositionMobs) en el AAF."""
        if not self.aaf:
            return []
        result = []
        for idx, comp in enumerate(self.aaf.content.compositionmobs()):
            name = comp.name if getattr(comp, "name", None) else f"Composition {idx + 1}"
            result.append(name)
        return result

    def _find_first_source_clip_in_segment(self, segment, depth=0):
        """Busca recursivamente el primer SourceClip dentro de cualquier estructura de segmento AAF."""
        if segment is None or depth > 12:
            return None
        if aaf2 and isinstance(segment, aaf2.components.SourceClip):
            return segment
        if aaf2 and isinstance(segment, aaf2.components.Sequence):
            for comp in getattr(segment, "components", []):
                found = self._find_first_source_clip_in_segment(comp, depth + 1)
                if found is not None:
                    return found
        if aaf2 and isinstance(segment, aaf2.components.OperationGroup):
            for seg in getattr(segment, "segments", []):
                found = self._find_first_source_clip_in_segment(seg, depth + 1)
                if found is not None:
                    return found
        if aaf2 and isinstance(segment, aaf2.components.EssenceGroup):
            for choice in getattr(segment, "choices", []):
                found = self._find_first_source_clip_in_segment(choice, depth + 1)
                if found is not None:
                    return found
        # Fallback genérico para Selector / NestedScope u otros contenedores
        for attr in ("selected", "segment", "components", "segments", "choices", "slots"):
            if hasattr(segment, attr):
                val = getattr(segment, attr)
                if hasattr(val, "value"):
                    val = val.value
                if isinstance(val, (list, tuple)) or hasattr(val, "__iter__"):
                    try:
                        for item in val:
                            found = self._find_first_source_clip_in_segment(item, depth + 1)
                            if found is not None:
                                return found
                    except Exception:
                        pass
                elif val is not None:
                    found = self._find_first_source_clip_in_segment(val, depth + 1)
                    if found is not None:
                        return found
        return None

    def _resolve_source_mob_chain(self, slot):
        """
        Sigue la cadena de referencias SourceClip desde un slot de MasterMob hasta encontrar
        el SourceMob que contiene el audio embebido (.essence) o el locator de archivo externo.
        """
        clip = self._find_first_source_clip_in_segment(getattr(slot, "segment", None))
        visited = set()
        best_mob = None

        while clip is not None:
            mob = getattr(clip, "mob", None)
            if mob is None:
                break
            mob_key = self._mob_id_str(mob)
            if mob_key in visited:
                break
            visited.add(mob_key)
            best_mob = mob

            # Si este Mob ya tiene esencia embebida o tiene locators en su descriptor, lo devolvemos
            if getattr(mob, "essence", None) is not None:
                return mob
            desc = getattr(mob, "descriptor", None)
            if desc is not None:
                try:
                    if hasattr(desc, "locator") and len(list(desc.locator)) > 0:
                        return mob
                except Exception:
                    pass

            # Intentar seguir bajando en la cadena de Mobs (ej. FileMob -> TapeMob)
            next_slot_id = getattr(clip, "slot_id", None)
            next_clip = None
            for s in getattr(mob, "slots", []):
                if next_slot_id is None or getattr(s, "slot_id", None) == next_slot_id:
                    next_clip = self._find_first_source_clip_in_segment(getattr(s, "segment", None))
                    if next_clip is not None:
                        break
            if next_clip is None:
                for s in getattr(mob, "slots", []):
                    next_clip = self._find_first_source_clip_in_segment(getattr(s, "segment", None))
                    if next_clip is not None:
                        break
            clip = next_clip

        return best_mob

    def get_embedded_essence_count(self):
        """Cuenta cuántos flujos de audio embebidos hay para extraer."""
        if not self.aaf:
            return 0
        count = 0
        for master_mob in self.aaf.content.mastermobs():
            for slot in master_mob.slots:
                source_mob = self._resolve_source_mob_chain(slot)
                if source_mob is None:
                    continue
                if str(slot.segment.media_kind) in ("Sound", "LegacySound") and getattr(source_mob, "essence", None):
                    count += 1
        return count

    def build_wav(self, fname, data, depth=16, rate=48000, channels=1):
        """Escribe datos PCM crudos en un archivo .wav."""
        sample_width = max(1, int(round(depth / 8)))
        framerate = max(8000, int(round(rate)))
        nchannels = max(1, int(channels))
        with wave.open(fname, "wb") as wav_file:
            wav_file.setnchannels(nchannels)
            wav_file.setsampwidth(sample_width)
            wav_file.setframerate(framerate)
            wav_file.writeframesraw(data)

    @staticmethod
    def _decode_aaf_url(raw_url):
        """Convierte un URLString de AAF (ej. file:///C%3a/carpeta/audio.wav) en una ruta del sistema."""
        if not raw_url:
            return ""
        raw_url = str(raw_url).strip()
        parsed = urllib.parse.urlparse(raw_url)
        if parsed.scheme in ("file", ""):
            path_part = urllib.parse.unquote(parsed.netloc + parsed.path)
            # En Windows, url2pathname convierte /C:/Users/... en C:\Users\...
            if re.match(r"^/[a-zA-Z]:/", path_part):
                path_part = path_part[1:]
            try:
                url_path = urllib.request.url2pathname(path_part)
            except Exception:
                url_path = path_part
        else:
            url_path = urllib.parse.unquote(raw_url)
        return url_path

    def get_linked_essence(self, mob):
        """Resuelve la ruta de un archivo de audio o video externo vinculado al AAF."""
        if mob is None:
            return ""
        desc = getattr(mob, "descriptor", None)
        if desc is None:
            return ""

        try:
            locators = list(getattr(desc, "locator", []))
            if not locators and "Locator" in desc:
                locators = list(desc["Locator"].value)
            if not locators:
                return ""

            candidate_urls = []
            for loc in locators:
                for key in ("URLString", "PathName", "Name"):
                    if key in loc:
                        val = str(loc[key].value).strip()
                        if val:
                            candidate_urls.append(val)

            if not candidate_urls:
                return ""

            url_path = self._decode_aaf_url(candidate_urls[-1])
            if os.path.isfile(url_path):
                return os.path.abspath(url_path)

            # Buscar el archivo en la carpeta del .aaf, subcarpetas comunes y carpetas extra
            basename = os.path.basename(url_path.replace("\\", "/"))
            if basename:
                search_roots = [self.aaf_directory] + self.extra_search_dirs
                for root_dir in search_roots:
                    if not root_dir or not os.path.isdir(root_dir):
                        continue
                    direct = os.path.join(root_dir, basename)
                    if os.path.isfile(direct):
                        return os.path.abspath(direct)
                    for subdir in ("Audio Files", "Media", "sources", "Audio", "Video", "Bounced Files"):
                        sub_candidate = os.path.join(root_dir, subdir, basename)
                        if os.path.isfile(sub_candidate):
                            return os.path.abspath(sub_candidate)

            # Devolver la ruta decodificada aunque aún no exista en disco para que el verificador
            # previo pueda mostrar exactamente qué ruta esperaba el AAF y revincularla.
            return url_path
        except Exception as exc:
            mob_name = getattr(mob, "name", "desconocido")
            self.log(f"No se pudo resolver la ruta externa para '{mob_name}': {exc}", "WARNING")
            return ""

    def extract_embedded_essence(self, mob, filename):
        """Extrae un flujo de audio embebido en el AAF y lo guarda como archivo .wav."""
        self.log(f"Extrayendo audio embebido: {os.path.basename(filename)}")
        stream = mob.essence.open()
        data = stream.read()
        stream.close()

        # Si los bytes ya comienzan con cabecera RIFF/WAVE, se escriben directamente
        if len(data) >= 12 and data[:4] == b"RIFF" and data[8:12] == b"WAVE":
            with open(filename, "wb") as out_file:
                out_file.write(data)
            return filename

        meta = getattr(mob, "descriptor", None)
        data_fmt = ""
        if meta is not None and "ContainerFormat" in meta:
            try:
                data_fmt = str(meta["ContainerFormat"].value.name)
            except Exception:
                data_fmt = ""

        sample_depth = 16
        sample_rate = self.sample_rate
        channels = 1
        if meta is not None:
            if "QuantizationBits" in meta:
                try:
                    sample_depth = int(meta["QuantizationBits"].value)
                except Exception:
                    pass
            if "SampleRate" in meta:
                try:
                    sample_rate = self.rational_to_float(meta["SampleRate"].value)
                except Exception:
                    pass
            if "Channels" in meta:
                try:
                    channels = int(meta["Channels"].value)
                except Exception:
                    pass

        if data_fmt == "MXF" or not (len(data) >= 4 and data[:4] in (b"RIFF", b"FORM", b"OggS", b"fLaC")):
            self.build_wav(filename, data, sample_depth, sample_rate, channels)
        else:
            with open(filename, "wb") as out_file:
                out_file.write(data)

        return filename

    def extract_essence(self, target_dir, progress_callback=None):
        """Recorre todos los MasterMobs y SourceMobs para extraer audios embebidos o resolver rutas vinculadas."""
        if not self.aaf:
            return
        os.makedirs(target_dir, exist_ok=True)
        used_filenames = set()

        for master_mob in self.aaf.content.mastermobs():
            mob_id = self._mob_id_str(master_mob)
            mob_name = master_mob.name or mob_id
            self.essence_by_mob_id.setdefault(mob_id, {})
            self.essence_by_name.setdefault(mob_name, {})

            for slot in master_mob.slots:
                source_mob = self._resolve_source_mob_chain(slot)
                if source_mob is None:
                    self.essence_by_mob_id[mob_id][slot.slot_id] = ""
                    self.essence_by_name[mob_name][slot.slot_id] = ""
                    continue

                src_mob_id = self._mob_id_str(source_mob)
                src_mob_name = getattr(source_mob, "name", None) or mob_name
                self.essence_by_mob_id.setdefault(src_mob_id, {})
                self.essence_by_name.setdefault(src_mob_name, {})

                media_kind = str(slot.segment.media_kind)
                if media_kind == "Picture":
                    resolved = self.get_linked_essence(source_mob)
                    self.essence_by_mob_id[mob_id][slot.slot_id] = resolved
                    self.essence_by_name[mob_name][slot.slot_id] = resolved
                    self.essence_by_mob_id[src_mob_id][slot.slot_id] = resolved
                    continue

                if getattr(source_mob, "essence", None):
                    slot_suffix = f"_{slot.name}" if getattr(slot, "name", "") else f"_slot{slot.slot_id}"
                    base_clean = sanitize_filename(f"{mob_name}{slot_suffix}")
                    candidate_name = f"{base_clean}.wav"
                    counter = 1
                    while candidate_name.lower() in used_filenames:
                        candidate_name = f"{base_clean}_{counter}.wav"
                        counter += 1
                    used_filenames.add(candidate_name.lower())

                    filepath = os.path.join(target_dir, candidate_name)
                    if progress_callback:
                        progress_callback(f"Extrayendo {candidate_name}...")
                    try:
                        extracted = os.path.abspath(self.extract_embedded_essence(source_mob, filepath))
                    except Exception as exc:
                        self.log(f"Error extrayendo '{candidate_name}': {exc}", "WARNING")
                        extracted = ""

                    self.essence_by_mob_id[mob_id][slot.slot_id] = extracted
                    self.essence_by_name[mob_name][slot.slot_id] = extracted
                    self.essence_by_mob_id[src_mob_id][slot.slot_id] = extracted
                    self.essence_by_name[src_mob_name][slot.slot_id] = extracted
                else:
                    resolved = self.get_linked_essence(source_mob)
                    self.essence_by_mob_id[mob_id][slot.slot_id] = resolved
                    self.essence_by_name[mob_name][slot.slot_id] = resolved
                    self.essence_by_mob_id[src_mob_id][slot.slot_id] = resolved
                    self.essence_by_name[src_mob_name][slot.slot_id] = resolved

    def get_essence_file(self, mob, slot_id):
        """Obtiene la ruta de archivo asociada a un Mob y slot_id con múltiples niveles de respaldo."""
        if mob is None:
            return ""
        mob_id = self._mob_id_str(mob)
        mob_name = getattr(mob, "name", None) or ""

        # 1. Buscar por MobID exacto
        if mob_id in self.essence_by_mob_id:
            slot_map = self.essence_by_mob_id[mob_id]
            if slot_id in slot_map and slot_map[slot_id]:
                return slot_map[slot_id]
            for val in slot_map.values():
                if val:
                    return val

        # 2. Buscar por nombre del Mob
        if mob_name and mob_name in self.essence_by_name:
            slot_map = self.essence_by_name[mob_name]
            if slot_id in slot_map and slot_map[slot_id]:
                return slot_map[slot_id]
            for val in slot_map.values():
                if val:
                    return val

        # 3. Resolver en vivo siguiendo la cadena del Mob
        direct = self.get_linked_essence(mob)
        if direct:
            return direct

        for s in getattr(mob, "slots", []):
            if getattr(s, "slot_id", None) == slot_id or len(getattr(mob, "slots", [])) == 1:
                chained_mob = self._resolve_source_mob_chain(s)
                if chained_mob is not None:
                    chained_id = self._mob_id_str(chained_mob)
                    if chained_id in self.essence_by_mob_id:
                        for val in self.essence_by_mob_id[chained_id].values():
                            if val:
                                return val
                    chained_path = self.get_linked_essence(chained_mob)
                    if chained_path:
                        return chained_path

        return ""

    def get_point_list(self, varying, duration):
        """Extrae puntos de automatización (tiempo en segundos, valor)."""
        data = []
        try:
            for point in varying["PointList"]:
                pt_time = self.rational_to_float(point.time) * duration
                pt_val = self.rational_to_float(point.value)
                data.append({"time": pt_time, "value": pt_val})
        except Exception as exc:
            self.log(f"Error leyendo PointList de automatización: {exc}", "WARNING")
        return data

    def collect_vol_pan_automation(self, track):
        """
        Convierte las curvas de volumen y paneo por ítem en envolventes de pista
        (<VOLENV2> y <PANENV2>), manteniendo valor neutro (1.0 para vol, 0.0 para pan)
        en los ítems que no tienen automatización.
        """
        envelopes = {
            "volume_envelope": {"points": [], "default": 1.0},
            "panning_envelope": {"points": [], "default": 0.0},
        }
        items = track.get("items", [])
        for env_name, env_info in envelopes.items():
            has_any = any(env_name in item and item[env_name] for item in items)
            if not has_any:
                continue

            for item in items:
                if env_name in item and item[env_name]:
                    for point in item[env_name]:
                        env_info["points"].append(
                            {
                                "time": max(0.0, item["position"] + point["time"]),
                                "value": point["value"],
                            }
                        )
                    del item[env_name]
                else:
                    env_info["points"].append(
                        {"time": max(0.0, item["position"]), "value": env_info["default"]}
                    )
                    env_info["points"].append(
                        {
                            "time": max(0.0, item["position"] + item["duration"]),
                            "value": env_info["default"],
                        }
                    )

            env_info["points"].sort(key=lambda pt: pt["time"])
            track[env_name] = env_info["points"]

        return track

    def parse_operation_group(self, group, edit_rate):
        """Extrae ganancia, paneo, velocidad y el SourceClip subyacente de un OperationGroup."""
        item = {}
        op_name = getattr(getattr(group, "operation", None), "name", "") or ""
        group_duration = self.rational_to_float(getattr(group, "length", 0)) / edit_rate if edit_rate else 0.0

        try:
            parameters = list(getattr(group, "parameters", []))
        except Exception:
            parameters = []

        for param in parameters:
            p_name = getattr(param, "name", "") or ""
            p_lower = p_name.lower()

            if op_name in ("Mono Audio Gain", "Audio Gain", "Audio Channel Combiner") or p_lower in (
                "amplitude",
                "amplitude multiplier",
                "level",
                "gain",
            ):
                if aaf2 and isinstance(param, aaf2.misc.VaryingValue):
                    item["volume_envelope"] = self.get_point_list(param, group_duration)
                elif aaf2 and isinstance(param, aaf2.misc.ConstantValue):
                    item["volume"] = self.rational_to_float(param.value)

            elif op_name in ("Mono Audio Pan", "Audio Pan") or p_lower in (
                "pan value",
                "pan",
                "pan level",
            ):
                if aaf2 and isinstance(param, aaf2.misc.VaryingValue):
                    points = self.get_point_list(param, group_duration)
                    item["panning_envelope"] = [
                        {"time": pt["time"], "value": pt["value"] * -2.0 + 1.0}
                        for pt in points
                    ]
                elif aaf2 and isinstance(param, aaf2.misc.ConstantValue):
                    item["panning"] = self.rational_to_float(param.value) * 2.0 - 1.0

            elif p_name == "SpeedRatio" or p_lower == "speedratio":
                try:
                    item["playbackrate"] = self.rational_to_float(param.value)
                except Exception:
                    pass

        # Inspeccionar los segmentos internos recursivamente
        try:
            segments = list(getattr(group, "segments", []))
        except Exception:
            segments = []

        for seg in segments:
            if aaf2 and isinstance(seg, aaf2.components.Sequence):
                for sub in seg.components:
                    if isinstance(sub, aaf2.components.OperationGroup):
                        item.update(self.parse_operation_group(sub, edit_rate))
                    elif isinstance(sub, aaf2.components.SourceClip):
                        item.update(self._extract_source_clip_info(sub, edit_rate))
                        break
                    else:
                        nested_clip = self._find_first_source_clip_in_segment(sub)
                        if nested_clip is not None:
                            item.update(self._extract_source_clip_info(nested_clip, edit_rate))
                            break
            elif aaf2 and isinstance(seg, aaf2.components.OperationGroup):
                item.update(self.parse_operation_group(seg, edit_rate))
            elif aaf2 and isinstance(seg, aaf2.components.SourceClip):
                item.update(self._extract_source_clip_info(seg, edit_rate))
            else:
                nested_clip = self._find_first_source_clip_in_segment(seg)
                if nested_clip is not None:
                    item.update(self._extract_source_clip_info(nested_clip, edit_rate))

        return item

    def _extract_source_clip_info(self, source_clip, edit_rate):
        """Obtiene la ruta de archivo, nombre y offset de inicio de un SourceClip."""
        mob = getattr(source_clip, "mob", None)
        slot_id = getattr(source_clip, "slot_id", 1)
        src_path = self.get_essence_file(mob, slot_id)
        start_frames = self.rational_to_float(getattr(source_clip, "start", 0))
        offset_sec = start_frames / edit_rate if edit_rate else 0.0
        clip_name = ""
        if src_path:
            clip_name = os.path.basename(src_path.replace("\\", "/"))
        elif mob is not None and getattr(mob, "name", None):
            clip_name = str(mob.name)
        else:
            clip_name = f"Clip_slot{slot_id}"
        return {
            "source": src_path,
            "offset": max(0.0, offset_sec),
            "name": clip_name,
        }

    def parse_sequence(self, sequence, edit_rate):
        """Recorre los componentes de una Sequence AAF y devuelve la lista de ítems."""
        items = []
        current_time = 0.0
        fade_state = 0  # 0 = sin fade, 1 = aplicar fade-in al siguiente ítem, -1 = último fue Filler
        fade_length = None
        fade_type = 0  # 0 = lineal, 1 = curva de potencia (equal power)

        try:
            components = list(sequence.components)
        except Exception:
            return items

        for component in components:
            try:
                comp_len = self.rational_to_float(getattr(component, "length", 0))
                duration = comp_len / edit_rate if edit_rate else 0.0

                if aaf2 and isinstance(component, aaf2.components.SourceClip):
                    item = {
                        "position": max(0.0, current_time),
                        "duration": max(0.0, duration),
                    }
                    item.update(self._extract_source_clip_info(component, edit_rate))
                    if fade_state == 1 and fade_length is not None:
                        item["fadein"] = fade_length
                        item["fadeintype"] = fade_type
                    fade_state = 0
                    items.append(item)
                    current_time += duration

                elif aaf2 and isinstance(component, aaf2.components.OperationGroup):
                    # Comprobar si este OperationGroup envuelve una Sequence con múltiples clips
                    inner_segs = list(getattr(component, "segments", []))
                    if (
                        len(inner_segs) == 1
                        and isinstance(inner_segs[0], aaf2.components.Sequence)
                        and len(list(inner_segs[0].components)) > 1
                    ):
                        sub_items = self.parse_sequence(inner_segs[0], edit_rate)
                        for sub_it in sub_items:
                            sub_it["position"] += current_time
                        items.extend(sub_items)
                        current_time += duration
                        fade_state = 0
                        continue

                    item = {
                        "position": max(0.0, current_time),
                        "duration": max(0.0, duration),
                    }
                    item.update(self.parse_operation_group(component, edit_rate))
                    if fade_state == 1 and fade_length is not None:
                        item["fadein"] = fade_length
                        item["fadeintype"] = fade_type
                    fade_state = 0

                    if "source" not in item:
                        self.log(f"No se encontró fuente para el ítem en {current_time:.2f} s.", "WARNING")
                        item["source"] = ""
                    if "offset" not in item:
                        item["offset"] = 0.0
                    if "name" not in item or not item["name"]:
                        item["name"] = os.path.basename(item["source"]) if item["source"] else "Clip"

                    items.append(item)
                    current_time += duration

                elif aaf2 and isinstance(component, aaf2.components.Transition):
                    fade_length = max(0.0, duration)
                    fade_type = 0
                    try:
                        op_grp = component["OperationGroup"].value
                        interp_name = op_grp.parameters.value[0].interpolation.name
                        if interp_name == "PowerInterp":
                            fade_type = 1
                    except Exception:
                        pass

                    if fade_state == 0 and items:
                        items[-1]["fadeout"] = fade_length
                        items[-1]["fadeouttype"] = fade_type
                    if fade_state != 1:
                        fade_state = 1
                    current_time -= duration

                elif aaf2 and isinstance(component, aaf2.components.Filler):
                    fade_state = -1
                    current_time += duration

                elif aaf2 and isinstance(component, aaf2.components.Sequence):
                    sub_items = self.parse_sequence(component, edit_rate)
                    for sub_it in sub_items:
                        sub_it["position"] += current_time
                    items.extend(sub_items)
                    current_time += duration

                else:
                    # Fallback para EssenceGroup, Selector u otros contenedores de clip en una secuencia
                    nested_clip = self._find_first_source_clip_in_segment(component)
                    if nested_clip is not None:
                        item = {
                            "position": max(0.0, current_time),
                            "duration": max(0.0, duration),
                        }
                        item.update(self._extract_source_clip_info(nested_clip, edit_rate))
                        if fade_state == 1 and fade_length is not None:
                            item["fadein"] = fade_length
                            item["fadeintype"] = fade_type
                        fade_state = 0
                        items.append(item)
                    current_time += duration

            except Exception as exc:
                self.log(f"Error procesando componente en {current_time:.2f} s: {exc}", "WARNING")

        return items

    def _unwrap_track_segment_items(self, segment, edit_rate, track_data=None):
        """
        Desenrolla recursivamente cualquier cantidad de OperationGroups, NestedScopes o
        Sequences a nivel de pista para extraer todos los ítems sin perder ninguno.
        """
        if segment is None:
            return []

        if aaf2 and isinstance(segment, aaf2.components.Sequence):
            return self.parse_sequence(segment, edit_rate)

        if aaf2 and isinstance(segment, aaf2.components.SourceClip):
            dur = self.rational_to_float(getattr(segment, "length", 0)) / edit_rate if edit_rate else 0.0
            clip_info = self._extract_source_clip_info(segment, edit_rate)
            clip_info.update({"position": 0.0, "duration": max(0.0, dur)})
            return [clip_info]

        if aaf2 and isinstance(segment, aaf2.components.OperationGroup):
            if track_data is not None:
                for param in getattr(segment, "parameters", []):
                    p_name = getattr(param, "name", "")
                    if p_name == "Pan value" and isinstance(param, aaf2.misc.ConstantValue):
                        track_data["panning"] = self.rational_to_float(param.value) * 2.0 - 1.0
                    elif p_name in ("Pan", "Pan Level", "Pan value") and isinstance(
                        param, aaf2.misc.VaryingValue
                    ):
                        real_length = self.rational_to_float(segment.length) / edit_rate
                        if self.encoder == "DaVinci Resolve" and len(segment.segments) > 0:
                            real_length = self.rational_to_float(segment.segments[0].length) / edit_rate
                        points = self.get_point_list(param, real_length)
                        track_data["panning_envelope"] = [
                            {"time": pt["time"], "value": pt["value"] * -2.0 + 1.0}
                            for pt in points
                        ]
                    elif p_name in ("Amplitude", "Amplitude multiplier", "Level"):
                        if isinstance(param, aaf2.misc.ConstantValue):
                            track_data["volume"] = self.rational_to_float(param.value)

            collected = []
            for inner in getattr(segment, "segments", []):
                collected.extend(self._unwrap_track_segment_items(inner, edit_rate, track_data))
            return collected

        if aaf2 and isinstance(segment, aaf2.components.NestedScope):
            collected = []
            for seq in getattr(segment.slots, "value", []):
                collected.extend(self._unwrap_track_segment_items(seq, edit_rate, track_data))
            return collected

        return []

    def get_picture_tracks(self, slot):
        """Extrae pistas de video (Picture) del slot AAF."""
        tracks = []
        edit_rate = self.rational_to_float(slot.edit_rate)
        if not edit_rate:
            edit_rate = 24.0

        segment = slot.segment
        if aaf2 and isinstance(segment, aaf2.components.NestedScope):
            for idx, seq in enumerate(segment.slots.value):
                seq_items = self._unwrap_track_segment_items(seq, edit_rate)
                if seq_items:
                    tracks.append(
                        {
                            "name": slot.name or f"Video {idx + 1}",
                            "kind": "Picture",
                            "items": seq_items,
                        }
                    )
        else:
            seq_items = self._unwrap_track_segment_items(segment, edit_rate)
            if seq_items:
                tracks.append(
                    {
                        "name": slot.name or "Video",
                        "kind": "Picture",
                        "items": seq_items,
                    }
                )
        return tracks

    def get_sound_track(self, slot):
        """Extrae una pista de audio (Sound / LegacySound) del slot AAF."""
        track_data = {
            "name": slot.name or f"Audio {slot.slot_id}",
            "kind": "Sound",
            "items": [],
        }
        edit_rate = self.rational_to_float(slot.edit_rate)
        if not edit_rate:
            edit_rate = float(self.sample_rate)

        track_data["items"] = self._unwrap_track_segment_items(
            slot.segment, edit_rate, track_data=track_data
        )
        return track_data

    def get_markers(self, slot):
        """Extrae marcadores (DescriptiveMetadata) incluyendo nombres y colores."""
        markers = []
        edit_rate = self.rational_to_float(slot.edit_rate)
        if not edit_rate:
            edit_rate = 24.0

        segment = slot.segment
        components = list(getattr(segment, "components", [])) if hasattr(segment, "components") else [segment]

        for component in components:
            try:
                pos_frames = 0.0
                if "Position" in component:
                    pos_frames = self.rational_to_float(component["Position"].value)
                position_sec = pos_frames / edit_rate

                name = ""
                if "Comment" in component:
                    name = str(component["Comment"].value)

                colour = None
                if "CommentMarkerColour" in component:
                    col = component["CommentMarkerColour"].value
                    colour = {
                        "r": int(col["red"] / 256),
                        "g": int(col["green"] / 256),
                        "b": int(col["blue"] / 256),
                    }

                # Soporte para UserComments / ComponentComments (ej. FilmCraft, Avid, Premiere)
                for prop_key in ("UserComments", "ComponentComments"):
                    if prop_key in component:
                        comment_text = ""
                        marker_title = ""
                        for entry in component[prop_key]:
                            k = str(entry["Name"].value).strip() if "Name" in entry else ""
                            v = str(entry["Value"].value).strip() if "Value" in entry else ""
                            if k.lower() == "name" and v:
                                marker_title = v
                            elif k.lower() == "comment" and v:
                                comment_text = v
                            elif k.lower() in ("color", "colour") and v and colour is None:
                                colour = NAMED_MARKER_COLORS.get(v.lower())
                        if marker_title and comment_text and marker_title != comment_text:
                            name = f"{marker_title} - {comment_text}"
                        elif marker_title:
                            name = marker_title
                        elif comment_text and not name:
                            name = comment_text

                markers.append(
                    {
                        "name": name,
                        "position": max(0.0, position_sec),
                        "colour": colour,
                    }
                )
            except Exception as exc:
                self.log(f"Error leyendo marcador: {exc}", "WARNING")

        return markers

    def get_timecode_offset(self, slot):
        """Extrae el desplazamiento de código de tiempo inicial (en segundos) si existe un slot Timecode."""
        try:
            edit_rate = self.rational_to_float(slot.edit_rate)
            segment = slot.segment
            if "Start" in segment:
                start_frames = self.rational_to_float(segment["Start"].value)
                fps = edit_rate if edit_rate > 0 else float(segment["FPS"].value)
                if fps > 0:
                    return start_frames / fps
        except Exception:
            pass
        return 0.0

    def get_composition(self, composition_index=0, safe_mode=False):
        """
        Extrae toda la información de la composición indicada.
        Si safe_mode=True, solo incluye pistas de audio y sus propiedades básicas
        (posición, duración, offset, ganancia, fades) sin video, marcadores ni automatizaciones.
        """
        data = {
            "name": "AAF Import",
            "sample_rate": self.sample_rate,
            "proj_offset": 0.0,
            "metadata": self.get_aaf_metadata(),
            "user_comments": {},
            "tracks": [],
            "markers": [],
        }

        compositions = list(self.aaf.content.compositionmobs())
        if not compositions:
            self.log("El archivo AAF no contiene composiciones (CompositionMobs).", "WARNING")
            return data

        comp = compositions[min(max(0, composition_index), len(compositions) - 1)]
        data["name"] = comp.name or "AAF Session"

        # Comentarios de usuario de la composición (ej. resolución, sample rate)
        if not safe_mode and "UserComments" in comp:
            try:
                for comment in comp["UserComments"]:
                    k = str(comment["Name"].value) if "Name" in comment else ""
                    v = str(comment["Value"].value) if "Value" in comment else ""
                    if k:
                        data["user_comments"][k] = v
            except Exception:
                pass

        for slot in comp.slots:
            try:
                media_kind = str(slot.media_kind)
                if media_kind in ("Sound", "LegacySound"):
                    track_data = self.get_sound_track(slot)
                    if safe_mode:
                        track_data.pop("volume_envelope", None)
                        track_data.pop("panning_envelope", None)
                        for item in track_data.get("items", []):
                            item.pop("volume_envelope", None)
                            item.pop("panning_envelope", None)
                            item.pop("playbackrate", None)
                            item.pop("panning", None)
                    else:
                        track_data = self.collect_vol_pan_automation(track_data)
                    data["tracks"].append(track_data)

                elif not safe_mode and media_kind == "Picture":
                    picture_tracks = self.get_picture_tracks(slot)
                    if picture_tracks:
                        data["tracks"].extend(picture_tracks)

                elif not safe_mode and media_kind == "DescriptiveMetadata":
                    data["markers"].extend(self.get_markers(slot))

                elif not safe_mode and media_kind == "Timecode":
                    tc_offset = self.get_timecode_offset(slot)
                    if tc_offset > 0:
                        data["proj_offset"] = tc_offset

            except Exception as exc:
                slot_name = getattr(slot, "name", str(getattr(slot, "slot_id", "?")))
                self.log(f"Error procesando el slot '{slot_name}': {exc}", "WARNING")

        return data


class RPPGenerator:
    """Genera un archivo de sesión de Reaper (.rpp) a partir de los datos extraídos del AAF."""

    @staticmethod
    def build_rpp_content(project_data, safe_mode=False):
        sample_rate = int(project_data.get("sample_rate", 48000))
        proj_offset = 0.0 if safe_mode else float(project_data.get("proj_offset", 0.0))
        timestamp = int(time.time())

        lines = []
        lines.append(f'<REAPER_PROJECT 0.1 "6.80/win32" {timestamp}')

        # Bloque <NOTES>
        lines.append("  <NOTES 0 2")
        if not safe_mode:
            meta = project_data.get("metadata", {})
            if meta.get("product") and meta.get("product") != "Desconocido":
                lines.append(
                    f"    |Importado desde AAF ({meta.get('company', '')} {meta.get('product', '')} {meta.get('version', '')})"
                )
            for k, v in project_data.get("user_comments", {}).items():
                lines.append(f"    |{k}: {v}")
        lines.append("  >")

        lines.extend(
            [
                "  RIPPLE 0",
                "  GROUPOVERRIDE 0 0 0",
                "  AUTOXFADE 1",
                "  ENVATTACH 3",
                "  POOLEDENVATTACH 0",
                "  MIXERUIFLAGS 11 48",
                "  PEAKGAIN 1",
                "  FEEDBACK 0",
                "  PANLAW 1",
                f"  PROJOFFS {format_num(proj_offset)} 0 0",
                "  MAXPROJLEN 0 0",
                "  GRID 3199 8 1 8 1 0 0 0",
                "  TIMEMODE 1 5 -1 30 0 0 -1",
                "  VIDEO_CONFIG 0 0 256",
                "  PANMODE 3",
                "  CURSOR 0",
                "  ZOOM 18.09988511555567 0 0",
                "  VZOOMEX 6 0",
                "  USE_REC_CFG 0",
                "  RECMODE 1",
                "  SMPTESYNC 0 30 100 40 1000 300 0 0 1 0 0",
                "  LOOP 0",
                "  LOOPGRAN 0 4",
                '  RECORD_PATH "" ""',
                "  <RECORD_CFG",
                "    ZXZhdxgAAQ==",
                "  >",
                "  <APPLYFX_CFG",
                "  >",
                '  RENDER_FILE ""',
                '  RENDER_PATTERN ""',
                "  RENDER_FMT 0 2 0",
                "  RENDER_1X 0",
                "  RENDER_RANGE 1 0 0 18 1000",
                "  RENDER_RESAMPLE 3 0 1",
                "  RENDER_ADDTOPROJ 0",
                "  RENDER_STEMS 0",
                "  RENDER_DITHER 0",
                "  TIMELOCKMODE 1",
                "  TEMPOENVLOCKMODE 1",
                "  ITEMMIX 1",
                "  DEFPITCHMODE 589824 0",
                "  TAKELANE 1",
                f"  SAMPLERATE {sample_rate} 0 0",
                "  <RENDER_CFG",
                "    ZXZhdxgAAQ==",
                "  >",
                "  LOCK 1",
                "  <METRONOME 6 2",
                "    VOL 0.25 0.125",
                "    FREQ 800 1600 1",
                "    BEATLEN 4",
                '    SAMPLES "" ""',
                "    PATTERN 2863311530 2863311529",
                "    MULT 1",
                "  >",
                "  GLOBAL_AUTO -1",
                "  TEMPO 120 4 4",
                "  PLAYRATE 1 0 0.25 4",
                "  SELECTION 0 0",
                "  SELECTION2 0 0",
                "  MASTERAUTOMODE 0",
                "  MASTERTRACKHEIGHT 0 0",
                "  MASTERPEAKCOL 16576",
                "  MASTERMUTESOLO 0",
                "  MASTERTRACKVIEW 0 0.6667 0.5 0.5 0 0 0 0 0 0 0 0 0",
                "  MASTERHWOUT 0 0 1 0 0 0 0 -1",
                "  MASTER_NCH 2 2",
                "  MASTER_VOLUME 1 0 -1 -1 1",
                "  MASTER_PANMODE 3",
                "  MASTER_FX 1",
                "  MASTER_SEL 0",
                "  <MASTERPLAYSPEEDENV",
                f"    EGUID {new_guid()}",
                "    ACT 0 -1",
                "    VIS 0 1 1",
                "    LANEHEIGHT 0 0",
                "    ARM 0",
                "    DEFSHAPE 0 -1 -1",
                "  >",
                "  <TEMPOENVEX",
                f"    EGUID {new_guid()}",
                "    ACT 1 -1",
                "    VIS 1 0 1",
                "    LANEHEIGHT 0 0",
                "    ARM 0",
                "    DEFSHAPE 1 -1 -1",
                "  >",
            ]
        )

        # Marcadores (solo en Modo Completo)
        if not safe_mode:
            for idx, marker in enumerate(project_data.get("markers", []), start=1):
                pos = format_num(max(0.0, float(marker.get("position", 0.0))))
                m_name = format_rpp_str(marker.get("name", f"Marker {idx}"))
                colour = marker.get("colour")
                color_code = (
                    rgb_to_reaper_native(colour["r"], colour["g"], colour["b"])
                    if colour
                    else 0
                )
                lines.append(
                    f"  MARKER {idx} {pos} {m_name} 0 {color_code} 1 B {new_guid()}"
                )

        lines.append("  <PROJBAY")
        lines.append("  >")

        # Pistas e ítems
        iid_counter = 1
        for track in project_data.get("tracks", []):
            if safe_mode and track.get("kind") == "Picture":
                continue

            track_guid = new_guid()
            track_name = format_rpp_str(track.get("name", "Track"))
            track_vol = format_num(float(track.get("volume", 1.0)))
            track_pan = format_num(float(track.get("panning", 0.0)) if not safe_mode else 0.0)

            lines.extend(
                [
                    f"  <TRACK {track_guid}",
                    f"    NAME {track_name}",
                    "    PEAKCOL 16576",
                    "    BEAT -1",
                    "    AUTOMODE 0",
                    f"    VOLPAN {track_vol} {track_pan} -1 -1 1",
                    "    MUTESOLO 0 0 0",
                    "    IPHASE 0",
                    "    PLAYOFFS 0 1",
                    "    ISBUS 0 0",
                    "    BUSCOMP 0 0 0 0 0",
                    "    SHOWINMIX 1 0.6667 0.5 1 0.5 0 0 0",
                    "    SEL 0",
                    "    REC 0 0 1 0 0 0 0 0",
                    "    VU 2",
                    "    TRACKHEIGHT 0 0 0 0 0 0",
                    "    INQ 0 0 0 0.5 100 0 0 100",
                    "    NCHAN 2",
                    "    FX 1",
                    f"    TRACKID {track_guid}",
                    "    PERF 0",
                    "    MIDIOUT -1",
                    "    MAINSEND 1 0",
                ]
            )

            # Envolventes de automatización de pista (solo en Modo Completo)
            if not safe_mode:
                vol_env = track.get("volume_envelope", [])
                if vol_env:
                    lines.extend(
                        [
                            "    <VOLENV2",
                            f"      EGUID {new_guid()}",
                            "      ACT 1 -1",
                            "      VIS 1 1 1",
                            "      LANEHEIGHT 0 0",
                            "      ARM 0",
                            "      DEFSHAPE 0 -1 -1",
                        ]
                    )
                    for pt in vol_env:
                        lines.append(
                            f"      PT {format_num(pt['time'])} {format_num(pt['value'])} 0"
                        )
                    lines.append("    >")

                pan_env = track.get("panning_envelope", [])
                if pan_env:
                    lines.extend(
                        [
                            "    <PANENV2",
                            f"      EGUID {new_guid()}",
                            "      ACT 1 -1",
                            "      VIS 1 1 1",
                            "      LANEHEIGHT 0 0",
                            "      ARM 0",
                            "      DEFSHAPE 0 -1 -1",
                        ]
                    )
                    for pt in pan_env:
                        lines.append(
                            f"      PT {format_num(pt['time'])} {format_num(pt['value'])} 0"
                        )
                    lines.append("    >")

            # Ítems de la pista
            for item in track.get("items", []):
                pos = format_num(max(0.0, float(item.get("position", 0.0))))
                length = format_num(max(0.0, float(item.get("duration", 0.0))))
                soffs = format_num(max(0.0, float(item.get("offset", 0.0))))
                item_vol = format_num(float(item.get("volume", 1.0)))
                item_pan = format_num(
                    float(item.get("panning", 0.0)) if not safe_mode else 0.0
                )
                playrate = format_num(
                    float(item.get("playbackrate", 1.0)) if not safe_mode else 1.0
                )

                if item.get("fadein") is not None and float(item["fadein"]) > 0:
                    fi_shape = int(item.get("fadeintype", 0))
                    fi_len = format_num(float(item["fadein"]))
                    fadein_line = f"      FADEIN {fi_shape} {fi_len} 0 1 0 0 0"
                else:
                    fadein_line = "      FADEIN 1 0.01 0 1 0 0 0"

                if item.get("fadeout") is not None and float(item["fadeout"]) > 0:
                    fo_shape = int(item.get("fadeouttype", 0))
                    fo_len = format_num(float(item["fadeout"]))
                    fadeout_line = f"      FADEOUT {fo_shape} {fo_len} 0 1 0 0 0"
                else:
                    fadeout_line = "      FADEOUT 1 0.01 0 1 0 0 0"

                source_path = (item.get("source") or "").strip()
                raw_name = item.get("name") or (
                    os.path.basename(source_path.replace("\\", "/"))
                    if source_path
                    else f"Item_{iid_counter}"
                )
                item_name = format_rpp_str(raw_name)

                # Si no hay ruta de archivo pero sí nombre de clip, ponemos un nombre de archivo
                # de respaldo para que Reaper siempre dibuje el ítem de audio en la pista.
                if not source_path:
                    fallback_ext = ".mp4" if track.get("kind") == "Picture" else ".wav"
                    source_path = raw_name if os.path.splitext(raw_name)[1] else (raw_name + fallback_ext)

                source_type = detect_source_type(source_path)

                lines.extend(
                    [
                        "    <ITEM",
                        f"      POSITION {pos}",
                        "      SNAPOFFS 0",
                        f"      LENGTH {length}",
                        "      LOOP 1",
                        "      ALLTAKES 0",
                        fadein_line,
                        fadeout_line,
                        "      MUTE 0 0",
                        "      SEL 0",
                        f"      IGUID {new_guid()}",
                        f"      IID {iid_counter}",
                        f"      NAME {item_name}",
                        f"      VOLPAN {item_vol} {item_pan} 1 -1",
                        f"      SOFFS {soffs}",
                        f"      PLAYRATE {playrate} 1 0 -1 0 0.0025",
                        "      CHANMODE 0",
                        f"      GUID {new_guid()}",
                        f"      <SOURCE {source_type}",
                        f'        FILE "{source_path}"',
                        "      >",
                        "    >",
                    ]
                )
                iid_counter += 1

            lines.append("  >")

        lines.append(">")
        lines.append("")
        return "\n".join(lines)

    @classmethod
    def write_rpp(cls, output_path, project_data, safe_mode=False):
        content = cls.build_rpp_content(project_data, safe_mode=safe_mode)
        os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
        with open(output_path, "w", encoding="utf-8", newline="\r\n") as rpp_file:
            rpp_file.write(content)
        return os.path.abspath(output_path)


def prepare_aaf_project_data(
    aaf_path,
    rpp_path=None,
    safe_mode=False,
    composition_index=0,
    sources_subfolder=True,
    extra_media_dirs=None,
    log_callback=None,
    progress_callback=None,
):
    """
    Extrae los audios embebidos, lee la composición del AAF y comprueba las ubicaciones
    de todos los archivos de audio/video ANTES de escribir el archivo .rpp.
    Devuelve (rpp_abs, project_data, media_report).
    """
    aaf_abs = os.path.abspath(aaf_path)
    if not rpp_path:
        base_no_ext = os.path.splitext(aaf_abs)[0]
        rpp_path = f"{base_no_ext}.rpp"
    rpp_abs = os.path.abspath(rpp_path)
    rpp_dir = os.path.dirname(rpp_abs)
    rpp_stem = os.path.splitext(os.path.basename(rpp_abs))[0]

    search_dirs = [os.path.dirname(aaf_abs), rpp_dir]
    if extra_media_dirs:
        for d in extra_media_dirs:
            if d and d not in search_dirs:
                search_dirs.append(d)

    parser = AAFParser(log_callback=log_callback, extra_search_dirs=search_dirs)
    if not parser.open(aaf_abs):
        raise RuntimeError(f"No se pudo abrir el archivo AAF: {aaf_abs}")

    try:
        meta = parser.get_aaf_metadata()
        parser.log(
            f"AAF creado con {meta['company']} {meta['product']} {meta['version']} ({meta['platform']})"
        )
        parser.log(f"Frecuencia de muestreo detectada: {parser.sample_rate} Hz")

        embedded_count = parser.get_embedded_essence_count()
        parser.log(f"Flujos de audio embebidos detectados en el AAF: {embedded_count}")
        if sources_subfolder and embedded_count > 0:
            extract_dir = os.path.join(rpp_dir, f"{sanitize_filename(rpp_stem)}_Audio")
        else:
            extract_dir = rpp_dir

        parser.extract_essence(extract_dir, progress_callback=progress_callback)
        if extract_dir not in search_dirs:
            search_dirs.insert(0, extract_dir)

        comp_list = parser.get_composition_list()
        if comp_list:
            chosen_idx = min(max(0, composition_index), len(comp_list) - 1)
            parser.log(f"Analizando composición: '{comp_list[chosen_idx]}'")
        else:
            chosen_idx = 0

        mode_label = "SafeMode (Solo Audio e Ítems)" if safe_mode else "Modo Completo (Full)"
        parser.log(f"Modo seleccionado: {mode_label}")

        project_data = parser.get_composition(chosen_idx, safe_mode=safe_mode)

        # Resumen de ítems por pista
        for trk in project_data.get("tracks", []):
            parser.log(
                f"  Pista '{trk.get('name', 'Track')}' ({trk.get('kind', 'Sound')}): {len(trk.get('items', []))} ítem(s)"
            )

        # Comprobar ubicaciones de los archivos de audio/video
        media_report = verify_and_relink_project_media(
            project_data, search_dirs=search_dirs, log_callback=log_callback
        )
        parser.log(
            f"Comprobación de archivos: {len(media_report['found_items'])} localizado(s), "
            f"{len(media_report['missing_items'])} faltante(s) de {media_report['total_items']} ítem(s) totales."
        )
        if media_report["total_items"] == 0:
            parser.log(
                "AVISO: Este archivo AAF contiene las pistas pero 0 clips/ítems dentro de ellas.",
                "WARNING",
            )

        return rpp_abs, project_data, media_report
    finally:
        parser.close()


def convert_aaf_to_rpp(
    aaf_path,
    rpp_path=None,
    safe_mode=False,
    composition_index=0,
    sources_subfolder=True,
    extra_media_dirs=None,
    log_callback=None,
    progress_callback=None,
):
    """
    Función de alto nivel para comprobar medios y convertir un archivo .aaf a .rpp.
    """
    rpp_abs, project_data, media_report = prepare_aaf_project_data(
        aaf_path=aaf_path,
        rpp_path=rpp_path,
        safe_mode=safe_mode,
        composition_index=composition_index,
        sources_subfolder=sources_subfolder,
        extra_media_dirs=extra_media_dirs,
        log_callback=log_callback,
        progress_callback=progress_callback,
    )

    written_path = RPPGenerator.write_rpp(rpp_abs, project_data, safe_mode=safe_mode)
    total_tracks = len(project_data.get("tracks", []))
    total_items = media_report["total_items"]
    total_markers = len(project_data.get("markers", []))

    msg = (
        f"[INFO] Sesión generada: {total_tracks} pista(s), {total_items} ítem(s) "
        f"({len(media_report['found_items'])} con archivo verificado), {total_markers} marcador(es).\n"
        f"[INFO] Archivo guardado en: {written_path}"
    )
    if log_callback:
        log_callback(msg)
    else:
        print(msg)

    return written_path


class AAFToReaperGUI:
    """Interfaz gráfica en Tkinter con comprobación previa de ubicaciones de audio/video."""

    def __init__(self, root):
        self.root = root
        self.root.title("Conversor AAF a REAPER (.rpp)")
        self.root.geometry("760x620")
        self.root.minsize(680, 540)

        self.aaf_path_var = tk.StringVar()
        self.rpp_path_var = tk.StringVar()
        self.media_dir_var = tk.StringVar()
        self.mode_var = tk.StringVar(value="full")
        self.subfolder_var = tk.BooleanVar(value=True)
        self.comp_var = tk.StringVar()
        self.compositions = []

        self._build_ui()

        if not HAVE_AAF2:
            self.append_log(
                "[ADVERTENCIA] La librería 'pyaaf2' no está instalada. Ejecuta: python -m pip install pyaaf2"
            )

    def _build_ui(self):
        main_frame = ttk.Frame(self.root, padding=15)
        main_frame.pack(fill=tk.BOTH, expand=True)
        main_frame.columnconfigure(1, weight=1)
        main_frame.rowconfigure(6, weight=1)

        # 1. Selección de archivo AAF
        lbl_aaf = ttk.Label(main_frame, text="Archivo AAF de entrada:")
        lbl_aaf.grid(row=0, column=0, sticky="w", pady=(0, 8))

        entry_aaf = ttk.Entry(main_frame, textvariable=self.aaf_path_var)
        entry_aaf.grid(row=0, column=1, sticky="ew", padx=8, pady=(0, 8))

        btn_aaf = ttk.Button(main_frame, text="Cargar AAF...", command=self.browse_aaf)
        btn_aaf.grid(row=0, column=2, sticky="ew", pady=(0, 8))

        # 2. Selección/edición de archivo RPP de salida
        lbl_rpp = ttk.Label(main_frame, text="Sesión Reaper (.rpp):")
        lbl_rpp.grid(row=1, column=0, sticky="w", pady=(0, 8))

        entry_rpp = ttk.Entry(main_frame, textvariable=self.rpp_path_var)
        entry_rpp.grid(row=1, column=1, sticky="ew", padx=8, pady=(0, 8))

        btn_rpp = ttk.Button(main_frame, text="Cambiar...", command=self.browse_rpp)
        btn_rpp.grid(row=1, column=2, sticky="ew", pady=(0, 8))

        # 3. Carpeta opcional donde buscar los audios/videos vinculados
        lbl_media = ttk.Label(main_frame, text="Carpeta de audios/videos:")
        lbl_media.grid(row=2, column=0, sticky="w", pady=(0, 8))

        entry_media = ttk.Entry(main_frame, textvariable=self.media_dir_var)
        entry_media.grid(row=2, column=1, sticky="ew", padx=8, pady=(0, 8))

        btn_media = ttk.Button(
            main_frame, text="Buscar carpeta...", command=self.browse_media_dir
        )
        btn_media.grid(row=2, column=2, sticky="ew", pady=(0, 8))

        # 4. Selector de composición
        lbl_comp = ttk.Label(main_frame, text="Composición AAF:")
        lbl_comp.grid(row=3, column=0, sticky="w", pady=(0, 8))

        self.combo_comp = ttk.Combobox(
            main_frame, textvariable=self.comp_var, state="readonly"
        )
        self.combo_comp.grid(
            row=3, column=1, columnspan=2, sticky="ew", padx=(8, 0), pady=(0, 8)
        )

        # 5. Modo de importación
        mode_frame = ttk.LabelFrame(main_frame, text="Modo de conversión", padding=10)
        mode_frame.grid(row=4, column=0, columnspan=3, sticky="ew", pady=(4, 10))
        mode_frame.columnconfigure(0, weight=1)

        rb_full = ttk.Radiobutton(
            mode_frame,
            text=(
                "Modo Completo (Full): Importa todos los datos traducibles "
                "(audio, video, marcadores, automatizaciones, fades, timecode y extracción WAV)"
            ),
            variable=self.mode_var,
            value="full",
        )
        rb_full.grid(row=0, column=0, sticky="w", pady=(0, 4))

        rb_safe = ttk.Radiobutton(
            mode_frame,
            text=(
                "Modo Seguro (SafeMode): Solo pistas de audio, sus ítems "
                "(posición, duración, offset, ganancia, fades) y extracción de audios WAV"
            ),
            variable=self.mode_var,
            value="safe",
        )
        rb_safe.grid(row=1, column=0, sticky="w", pady=(0, 6))

        chk_sub = ttk.Checkbutton(
            mode_frame,
            text="Guardar audios embebidos extraídos en una subcarpeta junto al .rpp",
            variable=self.subfolder_var,
        )
        chk_sub.grid(row=2, column=0, sticky="w")

        # 6. Barra de progreso y botones de comprobación y conversión
        action_frame = ttk.Frame(main_frame)
        action_frame.grid(row=5, column=0, columnspan=3, sticky="ew", pady=(0, 10))
        action_frame.columnconfigure(0, weight=1)

        self.progress = ttk.Progressbar(action_frame, mode="determinate")
        self.progress.grid(row=0, column=0, sticky="ew", padx=(0, 10))

        self.btn_verify = ttk.Button(
            action_frame,
            text="Comprobar Archivos",
            command=self.run_media_check_only,
        )
        self.btn_verify.grid(row=0, column=1, sticky="e", padx=(0, 6))

        self.btn_convert = ttk.Button(
            action_frame,
            text="Comprobar y Crear .rpp",
            command=self.run_conversion,
        )
        self.btn_convert.grid(row=0, column=2, sticky="e")

        # 7. Registro / Consola de estado
        log_frame = ttk.LabelFrame(
            main_frame, text="Registro y verificación de ubicaciones de medios", padding=6
        )
        log_frame.grid(row=6, column=0, columnspan=3, sticky="nsew")
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)

        self.log_text = tk.Text(log_frame, height=12, wrap=tk.WORD, state=tk.DISABLED)
        self.log_text.grid(row=0, column=0, sticky="nsew")

        scrollbar = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview)
        scrollbar.grid(row=0, column=1, sticky="ns")
        self.log_text.configure(yscrollcommand=scrollbar.set)

    def append_log(self, text):
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.insert(tk.END, text + "\n")
        self.log_text.see(tk.END)
        self.log_text.configure(state=tk.DISABLED)
        self.root.update_idletasks()

    def browse_aaf(self):
        filename = filedialog.askopenfilename(
            title="Seleccionar archivo AAF",
            filetypes=[("Archivos AAF", "*.aaf"), ("Todos los archivos", "*.*")],
        )
        if not filename:
            return

        aaf_abs = os.path.abspath(filename)
        self.aaf_path_var.set(aaf_abs)

        # Por defecto propone el .rpp en la misma carpeta y con el mismo nombre
        default_rpp = os.path.splitext(aaf_abs)[0] + ".rpp"
        self.rpp_path_var.set(default_rpp)

        # Si aún no se eligió carpeta de medios, sugerir la carpeta del AAF
        if not self.media_dir_var.get().strip():
            self.media_dir_var.set(os.path.dirname(aaf_abs))

        self.inspect_aaf_compositions(aaf_abs)

    def browse_rpp(self):
        current_rpp = self.rpp_path_var.get().strip()
        initial_dir = os.path.dirname(current_rpp) if current_rpp else ""
        initial_file = os.path.basename(current_rpp) if current_rpp else "sesion.rpp"

        filename = filedialog.asksaveasfilename(
            title="Guardar sesión de Reaper como",
            initialdir=initial_dir,
            initialfile=initial_file,
            defaultextension=".rpp",
            filetypes=[("Proyecto de Reaper", "*.rpp"), ("Todos los archivos", "*.*")],
        )
        if filename:
            self.rpp_path_var.set(os.path.abspath(filename))

    def browse_media_dir(self):
        current_dir = self.media_dir_var.get().strip()
        chosen = filedialog.askdirectory(
            title="Seleccionar carpeta donde se encuentran los archivos de audio/video",
            initialdir=current_dir if os.path.isdir(current_dir) else "",
        )
        if chosen:
            self.media_dir_var.set(os.path.abspath(chosen))
            self.append_log(f"Carpeta de búsqueda de medios establecida en: {os.path.abspath(chosen)}")

    def inspect_aaf_compositions(self, aaf_path):
        """Lee las composiciones del AAF y muestra un resumen inicial del contenido."""
        self.compositions = []
        self.combo_comp["values"] = []
        self.comp_var.set("")

        if not HAVE_AAF2:
            return

        parser = AAFParser(log_callback=self.append_log)
        if not parser.open(aaf_path):
            return
        try:
            comp_list = parser.get_composition_list()
            self.compositions = comp_list
            embedded_cnt = parser.get_embedded_essence_count()
            master_cnt = len(list(parser.aaf.content.mastermobs()))
            if comp_list:
                display_values = [f"{i + 1}. {name}" for i, name in enumerate(comp_list)]
                self.combo_comp["values"] = display_values
                self.combo_comp.current(0)
                self.append_log(
                    f"AAF cargado: {len(comp_list)} composición(es), "
                    f"{master_cnt} MasterMob(s), {embedded_cnt} audio(s) embebido(s)."
                )
            else:
                self.append_log("Advertencia: No se encontraron composiciones en el AAF.")
        finally:
            parser.close()

    def _prepare_and_verify(self):
        """Ejecuta el análisis del AAF y la verificación de ubicaciones de archivos."""
        aaf_path = self.aaf_path_var.get().strip()
        rpp_path = self.rpp_path_var.get().strip()

        if not aaf_path:
            messagebox.showwarning("Falta archivo AAF", "Por favor selecciona un archivo .aaf.")
            return None
        if not os.path.isfile(aaf_path):
            messagebox.showerror("Archivo no encontrado", f"No existe el archivo:\n{aaf_path}")
            return None

        if not rpp_path:
            rpp_path = os.path.splitext(os.path.abspath(aaf_path))[0] + ".rpp"
            self.rpp_path_var.set(rpp_path)

        safe_mode = self.mode_var.get() == "safe"
        comp_idx = max(0, self.combo_comp.current()) if self.compositions else 0
        extra_dirs = []
        custom_media_dir = self.media_dir_var.get().strip()
        if custom_media_dir and os.path.isdir(custom_media_dir):
            extra_dirs.append(custom_media_dir)

        total_steps = 1
        if HAVE_AAF2:
            temp_parser = AAFParser()
            if temp_parser.open(aaf_path):
                total_steps = max(1, temp_parser.get_embedded_essence_count() + 1)
                temp_parser.close()

        self.progress["maximum"] = total_steps
        self.progress["value"] = 0

        def on_progress(msg):
            self.append_log(msg)
            self.progress.step(1)
            self.root.update_idletasks()

        rpp_abs, project_data, media_report = prepare_aaf_project_data(
            aaf_path=aaf_path,
            rpp_path=rpp_path,
            safe_mode=safe_mode,
            composition_index=comp_idx,
            sources_subfolder=self.subfolder_var.get(),
            extra_media_dirs=extra_dirs,
            log_callback=self.append_log,
            progress_callback=on_progress,
        )
        self.progress["value"] = total_steps
        return rpp_abs, project_data, media_report, safe_mode

    def run_media_check_only(self):
        """Comprueba los ítems y ubicaciones de archivos sin escribir todavía el .rpp."""
        self.btn_verify.configure(state=tk.DISABLED)
        self.btn_convert.configure(state=tk.DISABLED)
        try:
            res = self._prepare_and_verify()
            if res is None:
                return
            _, project_data, media_report, _ = res
            total_tracks = len(project_data.get("tracks", []))
            total_items = media_report["total_items"]
            found_cnt = len(media_report["found_items"])
            missing_cnt = len(media_report["missing_items"])

            if total_items == 0:
                messagebox.showwarning(
                    "AAF sin clips de audio/video",
                    f"Se detectaron {total_tracks} pista(s), pero el archivo AAF contiene 0 ítems/clips "
                    "dentro de las pistas.\n\n"
                    "Si exportaste este AAF desde un editor de video/audio, verifica en las opciones de "
                    "exportación que las pistas tengan clips activos o que se incluyan los medios.",
                )
            elif missing_cnt == 0:
                messagebox.showinfo(
                    "Comprobación exitosa",
                    f"Todos los archivos fueron localizados correctamente.\n\n"
                    f"• Pistas: {total_tracks}\n"
                    f"• Ítems verificados: {found_cnt} de {total_items}",
                )
            else:
                missing_preview = "\n".join(
                    f"• [{m['track']}] {m['name']} -> {m['expected_path']}"
                    for m in media_report["missing_items"][:8]
                )
                if missing_cnt > 8:
                    missing_preview += f"\n... y {missing_cnt - 8} archivo(s) más."
                messagebox.showwarning(
                    "Archivos faltantes detectados",
                    f"Se encontraron {found_cnt} de {total_items} archivos, pero faltan {missing_cnt}:\n\n"
                    f"{missing_preview}\n\n"
                    "Puedes usar el botón 'Buscar carpeta...' para indicar dónde están guardados los audios/videos.",
                )
        except Exception as exc:
            self.append_log(f"[ERROR] {exc}")
            messagebox.showerror("Error al comprobar AAF", str(exc))
        finally:
            self.btn_verify.configure(state=tk.NORMAL)
            self.btn_convert.configure(state=tk.NORMAL)

    def run_conversion(self):
        """Comprueba primero las ubicaciones de los archivos y luego genera el archivo .rpp."""
        self.btn_verify.configure(state=tk.DISABLED)
        self.btn_convert.configure(state=tk.DISABLED)

        try:
            res = self._prepare_and_verify()
            if res is None:
                return
            rpp_abs, project_data, media_report, safe_mode = res

            # 1. Si el AAF no tiene ningún ítem en sus pistas, avisar antes de crear el .rpp
            if media_report["total_items"] == 0:
                proceed_empty = messagebox.askyesno(
                    "El AAF no contiene ítems de audio/video",
                    "El archivo AAF seleccionado tiene las pistas definidas pero contiene 0 clips/ítems "
                    "de audio o video dentro de ellas (solo estructura de pistas/marcadores).\n\n"
                    "¿Deseas crear el archivo .rpp de todas formas?",
                )
                if not proceed_empty:
                    self.append_log("Creación de .rpp cancelada por el usuario (0 ítems en el AAF).")
                    return

            # 2. Si faltan archivos de audio/video, ofrecer buscarlos en una carpeta antes de crear el .rpp
            while media_report["missing_items"]:
                missing_cnt = len(media_report["missing_items"])
                found_cnt = len(media_report["found_items"])
                total_cnt = media_report["total_items"]
                sample_list = "\n".join(
                    f"• {m['name']} ({m['expected_path']})"
                    for m in media_report["missing_items"][:6]
                )
                if missing_cnt > 6:
                    sample_list += f"\n... y {missing_cnt - 6} más."

                locate_now = messagebox.askyesno(
                    "Ubicaciones de audio/video no encontradas",
                    f"Antes de crear el .rpp: se verificaron {found_cnt} de {total_cnt} ítems, "
                    f"pero {missing_cnt} archivo(s) de audio/video NO se encontraron en su ruta original:\n\n"
                    f"{sample_list}\n\n"
                    "¿Quieres seleccionar ahora la carpeta donde están guardados esos archivos para revincularlos?",
                )
                if locate_now:
                    chosen_dir = filedialog.askdirectory(
                        title="Seleccionar carpeta donde están los archivos de audio o video"
                    )
                    if chosen_dir:
                        self.media_dir_var.set(os.path.abspath(chosen_dir))
                        self.append_log(f"Buscando archivos faltantes en: {chosen_dir} ...")
                        media_report = verify_and_relink_project_media(
                            project_data,
                            search_dirs=[os.path.abspath(chosen_dir)],
                            log_callback=self.append_log,
                        )
                        continue

                # Si no eligió carpeta o quedaron archivos sin localizar, preguntar si desea crear el .rpp igualmente
                create_anyway = messagebox.askyesno(
                    "¿Crear sesión .rpp con ítems offline?",
                    f"Aún quedan {len(media_report['missing_items'])} archivo(s) sin localizar en el disco.\n\n"
                    "¿Deseas crear el archivo .rpp igualmente? (Los ítems se crearán en la línea de tiempo "
                    "de Reaper para que puedas verlos y revincularlos al abrir el proyecto).",
                )
                if not create_anyway:
                    self.append_log("Creación de .rpp cancelada por el usuario.")
                    return
                break

            written_path = RPPGenerator.write_rpp(rpp_abs, project_data, safe_mode=safe_mode)
            total_tracks = len(project_data.get("tracks", []))
            total_items = media_report["total_items"]
            found_cnt = len(media_report["found_items"])
            total_markers = len(project_data.get("markers", []))

            self.append_log(
                f"[OK] Sesión creada: {total_tracks} pista(s), {total_items} ítem(s) "
                f"({found_cnt} con archivo verificado), {total_markers} marcador(es)."
            )
            self.append_log(f"[OK] Guardado en: {written_path}")

            messagebox.showinfo(
                "Conversión completada",
                f"La sesión de Reaper se creó correctamente en:\n{written_path}\n\n"
                f"• Pistas: {total_tracks}\n"
                f"• Ítems creados: {total_items} ({found_cnt} archivos verificados en disco)\n"
                f"• Marcadores: {total_markers}",
            )
        except Exception as exc:
            self.append_log(f"[ERROR] {exc}")
            messagebox.showerror("Error en la conversión", str(exc))
        finally:
            self.btn_verify.configure(state=tk.NORMAL)
            self.btn_convert.configure(state=tk.NORMAL)


def main():
    arg_parser = argparse.ArgumentParser(
        description="Convierte un archivo AAF a una sesión de Reaper (.rpp). Sin argumentos abre la interfaz gráfica."
    )
    arg_parser.add_argument("aaf_file", nargs="?", help="Ruta al archivo .aaf de entrada")
    arg_parser.add_argument("-o", "--output", help="Ruta al archivo .rpp de salida (opcional)")
    arg_parser.add_argument(
        "--safe",
        action="store_true",
        help="Activa SafeMode (solo pistas de audio, sus ítems con posición/duración/offset/ganancia/fades y extracción WAV)",
    )
    arg_parser.add_argument(
        "-c",
        "--composition",
        type=int,
        default=0,
        help="Índice de la composición a importar (por defecto 0)",
    )
    arg_parser.add_argument(
        "-m",
        "--media-dir",
        action="append",
        default=[],
        help="Carpeta adicional donde buscar los archivos de audio o video vinculados",
    )
    arg_parser.add_argument(
        "--no-subfolder",
        action="store_true",
        help="Extrae los audios embebidos en la misma carpeta del .rpp en lugar de crear una subcarpeta",
    )

    args = arg_parser.parse_args()

    if args.aaf_file:
        try:
            convert_aaf_to_rpp(
                aaf_path=args.aaf_file,
                rpp_path=args.output,
                safe_mode=args.safe,
                composition_index=args.composition,
                sources_subfolder=not args.no_subfolder,
                extra_media_dirs=args.media_dir,
            )
        except Exception as exc:
            print(f"Error: {exc}", file=sys.stderr)
            sys.exit(1)
        return

    if not HAVE_TK:
        print(
            "Error: Tkinter no está disponible en este entorno. Puedes usar el script por línea de comandos: python aaf_to_rpp.py archivo.aaf",
            file=sys.stderr,
        )
        sys.exit(1)

    root = tk.Tk()
    AAFToReaperGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()