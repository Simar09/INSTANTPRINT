"""
Instant Print - local, one-time phone-to-Windows-printer transfer.

All application source intentionally lives in this one file.  It is designed
for Windows 10/11 and Python 3.12+.  See the deployment instructions supplied
with this project before exposing it on a network.
"""

from __future__ import annotations

import ctypes
import ipaddress
import json
import logging
import os
import queue
import secrets
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import uuid
import zipfile
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Callable, Iterator

import tkinter as tk
from tkinter import messagebox

DEPENDENCY_IMPORT_ERROR: ImportError | None = None
try:
    from flask import Flask, Response, jsonify, render_template_string, request
    from waitress import create_server
    import fitz  # PyMuPDF
    import qrcode
    from PIL import Image, ImageDraw, ImageFont, ImageOps, ImageSequence, ImageTk
    try:
        from PIL import ImageWin
    except ImportError:  # ImageWin is Windows-only.
        ImageWin = None  # type: ignore[assignment]
except ImportError as exc:
    # main() shows a GUI explanation even in a --noconsole PyInstaller build.
    DEPENDENCY_IMPORT_ERROR = exc
    Flask = Response = None  # type: ignore[assignment,misc]
    jsonify = render_template_string = request = create_server = None  # type: ignore[assignment]
    fitz = qrcode = None  # type: ignore[assignment]
    Image = ImageDraw = ImageFont = ImageOps = ImageSequence = ImageTk = ImageWin = None  # type: ignore[assignment]

try:
    import pywintypes
    import win32con
    import win32print
    import win32ui
except ImportError as exc:  # Reported at launch rather than failing obscurely.
    pywintypes = None  # type: ignore[assignment]
    win32con = None  # type: ignore[assignment]
    win32print = None  # type: ignore[assignment]
    win32ui = None  # type: ignore[assignment]
    WIN32_IMPORT_ERROR = exc
else:
    WIN32_IMPORT_ERROR = None


# ---------------------------------------------------------------------------
# Constants and small helpers
# ---------------------------------------------------------------------------

APP_NAME = "Instant Print"
WINDOW_BG = "#050505"
PANEL_BG = "#101010"
PANEL_ALT = "#161616"
PANEL_HOVER = "#1d1d1d"
TEXT = "#f5f5f5"
MUTED = "#ababab"
ACCENT = "#7c5cff"
ACCENT_HOVER = "#937cff"
SUCCESS = "#4dde9b"
WARNING = "#f2bf5b"
ERROR = "#ff6e73"
MAX_UPLOAD_BYTES_DEFAULT = 100 * 1024 * 1024
SESSION_SECONDS_DEFAULT = 10 * 60
TERMINAL_STATUS_GRACE_SECONDS = 75
MAX_TEXT_BYTES = 5 * 1024 * 1024
ALLOWED_EXTENSIONS = {
    "pdf", "png", "jpg", "jpeg", "bmp", "tif", "tiff", "txt",
    "doc", "docx", "xls", "xlsx", "ppt", "pptx",
}
IMAGE_EXTENSIONS = {"png", "jpg", "jpeg", "bmp", "tif", "tiff"}
OFFICE_EXTENSIONS = {"doc", "docx", "xls", "xlsx", "ppt", "pptx"}


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def clamp(value: int, low: int, high: int) -> int:
    return max(low, min(high, value))


def safe_error_message(exc: BaseException, fallback: str) -> str:
    """Return a short, non-path-bearing error suitable for the mobile page."""
    text = str(exc).replace("\r", " ").replace("\n", " ").strip()
    if not text or len(text) > 180 or "\\" in text or "/" in text:
        return fallback
    return text


def secure_delete(path: Path | None) -> None:
    """Best-effort overwrite/delete for an app-owned temp file.

    This cannot promise forensic erasure on SSDs, copy-on-write storage, or
    spooler-managed files.  It does ensure Instant Print does not retain the
    source upload in its own temporary directory after processing.
    """
    if path is None:
        return
    try:
        if path.exists() and path.is_file():
            size = path.stat().st_size
            with path.open("r+b", buffering=0) as handle:
                remaining = size
                block = b"\x00" * min(1024 * 1024, max(1, remaining))
                while remaining:
                    count = min(len(block), remaining)
                    handle.write(block[:count])
                    remaining -= count
                handle.flush()
                os.fsync(handle.fileno())
            path.unlink(missing_ok=True)
    except OSError:
        # The print spooler may retain a handle briefly.  A normal delete is
        # still attempted; no source path is logged.
        try:
            path.unlink(missing_ok=True)
        except OSError:
            logging.getLogger(APP_NAME).warning("Unable to remove an app temp file")


def format_bytes(value: int) -> str:
    units = ("B", "KB", "MB", "GB")
    amount = float(value)
    for unit in units:
        if amount < 1024 or unit == units[-1]:
            return f"{amount:.1f} {unit}" if unit != "B" else f"{int(amount)} B"
        amount /= 1024
    return f"{value} B"


def is_private_or_local_address(address: str) -> bool:
    try:
        parsed = ipaddress.ip_address(address.split("%", 1)[0])
    except ValueError:
        return False
    return bool(parsed.is_private or parsed.is_loopback or parsed.is_link_local)


def find_lan_ipv4() -> str | None:
    """Find a routable private IPv4 without placing localhost in a QR code."""
    candidates: list[str] = []
    probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        # UDP connect does not transmit data; it asks Windows which interface
        # it would use for a LAN/Internet route.
        probe.connect(("8.8.8.8", 80))
        candidates.append(probe.getsockname()[0])
    except OSError:
        pass
    finally:
        probe.close()
    try:
        candidates.extend(
            item[4][0]
            for item in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET)
        )
    except OSError:
        pass
    for address in dict.fromkeys(candidates):
        if address != "127.0.0.1" and is_private_or_local_address(address):
            return address
    return None


def set_dpi_awareness() -> None:
    if sys.platform != "win32":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)  # Per-monitor DPI aware.
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def setup_logging(temp_root: Path) -> logging.Logger:
    temp_root.mkdir(parents=True, exist_ok=True)
    logger = logging.getLogger(APP_NAME)
    if logger.handlers:
        return logger
    logger.setLevel(logging.INFO)
    handler = RotatingFileHandler(temp_root / "instant-print.log", maxBytes=750_000, backupCount=2, encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    logger.addHandler(handler)
    return logger


def cleanup_stale_temp_files(temp_root: Path) -> None:
    """Remove only files bearing this application's private prefix."""
    try:
        for path in temp_root.glob("ip_*"):
            if path.is_file():
                secure_delete(path)
    except OSError:
        pass


# ---------------------------------------------------------------------------
# Printer discovery and Windows print status
# ---------------------------------------------------------------------------

@dataclass(slots=True)
class PrinterInfo:
    name: str
    driver: str
    port: str
    connection: str
    status: str
    status_bits: int
    jobs: int
    is_default: bool
    available: bool
    attributes: int = 0


class PrinterManager:
    """Windows print-subsystem access.  All callers use background threads."""

    _unavailable_states = {
        "Offline", "Not Available", "Error", "Paper Out", "Paper Jam",
        "Door Open", "No Toner", "User Intervention Required",
    }

    def __init__(self, logger: logging.Logger) -> None:
        self.logger = logger

    @staticmethod
    def _require_windows() -> None:
        if sys.platform != "win32" or win32print is None:
            raise RuntimeError("Windows printer APIs are unavailable. Install pywin32 on Windows.")

    @staticmethod
    def _connection(port: str, name: str, driver: str) -> str:
        text = f"{port} {name} {driver}".lower()
        if port.startswith("\\\\"):
            return "Shared"
        if "usb" in text:
            return "USB"
        if any(value in text for value in ("bth", "bluetooth")):
            return "Bluetooth"
        if any(value in text for value in ("ip_", "tcp", "wsd", "http", "network", "wifi", "wi-fi")):
            return "Network"
        if any(value in text for value in ("file:", "portprompt", "xps", "onenote", "pdf", "fax")):
            return "Virtual"
        return "Unknown"

    @staticmethod
    def _normal_status(bits: int) -> str:
        if win32print is None:
            return "Unknown"
        ordered = (
            ("PRINTER_STATUS_PAPER_JAM", "Paper Jam"),
            ("PRINTER_STATUS_PAPER_OUT", "Paper Out"),
            ("PRINTER_STATUS_DOOR_OPEN", "Door Open"),
            ("PRINTER_STATUS_NO_TONER", "No Toner"),
            ("PRINTER_STATUS_USER_INTERVENTION", "User Intervention Required"),
            ("PRINTER_STATUS_OFFLINE", "Offline"),
            ("PRINTER_STATUS_NOT_AVAILABLE", "Not Available"),
            ("PRINTER_STATUS_ERROR", "Error"),
            ("PRINTER_STATUS_PAUSED", "Paused"),
            ("PRINTER_STATUS_WARMING_UP", "Warming Up"),
            ("PRINTER_STATUS_INITIALIZING", "Initializing"),
            ("PRINTER_STATUS_PRINTING", "Printing"),
            ("PRINTER_STATUS_PROCESSING", "Processing"),
            ("PRINTER_STATUS_BUSY", "Busy"),
            ("PRINTER_STATUS_TONER_LOW", "Low Toner"),
        )
        for constant, label in ordered:
            if bits & int(getattr(win32print, constant, 0)):
                return label
        # Windows defines 0 as an idle printer.  It is not an Offline flag.
        return "Ready"

    def _get_default_printer(self) -> str:
        try:
            return str(win32print.GetDefaultPrinter())
        except Exception:
            return ""

    def _build_info(self, name: str, default_name: str) -> PrinterInfo:
        self._require_windows()
        handle = win32print.OpenPrinter(name)
        try:
            detail = win32print.GetPrinter(handle, 2)
            # EnumJobs supplements cJobs for some driver configurations.
            try:
                jobs = len(win32print.EnumJobs(handle, 0, 999, 1))
            except Exception:
                jobs = int(detail.get("cJobs", 0) or 0)
            status_bits = int(detail.get("Status", 0) or 0)
            status = self._normal_status(status_bits)
            driver = str(detail.get("pDriverName") or "")
            port = str(detail.get("pPortName") or "")
            available = status not in self._unavailable_states
            return PrinterInfo(
                name=str(detail.get("pPrinterName") or name),
                driver=driver,
                port=port,
                connection=self._connection(port, name, driver),
                status=status,
                status_bits=status_bits,
                jobs=jobs,
                is_default=name.casefold() == default_name.casefold(),
                available=available,
                attributes=int(detail.get("Attributes", 0) or 0),
            )
        finally:
            win32print.ClosePrinter(handle)

    def enumerate_printers(self) -> list[PrinterInfo]:
        self._require_windows()
        flags = int(win32print.PRINTER_ENUM_LOCAL | win32print.PRINTER_ENUM_CONNECTIONS)
        try:
            rows = win32print.EnumPrinters(flags, None, 2)
        except pywintypes.error as exc:
            raise RuntimeError("Windows could not enumerate installed print queues.") from exc
        default_name = self._get_default_printer()
        names: list[str] = []
        for row in rows:
            if isinstance(row, dict):
                candidate = row.get("pPrinterName")
            else:
                candidate = row[2] if len(row) > 2 else None
            if candidate:
                names.append(str(candidate))
        printers: list[PrinterInfo] = []
        for name in dict.fromkeys(names):
            try:
                printers.append(self._build_info(name, default_name))
            except Exception:
                # An installed network queue may vanish between EnumPrinters and
                # OpenPrinter.  It is omitted rather than displayed as fake data.
                self.logger.info("A print queue became unavailable during enumeration")
        printers.sort(key=lambda item: (not item.is_default, item.name.casefold()))
        self.logger.info("%d printers detected", len(printers))
        return printers

    def inspect_printer(self, name: str) -> PrinterInfo:
        """Open a selected queue and retrieve a fresh, actionable state."""
        return self._build_info(name, self._get_default_printer())

    def get_capabilities(self, info: PrinterInfo) -> dict[str, Any]:
        """Return only settings that Windows says the driver can expose."""
        self._require_windows()
        capabilities: dict[str, Any] = {"duplex": False, "papers": []}
        try:
            duplex_flag = int(getattr(win32con, "DC_DUPLEX", 7))
            capabilities["duplex"] = bool(win32print.DeviceCapabilities(info.name, info.port, duplex_flag))
        except Exception:
            pass
        try:
            papers_flag = int(getattr(win32con, "DC_PAPERS", 2))
            names_flag = int(getattr(win32con, "DC_PAPERNAMES", 16))
            codes = win32print.DeviceCapabilities(info.name, info.port, papers_flag) or []
            names = win32print.DeviceCapabilities(info.name, info.port, names_flag) or []
            pairs = []
            for code, label in zip(codes, names):
                clean = str(label).strip()
                if clean:
                    pairs.append({"code": int(code), "label": clean[:80]})
            capabilities["papers"] = pairs[:30]
        except Exception:
            pass
        return capabilities

    def job_state(self, printer_name: str, job_id: int) -> str | None:
        """Return a spooler job state, None when it has left the queue."""
        self._require_windows()
        handle = win32print.OpenPrinter(printer_name)
        try:
            jobs = win32print.EnumJobs(handle, 0, 999, 1)
        finally:
            win32print.ClosePrinter(handle)
        for job in jobs:
            if int(job.get("JobId", -1)) != int(job_id):
                continue
            text = str(job.get("pStatus") or "").strip()
            bits = int(job.get("Status", 0) or 0)
            if text:
                return text[:80]
            if bits & int(getattr(win32print, "JOB_STATUS_ERROR", 0)):
                return "Error"
            if bits & int(getattr(win32print, "JOB_STATUS_OFFLINE", 0)):
                return "Offline"
            if bits & int(getattr(win32print, "JOB_STATUS_PAPEROUT", 0)):
                return "Paper Out"
            if bits & int(getattr(win32print, "JOB_STATUS_PAUSED", 0)):
                return "Paused"
            if bits & int(getattr(win32print, "JOB_STATUS_PRINTING", 0)):
                return "Printing"
            return "Queued"
        return None


# ---------------------------------------------------------------------------
# Session state.  No documents, tokens, or history are persisted.
# ---------------------------------------------------------------------------

@dataclass(slots=True)
class PrintSession:
    session_id: str
    token: str
    csrf: str
    printer: PrinterInfo
    capabilities: dict[str, Any]
    created_at: datetime
    expires_at: datetime
    state: str = "waiting"
    message: str = "Waiting for document..."
    document_kind: str = ""
    document_size: int = 0
    temp_path: Path | None = None
    job_id: int | None = None
    finished_at: datetime | None = None


class SessionManager:
    _active_states = {"waiting", "receiving", "received", "preparing", "queued", "printing"}
    _terminal_states = {"completed", "failed", "cancelled", "expired"}

    def __init__(self, logger: logging.Logger, session_seconds: Callable[[], int]) -> None:
        self._sessions: dict[str, PrintSession] = {}
        self._lock = threading.RLock()
        self._logger = logger
        self._session_seconds = session_seconds

    def create(self, printer: PrinterInfo, capabilities: dict[str, Any]) -> PrintSession:
        now = utcnow()
        session = PrintSession(
            session_id=uuid.uuid4().hex,
            token=secrets.token_urlsafe(32),  # 256-bit-class unpredictable bearer secret
            csrf=secrets.token_urlsafe(24),
            printer=printer,
            capabilities=capabilities,
            created_at=now,
            expires_at=now + timedelta(seconds=self._session_seconds()),
        )
        with self._lock:
            self._sessions[session.token] = session
        self._logger.info("Secure one-time session created")
        return session

    def _is_expired(self, session: PrintSession) -> bool:
        # The short-lived QR authorisation expires before a document is accepted.
        # Once an already-authorised upload is accepted, its one print transaction
        # is allowed to finish; it cannot be used to submit another upload.
        return utcnow() >= session.expires_at and session.state in {"waiting", "receiving"}

    def _expire_locked(self, session: PrintSession) -> Path | None:
        if session.state in self._active_states:
            session.state = "expired"
            session.message = "This QR session has expired. Generate a new QR code."
            session.finished_at = utcnow()
            self._logger.info("Session expired")
            return session.temp_path
        return None

    def get_for_page(self, token: str) -> PrintSession | None:
        cleanup: Path | None = None
        with self._lock:
            session = self._sessions.get(token)
            if session is None:
                return None
            cleanup = self._expire_locked(session) if self._is_expired(session) else None
            if cleanup:
                session.temp_path = None
            # A consumed/terminal QR must not open another printing page.
            if session.state not in self._active_states:
                result = None
            else:
                result = session
        if cleanup:
            secure_delete(cleanup)
        return result

    def status_snapshot(self, token: str) -> dict[str, Any] | None:
        cleanup: Path | None = None
        with self._lock:
            session = self._sessions.get(token)
            if session is None:
                return None
            if self._is_expired(session):
                cleanup = self._expire_locked(session)
                session.temp_path = None
            snapshot = {
                "state": session.state,
                "message": session.message,
                "terminal": session.state in self._terminal_states,
                "expires_in": max(0, int((session.expires_at - utcnow()).total_seconds())),
            }
        if cleanup:
            secure_delete(cleanup)
        return snapshot

    def claim_upload(self, token: str, csrf: str) -> PrintSession:
        cleanup: Path | None = None
        error: PermissionError | None = None
        with self._lock:
            session = self._sessions.get(token)
            if session is None:
                error = PermissionError("This QR session is no longer valid.")
            elif self._is_expired(session):
                cleanup = self._expire_locked(session)
                session.temp_path = None
                error = PermissionError("This QR session has expired. Generate a new QR code.")
            elif not secrets.compare_digest(csrf or "", session.csrf):
                error = PermissionError("This upload request could not be verified.")
            elif session.state != "waiting":
                error = PermissionError("This QR code is one-time and has already been used.")
            else:
                session.state = "receiving"
                session.message = "Document received. Preparing securely..."
        if cleanup:
            secure_delete(cleanup)
        if error:
            raise error
        return session

    def attach_file(self, token: str, path: Path, kind: str, size: int) -> bool:
        with self._lock:
            session = self._sessions.get(token)
            if session is None or session.state != "receiving":
                return False
            session.temp_path = path
            session.document_kind = kind
            session.document_size = size
            session.state = "received"
            session.message = "Document received. Preparing document..."
            self._logger.info("Upload accepted (%s, %s)", kind, format_bytes(size))
            return True

    def can_worker_continue(self, token: str) -> bool:
        with self._lock:
            session = self._sessions.get(token)
            return bool(session and session.state in {"received", "preparing", "queued", "printing"})

    def printer_name_for_worker(self, token: str) -> str | None:
        with self._lock:
            session = self._sessions.get(token)
            if session is None or session.state not in {"received", "preparing", "queued", "printing"}:
                return None
            return session.printer.name

    def update(self, token: str, state: str, message: str, job_id: int | None = None) -> None:
        with self._lock:
            session = self._sessions.get(token)
            if session is None or session.state in self._terminal_states:
                return
            session.state = state
            session.message = message[:180]
            if job_id is not None:
                session.job_id = job_id

    def finish(self, token: str, success: bool, message: str) -> None:
        with self._lock:
            session = self._sessions.get(token)
            if session is None:
                return
            if session.state in {"cancelled", "expired"}:
                return
            session.state = "completed" if success else "failed"
            session.message = message[:180]
            session.finished_at = utcnow()
            session.temp_path = None
        self._logger.info("Session %s", "completed" if success else "failed")

    def invalidate(self, token: str, message: str = "Session closed securely.") -> None:
        path: Path | None = None
        with self._lock:
            session = self._sessions.get(token)
            if session is None:
                return
            path = session.temp_path
            session.temp_path = None
            session.state = "cancelled"
            session.message = message
            session.finished_at = utcnow()
        secure_delete(path)
        self._logger.info("Session invalidated")

    def invalidate_all(self) -> None:
        with self._lock:
            tokens = list(self._sessions)
        for token in tokens:
            self.invalidate(token, "Instant Print was closed securely.")

    def cleanup(self) -> None:
        paths: list[Path] = []
        now = utcnow()
        with self._lock:
            remove: list[str] = []
            for token, session in self._sessions.items():
                if self._is_expired(session):
                    path = self._expire_locked(session)
                    if path:
                        paths.append(path)
                    session.temp_path = None
                if session.finished_at and (now - session.finished_at).total_seconds() >= TERMINAL_STATUS_GRACE_SECONDS:
                    if session.temp_path:
                        paths.append(session.temp_path)
                    remove.append(token)
            for token in remove:
                self._sessions.pop(token, None)
        for path in paths:
            secure_delete(path)


# ---------------------------------------------------------------------------
# Document validation, Office conversion, rasterisation, and real GDI print.
# ---------------------------------------------------------------------------

@dataclass(slots=True)
class PrintOptions:
    copies: int = 1
    orientation: str = "auto"
    color: str = "color"
    page_range: str = "all"
    duplex: str = "single"
    paper_code: int | None = None
    fit_to_page: bool = True


def parse_print_options(raw: str, capabilities: dict[str, Any]) -> PrintOptions:
    try:
        data = json.loads(raw or "{}")
    except (TypeError, json.JSONDecodeError) as exc:
        raise ValueError("The print settings were malformed.") from exc
    copies = clamp(int(data.get("copies", 1)), 1, 99)
    orientation = str(data.get("orientation", "auto")).lower()
    if orientation not in {"auto", "portrait", "landscape"}:
        orientation = "auto"
    color = str(data.get("color", "color")).lower()
    if color not in {"color", "grayscale"}:
        color = "color"
    page_range = str(data.get("page_range", "all")).strip().lower()
    if len(page_range) > 120:
        raise ValueError("The page range is too long.")
    duplex = str(data.get("duplex", "single")).lower()
    if duplex not in {"single", "long", "short"} or not capabilities.get("duplex"):
        duplex = "single"
    accepted_papers = {int(item["code"]) for item in capabilities.get("papers", []) if "code" in item}
    paper_value = data.get("paper_code")
    paper_code = int(paper_value) if str(paper_value).isdigit() and int(paper_value) in accepted_papers else None
    return PrintOptions(
        copies=copies,
        orientation=orientation,
        color=color,
        page_range=page_range or "all",
        duplex=duplex,
        paper_code=paper_code,
        fit_to_page=bool(data.get("fit_to_page", True)),
    )


def page_numbers(specification: str, total: int) -> list[int]:
    if total < 1:
        raise ValueError("The document does not contain printable pages.")
    if specification in {"", "all"}:
        return list(range(total))
    chosen: set[int] = set()
    for raw_piece in specification.split(","):
        piece = raw_piece.strip()
        if not piece:
            continue
        if "-" in piece:
            start_text, end_text = (part.strip() for part in piece.split("-", 1))
            if not start_text.isdigit() or not end_text.isdigit():
                raise ValueError("Use page ranges such as 1-3,5.")
            start, end = int(start_text), int(end_text)
            if start < 1 or end < start or end > total:
                raise ValueError(f"Choose pages between 1 and {total}.")
            chosen.update(range(start - 1, end))
        else:
            if not piece.isdigit() or not 1 <= int(piece) <= total:
                raise ValueError(f"Choose pages between 1 and {total}.")
            chosen.add(int(piece) - 1)
    if not chosen:
        raise ValueError("Choose at least one page to print.")
    return sorted(chosen)


def validate_document(path: Path, extension: str) -> str:
    """Check extension and simple format signatures before processing untrusted input."""
    if extension not in ALLOWED_EXTENSIONS:
        raise ValueError("That document type is not supported. Please upload a PDF, image, text, or Office document.")
    with path.open("rb") as handle:
        header = handle.read(4096)
    if extension == "pdf":
        if not header.startswith(b"%PDF-"):
            raise ValueError("The selected file is not a valid PDF.")
        try:
            document = fitz.open(path)
            try:
                if document.page_count < 1:
                    raise ValueError("The PDF does not contain printable pages.")
            finally:
                document.close()
        except ValueError:
            raise
        except Exception as exc:
            raise ValueError("The PDF could not be opened safely.") from exc
        return "PDF"
    if extension in IMAGE_EXTENSIONS:
        try:
            with Image.open(path) as image:
                image.verify()
        except Exception as exc:
            raise ValueError("The selected image is damaged or unsupported.") from exc
        return "Image"
    if extension == "txt":
        if b"\x00" in header:
            raise ValueError("The selected text file appears to be binary data.")
        return "Text"
    if extension in {"doc", "xls", "ppt"}:
        if not header.startswith(b"\xd0\xcf\x11\xe0"):
            raise ValueError("The selected legacy Office file is not valid.")
    else:
        if not zipfile.is_zipfile(path):
            raise ValueError("The selected Office file is not valid.")
    return "Office"


class DocumentProcessor:
    def __init__(self, logger: logging.Logger, temp_root: Path) -> None:
        self.logger = logger
        self.temp_root = temp_root

    def _convert_office_to_pdf(self, source: Path, extension: str) -> Path:
        """Use installed desktop Office only; macros are disabled where exposed."""
        try:
            import win32com.client  # Imported only for Office-format requests.
        except ImportError as exc:
            raise RuntimeError("This document format requires a compatible Microsoft Office desktop renderer. Please upload a PDF instead.") from exc
        target = self.temp_root / f"ip_{secrets.token_hex(20)}.pdf"
        app: Any = None
        document: Any = None
        try:
            if extension in {"doc", "docx"}:
                app = win32com.client.DispatchEx("Word.Application")
                app.Visible = False
                app.DisplayAlerts = 0
                try:
                    app.AutomationSecurity = 3  # msoAutomationSecurityForceDisable
                except Exception:
                    pass
                document = app.Documents.Open(str(source), ReadOnly=True, AddToRecentFiles=False, ConfirmConversions=False, NoEncodingDialog=True)
                document.ExportAsFixedFormat(str(target), 17)  # wdExportFormatPDF
            elif extension in {"xls", "xlsx"}:
                app = win32com.client.DispatchEx("Excel.Application")
                app.Visible = False
                app.DisplayAlerts = False
                try:
                    app.AutomationSecurity = 3
                except Exception:
                    pass
                document = app.Workbooks.Open(str(source), ReadOnly=True, UpdateLinks=0, IgnoreReadOnlyRecommended=True)
                document.ExportAsFixedFormat(0, str(target))  # xlTypePDF
            else:
                app = win32com.client.DispatchEx("PowerPoint.Application")
                document = app.Presentations.Open(str(source), ReadOnly=True, Untitled=False, WithWindow=False)
                document.SaveAs(str(target), 32)  # ppSaveAsPDF
            if not target.exists() or target.stat().st_size == 0:
                raise RuntimeError("The compatible Office renderer did not create a printable PDF.")
            return target
        except RuntimeError:
            raise
        except Exception as exc:
            raise RuntimeError("This Office document could not be prepared for printing. Please upload a PDF instead.") from exc
        finally:
            if document is not None:
                try:
                    document.Close(False)
                except Exception:
                    try:
                        document.Close()
                    except Exception:
                        pass
            if app is not None:
                try:
                    app.Quit()
                except Exception:
                    pass

    @staticmethod
    def _text_images(source: Path) -> list[Image.Image]:
        if source.stat().st_size > MAX_TEXT_BYTES:
            raise RuntimeError("Text documents over 5 MB should be converted to PDF before printing.")
        text = source.read_text(encoding="utf-8", errors="replace")
        try:
            font = ImageFont.truetype("arial.ttf", 22)
        except OSError:
            font = ImageFont.load_default()
        canvas_width, canvas_height = 1275, 1650  # 8.5x11 at 150 dpi
        margin, line_height = 80, 34
        max_lines = (canvas_height - margin * 2) // line_height
        # Wrap conservatively; physical scaling is handled at draw time.
        wrapped: list[str] = []
        for line in text.splitlines() or [""]:
            while len(line) > 95:
                wrapped.append(line[:95])
                line = line[95:]
            wrapped.append(line)
        pages: list[Image.Image] = []
        for offset in range(0, len(wrapped), max_lines):
            page = Image.new("RGB", (canvas_width, canvas_height), "white")
            draw = ImageDraw.Draw(page)
            y = margin
            for line in wrapped[offset:offset + max_lines]:
                draw.text((margin, y), line, fill="black", font=font)
                y += line_height
            pages.append(page)
        return pages or [Image.new("RGB", (canvas_width, canvas_height), "white")]

    def _page_count(self, source: Path, kind: str) -> int:
        if kind == "PDF":
            document = fitz.open(source)
            try:
                return document.page_count
            finally:
                document.close()
        if kind == "Image":
            with Image.open(source) as image:
                return int(getattr(image, "n_frames", 1))
        if kind == "Text":
            return len(self._text_images(source))
        raise RuntimeError("Unsupported document processor.")

    def _image_for_page(self, source: Path, kind: str, index: int) -> Image.Image:
        if kind == "PDF":
            document = fitz.open(source)
            try:
                page = document.load_page(index)
                pixmap = page.get_pixmap(matrix=fitz.Matrix(2.0, 2.0), colorspace=fitz.csRGB, alpha=False)
                return Image.frombytes("RGB", (pixmap.width, pixmap.height), pixmap.samples)
            finally:
                document.close()
        if kind == "Image":
            with Image.open(source) as image:
                image.seek(index)
                return ImageOps.exif_transpose(image.copy()).convert("RGB")
        if kind == "Text":
            pages = self._text_images(source)
            return pages[index]
        raise RuntimeError("Unsupported document processor.")

    @staticmethod
    def _apply_devmode(printer_name: str, options: PrintOptions) -> Any:
        """Best-effort driver configuration; printing still works on strict drivers."""
        handle = win32print.OpenPrinter(printer_name)
        try:
            devmode = win32print.GetPrinter(handle, 2).get("pDevMode")
            if devmode is None:
                return None
            def enable(field_name: str) -> None:
                try:
                    devmode.Fields = int(devmode.Fields) | int(getattr(win32con, field_name, 0))
                except Exception:
                    # Some drivers expose a read-only DEVMODE copy.  Assigning
                    # the value below remains worthwhile and is driver-dependent.
                    pass
            if options.orientation == "portrait":
                enable("DM_ORIENTATION")
                devmode.Orientation = int(getattr(win32con, "DMORIENT_PORTRAIT", 1))
            elif options.orientation == "landscape":
                enable("DM_ORIENTATION")
                devmode.Orientation = int(getattr(win32con, "DMORIENT_LANDSCAPE", 2))
            if options.duplex == "long":
                enable("DM_DUPLEX")
                devmode.Duplex = int(getattr(win32con, "DMDUP_VERTICAL", 2))
            elif options.duplex == "short":
                enable("DM_DUPLEX")
                devmode.Duplex = int(getattr(win32con, "DMDUP_HORIZONTAL", 3))
            elif options.duplex == "single":
                enable("DM_DUPLEX")
                devmode.Duplex = int(getattr(win32con, "DMDUP_SIMPLEX", 1))
            if options.paper_code is not None:
                enable("DM_PAPERSIZE")
                devmode.PaperSize = options.paper_code
            if options.color == "grayscale":
                enable("DM_COLOR")
                devmode.Color = int(getattr(win32con, "DMCOLOR_MONOCHROME", 1))
            else:
                enable("DM_COLOR")
                devmode.Color = int(getattr(win32con, "DMCOLOR_COLOR", 2))
            return devmode
        finally:
            win32print.ClosePrinter(handle)

    @staticmethod
    def _printer_dc(printer_name: str, devmode: Any) -> Any:
        if ImageWin is None:
            raise RuntimeError("Windows imaging support is unavailable.")
        dc = win32ui.CreateDC()
        if devmode is not None:
            try:
                dc.CreateDC("WINSPOOL", printer_name, None, devmode)
                return dc
            except Exception:
                # Some drivers reject a copied DEVMODE.  The default printer
                # settings still produce a real print job rather than a fake one.
                try:
                    dc.DeleteDC()
                except Exception:
                    pass
                dc = win32ui.CreateDC()
        dc.CreatePrinterDC(printer_name)
        return dc

    @staticmethod
    def _draw_image(dc: Any, image: Image.Image, options: PrintOptions) -> None:
        horizontal = dc.GetDeviceCaps(int(getattr(win32con, "HORZRES", 8)))
        vertical = dc.GetDeviceCaps(int(getattr(win32con, "VERTRES", 10)))
        if horizontal <= 0 or vertical <= 0:
            raise RuntimeError("The selected printer did not provide printable page dimensions.")
        source = image.convert("L").convert("RGB") if options.color == "grayscale" else image.convert("RGB")
        if not options.fit_to_page:
            target_width, target_height = min(source.width, horizontal), min(source.height, vertical)
        else:
            scale = min(horizontal / source.width, vertical / source.height)
            target_width = max(1, int(source.width * scale))
            target_height = max(1, int(source.height * scale))
        left = max(0, (horizontal - target_width) // 2)
        top = max(0, (vertical - target_height) // 2)
        ImageWin.Dib(source).draw(dc.GetHandleOutput(), (left, top, left + target_width, top + target_height))

    def print_document(
        self,
        printer_name: str,
        source: Path,
        extension: str,
        kind: str,
        options: PrintOptions,
        progress: Callable[[str, str, int | None], None],
    ) -> int:
        """Render and submit a Windows GDI spooler job.  Returns a real job ID."""
        self.logger.info("Preparing document for print")
        converted: Path | None = None
        active_source, active_kind = source, kind
        try:
            if kind == "Office":
                progress("preparing", "Preparing Office document...", None)
                converted = self._convert_office_to_pdf(source, extension)
                active_source, active_kind = converted, "PDF"
            total = self._page_count(active_source, active_kind)
            selected_pages = page_numbers(options.page_range, total)
            progress("preparing", "Preparing document...", None)
            devmode = self._apply_devmode(printer_name, options)
            dc = self._printer_dc(printer_name, devmode)
            document_started = False
            try:
                job_id = int(dc.StartDoc("Instant Print"))
                document_started = True
                progress("queued", "Document sent to the Windows print queue.", job_id)
                for copy_number in range(options.copies):
                    for page_index in selected_pages:
                        image = self._image_for_page(active_source, active_kind, page_index)
                        try:
                            dc.StartPage()
                            self._draw_image(dc, image, options)
                            dc.EndPage()
                        finally:
                            image.close()
                dc.EndDoc()
                document_started = False
                self.logger.info("Real Windows spooler job submitted")
                return job_id
            except Exception:
                if document_started:
                    try:
                        dc.AbortDoc()
                    except Exception:
                        pass
                raise
            finally:
                try:
                    dc.DeleteDC()
                except Exception:
                    pass
        finally:
            secure_delete(converted)


class PrintManager:
    def __init__(self, sessions: SessionManager, printers: PrinterManager, processor: DocumentProcessor, logger: logging.Logger) -> None:
        self.sessions = sessions
        self.printers = printers
        self.processor = processor
        self.logger = logger
        self._executor = ThreadPoolExecutor(max_workers=2, thread_name_prefix="InstantPrintWorker")
        self._stopped = threading.Event()

    def submit(self, token: str, source: Path, extension: str, kind: str, options: PrintOptions) -> None:
        if self._stopped.is_set():
            secure_delete(source)
            self.sessions.finish(token, False, "Instant Print is closing. The document was removed.")
            return
        self._executor.submit(self._worker, token, source, extension, kind, options)

    def _worker(self, token: str, source: Path, extension: str, kind: str, options: PrintOptions) -> None:
        try:
            if not self.sessions.can_worker_continue(token):
                return
            self.sessions.update(token, "preparing", "Verifying selected printer...", None)
            printer_name = self.sessions.printer_name_for_worker(token)
            if not printer_name:
                return
            info = self.printers.inspect_printer(printer_name)
            if not info.available:
                raise RuntimeError(f"The selected printer is {info.status.lower()}. Fix the printer and generate a new QR code.")
            job_id = self.processor.print_document(
                printer_name, source, extension, kind, options,
                lambda state, message, job: self.sessions.update(token, state, message, job),
            )
            # The app-owned upload can be destroyed as soon as GDI has accepted
            # the rendered pages; the Windows spooler owns its separate job data.
            secure_delete(source)
            self._monitor_spooler(token, printer_name, job_id)
        except Exception as exc:
            secure_delete(source)
            self.logger.exception("Print processing failed without logging document data")
            self.sessions.finish(token, False, safe_error_message(exc, "The document could not be printed. Check the printer and try again."))

    def _monitor_spooler(self, token: str, printer_name: str, job_id: int) -> None:
        # Spooler removal commonly means the printer accepted the job.  It is not
        # a claim that paper has physically emerged (many devices cannot report it).
        seen = False
        for _ in range(45):
            if self._stopped.is_set() or not self.sessions.can_worker_continue(token):
                return
            try:
                state = self.printers.job_state(printer_name, job_id)
            except Exception:
                state = "Queued"
            if state is None:
                message = "Print job completed and temporary document data was removed." if seen else "Print job sent successfully and temporary document data was removed."
                self.sessions.finish(token, True, message)
                return
            seen = True
            lowered = state.casefold()
            if any(word in lowered for word in ("error", "offline", "paper", "blocked", "deleted")):
                self.sessions.finish(token, False, f"The Windows print queue reported: {state}.")
                return
            self.sessions.update(token, "printing" if "print" in lowered else "queued", f"Windows print queue: {state}.", job_id)
            time.sleep(1)
        self.sessions.finish(token, True, "Print job remains with the Windows print queue. Temporary document data was removed.")

    def shutdown(self) -> None:
        self._stopped.set()
        self._executor.shutdown(wait=False, cancel_futures=True)


# ---------------------------------------------------------------------------
# Embedded mobile web app.  There are intentionally no document GET endpoints.
# ---------------------------------------------------------------------------

MOBILE_PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="dark">
<title>Instant Print</title>
<style>
:root{color-scheme:dark;--bg:#050505;--panel:#111;--panel2:#181818;--text:#f5f5f5;--muted:#aaa;--accent:#7c5cff;--good:#4dde9b;--bad:#ff747b;--line:#2b2b2b}*{box-sizing:border-box}body{margin:0;background:radial-gradient(ellipse 110% 55% at 50% -5%,#211c45 0%,var(--bg) 44%);color:var(--text);font:16px -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;min-height:100vh}.shell{width:min(100%,560px);margin:auto;padding:22px 16px 42px}.brand{display:flex;align-items:center;gap:10px;font-weight:800;letter-spacing:.2px;font-size:20px}.bolt{display:grid;place-items:center;background:linear-gradient(145deg,#9b89ff,#6848ff);width:32px;height:32px;border-radius:10px;box-shadow:0 8px 25px #664cff55}.eyebrow{color:#b8adff;text-transform:uppercase;letter-spacing:1.4px;font-size:11px;font-weight:750;margin:40px 0 9px}.printer{font-size:28px;line-height:1.14;margin:0 0 8px;overflow-wrap:anywhere}.sub{color:var(--muted);line-height:1.5;margin:0 0 27px}.card{background:linear-gradient(145deg,#171717,#101010);border:1px solid var(--line);border-radius:22px;padding:18px;box-shadow:0 20px 40px #0005;margin:14px 0}.drop{border:1.5px dashed #5b4ea6;border-radius:17px;padding:30px 12px;text-align:center;background:#121120;cursor:pointer;transition:.18s}.drop.drag,.drop:hover{border-color:#a699ff;background:#1a1831}.plus{font-size:30px;color:#b9aeff;margin-bottom:8px}.hint{font-size:13px;color:var(--muted);margin-top:6px}input[type=file]{display:none}.file{display:none;align-items:center;justify-content:space-between;gap:12px;margin-top:14px;padding:13px;background:var(--panel2);border-radius:14px}.file.show{display:flex}.file-name{font-weight:650;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.file-meta{color:var(--muted);font-size:13px;margin-top:3px}.plain{border:0;background:transparent;color:#c4bcff;font:inherit;padding:8px;cursor:pointer}.row{display:flex;justify-content:space-between;align-items:center;gap:16px;padding:14px 0;border-bottom:1px solid var(--line)}.row:last-child{border:0;padding-bottom:0}.row label{font-weight:650}.row small{display:block;color:var(--muted);font-weight:400;margin-top:3px}.stepper{display:flex;align-items:center;gap:13px}.stepper button{width:33px;height:33px;border-radius:11px;background:#292929;color:#fff;border:1px solid #3b3b3b;font-size:20px}.value{min-width:15px;text-align:center;font-weight:750}select,input[type=text]{background:#222;border:1px solid #3b3b3b;border-radius:10px;color:#fff;padding:10px;font:inherit;max-width:190px}select{width:155px}.range{display:none;margin:0 0 10px}.range.show{display:block}.range input{width:100%;max-width:none}.button{width:100%;margin-top:20px;border:0;border-radius:15px;padding:16px;background:linear-gradient(135deg,#927dff,#6545ef);box-shadow:0 13px 30px #6144e655;color:white;font:750 17px -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;cursor:pointer}.button:disabled{opacity:.45;cursor:not-allowed}.progress-wrap{display:none;margin-top:16px}.progress-wrap.show{display:block}.track{height:8px;border-radius:9px;background:#2a2a2a;overflow:hidden;margin:10px 0}.bar{height:100%;width:0;background:linear-gradient(90deg,#886fff,#c0b5ff);transition:width .2s}.status{display:none;text-align:center;padding:19px 12px;line-height:1.5}.status.show{display:block}.status-icon{font-size:29px;margin-bottom:5px}.status.good .status-icon{color:var(--good)}.status.bad .status-icon{color:var(--bad)}.foot{color:#777;font-size:12px;line-height:1.5;text-align:center;margin:23px 7px 0}@media(max-width:350px){.printer{font-size:24px}.row{align-items:flex-start;flex-direction:column;gap:8px}select{width:100%;max-width:none}}
</style>
</head>
<body><main class="shell">
<div class="brand"><span class="bolt">⚡</span>Instant Print</div>
<div class="eyebrow">Connected securely to</div><h1 class="printer">{{ printer_name }}</h1>
<p class="sub">Choose a document and its print settings. Your file is removed from Instant Print after it is sent to the Windows print queue.</p>
<section class="card" id="form-card">
 <label class="drop" id="drop" for="document"><div class="plus">＋</div><strong>Add Document</strong><div class="hint">Tap to browse files</div></label>
 <input id="document" type="file" accept=".pdf,.png,.jpg,.jpeg,.bmp,.tif,.tiff,.txt,.doc,.docx,.xls,.xlsx,.ppt,.pptx">
 <div class="file" id="file-info"><div style="min-width:0"><div class="file-name" id="file-name"></div><div class="file-meta" id="file-meta"></div></div><button class="plain" id="remove" type="button">Remove</button></div>
 <div class="row"><label>Copies<small>1 to 99</small></label><div class="stepper"><button id="minus" type="button" aria-label="Fewer copies">−</button><span class="value" id="copies">1</span><button id="plus" type="button" aria-label="More copies">＋</button></div></div>
 <div class="row"><label for="orientation">Orientation</label><select id="orientation"><option value="auto">Auto</option><option value="portrait">Portrait</option><option value="landscape">Landscape</option></select></div>
 <div class="row"><label for="color">Color</label><select id="color"><option value="color">Color</option><option value="grayscale">Black &amp; White</option></select></div>
 <div class="row"><label for="pages">Pages<small>All, or a range such as 1-3,5</small></label><select id="pages"><option value="all">All</option><option value="custom">Custom</option></select></div>
 <div class="range" id="range"><input id="page-range" maxlength="120" type="text" inputmode="text" placeholder="Example: 1-3,5"></div>
 {% if capabilities.duplex %}<div class="row"><label for="duplex">Sides<small>Reported by this printer driver</small></label><select id="duplex"><option value="single">Single-sided</option><option value="long">Double-sided (long edge)</option><option value="short">Double-sided (short edge)</option></select></div>{% endif %}
 {% if capabilities.papers %}<div class="row"><label for="paper">Paper size<small>Reported by this printer driver</small></label><select id="paper"><option value="">Driver default</option>{% for paper in capabilities.papers %}<option value="{{ paper.code }}">{{ paper.label }}</option>{% endfor %}</select></div>{% endif %}
 <div class="row"><label for="fit">Fit to page<small>Preserves document proportions</small></label><input id="fit" type="checkbox" checked style="accent-color:#8a74ff;width:21px;height:21px"></div>
 <button class="button" id="print" type="button" disabled>Print Document</button>
 <div class="progress-wrap" id="progress"><strong id="progress-label">Uploading</strong><div class="track"><div class="bar" id="bar"></div></div><span id="percent">0%</span></div>
 <div class="status" id="status"><div class="status-icon" id="status-icon">●</div><strong id="status-title">Preparing</strong><div class="hint" id="status-message"></div></div>
</section>
<p class="foot">Local network transfer only. Keep this phone and the Windows PC on the same network. Instant Print does not provide a document download or preview link.</p>
</main>
<script>
(() => {"use strict";
 const token={{ token|tojson }}, csrf={{ csrf|tojson }};
 let file=null,copies=1,polling=false;
 const $=id=>document.getElementById(id), drop=$("drop"), input=$("document"), print=$("print"), card=$("form-card"), status=$("status"), progress=$("progress");
 const bytes=n=>n<1024?n+" B":n<1048576?(n/1024).toFixed(1)+" KB":(n/1048576).toFixed(1)+" MB";
 const setFile=f=>{file=f||null; $("file-info").classList.toggle("show",!!file); if(file){$("file-name").textContent=file.name;$("file-meta").textContent=bytes(file.size)+" · "+(file.type||"Document");} print.disabled=!file;};
 input.addEventListener("change",()=>setFile(input.files[0])); $("remove").onclick=()=>{input.value="";setFile(null)};
 ["dragenter","dragover"].forEach(e=>drop.addEventListener(e,event=>{event.preventDefault();drop.classList.add("drag")})); ["dragleave","drop"].forEach(e=>drop.addEventListener(e,event=>{event.preventDefault();drop.classList.remove("drag")})); drop.addEventListener("drop",e=>{if(e.dataTransfer.files.length){input.files=e.dataTransfer.files;setFile(input.files[0]);}});
 const drawCopies=()=>$("copies").textContent=copies; $("minus").onclick=()=>{copies=Math.max(1,copies-1);drawCopies()}; $("plus").onclick=()=>{copies=Math.min(99,copies+1);drawCopies()};
 $("pages").onchange=()=>$("range").classList.toggle("show",$("pages").value==="custom");
 const show=(title,message,kind="")=>{status.className="status show "+kind;$("status-title").textContent=title;$("status-message").textContent=message;$("status-icon").textContent=kind==="good"?"✓":kind==="bad"?"!":"●";};
 const disable=()=>{print.disabled=true;input.disabled=true;document.querySelectorAll("select,input,button").forEach(x=>{if(x.id!=="status")x.disabled=true});};
 const poll=()=>{if(polling)return;polling=true;const tick=async()=>{try{const r=await fetch(`/s/${encodeURIComponent(token)}/status`,{cache:"no-store"});if(!r.ok)throw new Error();const data=await r.json();let kind=data.state==="completed"?"good":data.state==="failed"||data.state==="expired"?"bad":"";show(data.state==="completed"?"Print job sent":data.state==="failed"?"Print failed":data.state==="expired"?"Session expired":"Instant Print",data.message,kind);if(data.terminal){disable();return;}setTimeout(tick,1000);}catch(e){show("Connection lost","Check that your phone and PC remain on the same local network.","bad");}};tick();};
 print.onclick=()=>{if(!file)return;const range=$("pages").value==="custom"?$("page-range").value:"all";const options={copies,orientation:$("orientation").value,color:$("color").value,page_range:range,duplex:$("duplex")?$("duplex").value:"single",paper_code:$("paper")?$("paper").value:"",fit_to_page:$("fit").checked};const data=new FormData();data.append("csrf",csrf);data.append("document",file);data.append("options",JSON.stringify(options));disable();progress.classList.add("show");$("progress-label").textContent="Uploading securely";const xhr=new XMLHttpRequest();xhr.open("POST",`/s/${encodeURIComponent(token)}/print`);xhr.upload.onprogress=e=>{if(e.lengthComputable){let p=Math.round(e.loaded/e.total*100);$("bar").style.width=p+"%";$("percent").textContent=p+"%";}};xhr.onload=()=>{progress.classList.remove("show");if(xhr.status===202){show("Document received","Preparing document...","");poll();}else{let msg="The document could not be accepted.";try{msg=JSON.parse(xhr.responseText).error||msg}catch(e){}show("Print not started",msg,"bad");}};xhr.onerror=()=>{progress.classList.remove("show");show("Upload interrupted","Check the local network and generate a new QR code.","bad")};xhr.send(data);};
 {% if state != "waiting" %} show("Instant Print",{{ initial_message|tojson }},""); poll(); {% endif %}
})();
</script></body></html>"""


class LocalPrintServer:
    def __init__(
        self,
        sessions: SessionManager,
        print_manager: PrintManager,
        temp_root: Path,
        max_upload: Callable[[], int],
        logger: logging.Logger,
    ) -> None:
        self.sessions = sessions
        self.print_manager = print_manager
        self.temp_root = temp_root
        self.max_upload = max_upload
        self.logger = logger
        self.port: int | None = None
        self._server: Any = None
        self._thread: threading.Thread | None = None
        self._stopping = threading.Event()
        self._rate_lock = threading.Lock()
        self._hits: dict[str, deque[float]] = defaultdict(deque)
        self.flask = Flask(APP_NAME)
        self.flask.config.update(MAX_CONTENT_LENGTH=MAX_UPLOAD_BYTES_DEFAULT, PROPAGATE_EXCEPTIONS=False)
        self._configure_routes()

    def _allowed_client(self) -> bool:
        return is_private_or_local_address(request.remote_addr or "")

    def _rate_allowed(self) -> bool:
        remote = request.remote_addr or "unknown"
        now = time.monotonic()
        with self._rate_lock:
            hits = self._hits[remote]
            while hits and now - hits[0] > 60:
                hits.popleft()
            if len(hits) >= 90:
                return False
            hits.append(now)
        return True

    @staticmethod
    def _error_page(title: str, detail: str) -> Response:
        html = f"""<!doctype html><meta name=viewport content='width=device-width,initial-scale=1'>
        <title>Instant Print</title><body style='margin:0;background:#050505;color:#f5f5f5;font:16px Segoe UI,sans-serif'>
        <main style='max-width:480px;margin:15vh auto;padding:28px'><div style='color:#b8adff;font-weight:700'>INSTANT PRINT</div>
        <h1>{title}</h1><p style='color:#aaa;line-height:1.6'>{detail}</p></main></body>"""
        return Response(html, status=404, content_type="text/html; charset=utf-8")

    def _configure_routes(self) -> None:
        app = self.flask

        @app.before_request
        def network_guard() -> Response | None:
            if self._stopping.is_set():
                return jsonify(error="Instant Print is closing."), 503
            if not self._allowed_client():
                return jsonify(error="Instant Print accepts local-network connections only."), 403
            if not self._rate_allowed():
                return jsonify(error="Too many requests. Please wait and try again."), 429
            return None

        @app.after_request
        def security_headers(response: Response) -> Response:
            response.headers["Cache-Control"] = "no-store, max-age=0"
            response.headers["Pragma"] = "no-cache"
            response.headers["X-Content-Type-Options"] = "nosniff"
            response.headers["X-Frame-Options"] = "DENY"
            response.headers["Referrer-Policy"] = "no-referrer"
            response.headers["Permissions-Policy"] = "camera=(), geolocation=(), microphone=()"
            response.headers["Content-Security-Policy"] = "default-src 'self'; base-uri 'none'; img-src 'self' data:; style-src 'unsafe-inline'; script-src 'unsafe-inline'; form-action 'self'; frame-ancestors 'none'"
            return response

        @app.errorhandler(413)
        def too_large(_: BaseException) -> tuple[Response, int]:
            return jsonify(error=f"This document exceeds the {format_bytes(self.max_upload())} upload limit."), 413

        @app.errorhandler(Exception)
        def generic_error(exc: BaseException) -> tuple[Response, int]:
            self.logger.exception("Local web request failed")
            if request.path.endswith("/print") or request.path.endswith("/status"):
                return jsonify(error="Instant Print could not process that request."), 500
            return self._error_page("Page unavailable", "This QR session is unavailable. Generate a new QR code on the Windows computer."), 404

        @app.get("/")
        def root() -> Response:
            return self._error_page("A secure QR code is required", "Generate a session from the Instant Print Windows application." )

        @app.get("/s/<token>")
        def mobile_page(token: str) -> Response:
            session = self.sessions.get_for_page(token)
            if session is None:
                return self._error_page("This QR session is no longer valid", "Generate a new QR code on the Windows computer and scan it again.")
            return Response(render_template_string(
                MOBILE_PAGE,
                token=token,
                csrf=session.csrf,
                printer_name=session.printer.name,
                capabilities=session.capabilities,
                state=session.state,
                initial_message=session.message,
            ), content_type="text/html; charset=utf-8")

        @app.get("/s/<token>/status")
        def mobile_status(token: str) -> tuple[Response, int] | Response:
            status = self.sessions.status_snapshot(token)
            if status is None:
                return jsonify(error="This QR session is no longer valid."), 404
            return jsonify(status)

        @app.post("/s/<token>/print")
        def upload_and_print(token: str) -> tuple[Response, int] | Response:
            # Flask checks Content-Length against its configured cap first.  The
            # current setting is refreshed here so the desktop setting takes effect.
            app.config["MAX_CONTENT_LENGTH"] = self.max_upload()
            csrf = str(request.form.get("csrf") or "")
            try:
                session = self.sessions.claim_upload(token, csrf)
            except PermissionError as exc:
                return jsonify(error=str(exc)), 403
            uploaded = request.files.get("document")
            if uploaded is None or not uploaded.filename:
                self.sessions.finish(token, False, "No document was received. Generate a new QR code and try again.")
                return jsonify(error="Choose a document before printing."), 400
            extension = uploaded.filename.rsplit(".", 1)[-1].lower() if "." in uploaded.filename else ""
            if extension not in ALLOWED_EXTENSIONS:
                self.sessions.finish(token, False, "Unsupported document type.")
                return jsonify(error="That document type is not supported. Please upload a PDF, image, text, or Office document."), 415
            target = self.temp_root / f"ip_{secrets.token_hex(24)}.{extension}"
            try:
                # The controlled filename is generated here; the user filename is
                # never used as a path or retained in session metadata/logs.
                total = 0
                with target.open("xb") as output:
                    while True:
                        chunk = uploaded.stream.read(1024 * 1024)
                        if not chunk:
                            break
                        total += len(chunk)
                        if total > self.max_upload():
                            raise ValueError(f"This document exceeds the {format_bytes(self.max_upload())} upload limit.")
                        output.write(chunk)
                if total == 0:
                    raise ValueError("The selected document is empty.")
                kind = validate_document(target, extension)
                options = parse_print_options(str(request.form.get("options") or "{}"), session.capabilities)
                if not self.sessions.attach_file(token, target, kind, total):
                    raise PermissionError("This QR session is no longer valid.")
                self.print_manager.submit(token, target, extension, kind, options)
                return jsonify(accepted=True, state="received"), 202
            except (ValueError, PermissionError) as exc:
                secure_delete(target)
                self.sessions.finish(token, False, str(exc))
                return jsonify(error=str(exc)), 400
            except OSError:
                secure_delete(target)
                self.sessions.finish(token, False, "Instant Print could not safely store the temporary document.")
                return jsonify(error="Instant Print could not safely accept the document."), 500
            except Exception:
                secure_delete(target)
                self.logger.exception("Upload preparation failed")
                self.sessions.finish(token, False, "The document could not be prepared for printing.")
                return jsonify(error="The document could not be prepared for printing."), 500

    def start(self) -> int:
        """Bind Waitress once on the preferred port, then fall back safely."""
        if self._thread and self._thread.is_alive() and self.port:
            return self.port
        last_error: BaseException | None = None
        for port in [8765, *range(8766, 8791)]:
            try:
                server = create_server(self.flask, host="0.0.0.0", port=port, threads=4)
                self._server, self.port = server, port
                self._thread = threading.Thread(target=server.run, name="InstantPrintWebServer", daemon=True)
                self._thread.start()
                self.logger.info("Local Waitress server started on a LAN port")
                return port
            except OSError as exc:
                last_error = exc
        raise RuntimeError("Instant Print could not bind a local network port.") from last_error

    def stop(self) -> None:
        self._stopping.set()
        if self._server is not None:
            try:
                self._server.close()
            except Exception:
                pass


# ---------------------------------------------------------------------------
# Desktop UI.  Widgets are updated exclusively on the Tk main thread.
# ---------------------------------------------------------------------------

class DarkButton(tk.Button):
    def __init__(self, parent: tk.Misc, text: str, command: Callable[[], None], accent: bool = True, **kwargs: Any) -> None:
        self.normal = ACCENT if accent else PANEL_ALT
        self.hover = ACCENT_HOVER if accent else PANEL_HOVER
        super().__init__(parent, text=text, command=command, bg=self.normal, fg=TEXT,
                         activebackground=self.hover, activeforeground=TEXT, relief="flat",
                         bd=0, cursor="hand2", font=("Segoe UI", 11, "bold"), padx=18, pady=11,
                         highlightthickness=0, **kwargs)
        self.bind("<Enter>", lambda _event: self.configure(bg=self.hover) if str(self["state"]) == "normal" else None)
        self.bind("<Leave>", lambda _event: self.configure(bg=self.normal))
        self.bind("<ButtonPress-1>", lambda _event: self.configure(bg="#5f45cf" if accent else "#242424"))
        self.bind("<ButtonRelease-1>", lambda _event: self.configure(bg=self.hover))


class ScrollFrame(tk.Frame):
    def __init__(self, parent: tk.Misc) -> None:
        super().__init__(parent, bg=WINDOW_BG)
        self.canvas = tk.Canvas(self, bg=WINDOW_BG, highlightthickness=0, bd=0)
        scrollbar = tk.Scrollbar(self, orient="vertical", command=self.canvas.yview, bg=PANEL_ALT, activebackground=PANEL_HOVER, troughcolor=WINDOW_BG, relief="flat")
        self.content = tk.Frame(self.canvas, bg=WINDOW_BG)
        self.window_id = self.canvas.create_window((0, 0), window=self.content, anchor="nw")
        self.canvas.configure(yscrollcommand=scrollbar.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        self.content.bind("<Configure>", lambda _event: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda event: self.canvas.itemconfigure(self.window_id, width=event.width))
        self.canvas.bind_all("<MouseWheel>", self._wheel, add="+")

    def _wheel(self, event: tk.Event[Any]) -> None:
        if self.winfo_exists():
            self.canvas.yview_scroll(int(-event.delta / 120), "units")


class InstantPrintApp:
    def __init__(self) -> None:
        set_dpi_awareness()
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.configure(bg=WINDOW_BG)
        self.root.geometry("1180x760")
        self.root.minsize(1100, 700)
        self.root.option_add("*tearOff", False)
        try:
            self.root.tk.call("tk", "scaling", self.root.winfo_fpixels("1i") / 96.0)
        except tk.TclError:
            pass

        self.settings = {
            "session_seconds": SESSION_SECONDS_DEFAULT,
            "max_upload_bytes": MAX_UPLOAD_BYTES_DEFAULT,
            "auto_refresh": True,
        }
        self.temp_root = Path(tempfile.gettempdir()) / "InstantPrint"
        cleanup_stale_temp_files(self.temp_root)
        self.logger = setup_logging(self.temp_root)
        self.printers = PrinterManager(self.logger)
        self.sessions = SessionManager(self.logger, lambda: int(self.settings["session_seconds"]))
        self.processor = DocumentProcessor(self.logger, self.temp_root)
        self.print_manager = PrintManager(self.sessions, self.printers, self.processor, self.logger)
        self.server = LocalPrintServer(self.sessions, self.print_manager, self.temp_root, lambda: int(self.settings["max_upload_bytes"]), self.logger)
        self.server_error: str | None = None
        self.current_page = ""
        self.current_session_token: str | None = None
        self.selected_printer: PrinterInfo | None = None
        self.printer_cache: list[PrinterInfo] = []
        self.printer_loading = False
        self._ui_events: queue.Queue[tuple[str, Any]] = queue.Queue()
        self._closing = False
        self._qr_photo: ImageTk.PhotoImage | None = None
        self._status_label: tk.Label | None = None
        self._countdown_label: tk.Label | None = None
        self._page_body = tk.Frame(self.root, bg=WINDOW_BG)
        self._page_body.pack(fill="both", expand=True)
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self._start_server()
        self.show_welcome()
        self.root.after(150, self._drain_events)
        self.root.after(1000, self._housekeep)
        self.logger.info("Application launched")

    def _start_server(self) -> None:
        try:
            self.server.start()
        except Exception as exc:
            self.server_error = safe_error_message(exc, "The local phone connection service could not start.")
            self.logger.exception("Local server startup failed")

    def _clear_page(self) -> tk.Frame:
        for child in self._page_body.winfo_children():
            child.destroy()
        frame = tk.Frame(self._page_body, bg=WINDOW_BG)
        frame.pack(fill="both", expand=True)
        return frame

    def _topbar(self, parent: tk.Misc, back: Callable[[], None] | None = None) -> tk.Frame:
        bar = tk.Frame(parent, bg=WINDOW_BG)
        bar.pack(fill="x", padx=40, pady=(26, 10))
        if back is not None:
            DarkButton(bar, "← Back", back, accent=False, padx=13, pady=7).pack(side="left")
        tk.Label(bar, text="INSTANT PRINT", bg=WINDOW_BG, fg="#c4bbff", font=("Segoe UI", 10, "bold")).pack(side="left", padx=(14 if back else 0, 0))
        DarkButton(bar, "⚙ Settings", self.show_settings, accent=False, padx=13, pady=7).pack(side="right")
        return bar

    @staticmethod
    def _label(parent: tk.Misc, text: str, size: int = 12, color: str = TEXT, bold: bool = False, **kwargs: Any) -> tk.Label:
        return tk.Label(parent, text=text, bg=kwargs.pop("bg", WINDOW_BG), fg=color,
                        font=("Segoe UI", size, "bold" if bold else "normal"), **kwargs)

    def _invalidate_active_session(self) -> None:
        if self.current_session_token:
            self.sessions.invalidate(self.current_session_token)
            self.current_session_token = None

    def show_welcome(self) -> None:
        self._invalidate_active_session()
        self.current_page = "welcome"
        page = self._clear_page()
        self._topbar(page)
        hero = tk.Frame(page, bg=WINDOW_BG)
        hero.pack(fill="both", expand=True, padx=80)
        hero.grid_columnconfigure(0, weight=1)
        hero.grid_rowconfigure(0, weight=1)
        content = tk.Frame(hero, bg=WINDOW_BG)
        content.grid(row=0, column=0)
        self._label(content, "Print instantly.", 42, bold=True).pack(anchor="center")
        self._label(content, "No cables.  No file sharing.  No downloads.", 19, color="#d4d4d4").pack(pady=(12, 0))
        self._label(content, "Just scan, upload and print.", 19, color="#d4d4d4").pack(pady=(2, 25))
        grid = tk.Frame(content, bg=WINDOW_BG)
        grid.pack(pady=(0, 26))
        features = ("Secure QR Sessions", "Real-Time Printers", "Private Printing", "No Account Required", "Local Network Transfer", "Automatic Cleanup")
        for index, feature in enumerate(features):
            card = tk.Frame(grid, bg=PANEL_BG, highlightbackground="#242424", highlightthickness=1, width=205, height=75)
            card.grid(row=index // 3, column=index % 3, padx=7, pady=7, sticky="nsew")
            card.grid_propagate(False)
            self._label(card, "●", 13, ACCENT, bg=PANEL_BG).pack(side="left", padx=(16, 8))
            self._label(card, feature, 10, bg=PANEL_BG, bold=True).pack(side="left")
        DarkButton(content, "Get Started  →", self.show_printers, width=22).pack(pady=5)
        self._label(content, "Print from any phone on the same local network.", 10, MUTED).pack(pady=(13, 0))
        if self.server_error:
            self._label(content, self.server_error, 10, ERROR, wraplength=650).pack(pady=(16, 0))

    def show_printers(self) -> None:
        self._invalidate_active_session()
        self.current_page = "printers"
        page = self._clear_page()
        self._topbar(page, self.show_welcome)
        main = tk.Frame(page, bg=WINDOW_BG)
        main.pack(fill="both", expand=True, padx=85, pady=(24, 25))
        title_row = tk.Frame(main, bg=WINDOW_BG)
        title_row.pack(fill="x")
        self._label(title_row, "Select a Printer", 29, bold=True).pack(side="left")
        DarkButton(title_row, "↻ Refresh Printers", self.refresh_printers, accent=False, padx=14, pady=8).pack(side="right")
        self._label(main, "Choose a printer connected to this Windows device.", 12, MUTED).pack(anchor="w", pady=(8, 21))
        self.printer_area = ScrollFrame(main)
        self.printer_area.pack(fill="both", expand=True)
        self.printer_message = self._label(self.printer_area.content, "Detecting Windows printers...", 13, MUTED)
        self.printer_message.pack(pady=55)
        self.refresh_printers()

    def refresh_printers(self) -> None:
        if self.printer_loading:
            return
        self.printer_loading = True
        if hasattr(self, "printer_message") and self.printer_message.winfo_exists():
            self.printer_message.configure(text="Detecting Windows printers...")
        threading.Thread(target=self._enumerate_worker, name="InstantPrintDiscover", daemon=True).start()

    def _enumerate_worker(self) -> None:
        try:
            result: tuple[str, Any] = ("printers", self.printers.enumerate_printers())
        except Exception as exc:
            result = ("printer_error", safe_error_message(exc, "Windows printer discovery failed."))
        self._ui_events.put(result)

    def _render_printers(self, printers: list[PrinterInfo]) -> None:
        if self.current_page != "printers":
            return
        self.printer_loading = False
        for child in self.printer_area.content.winfo_children():
            child.destroy()
        if not printers:
            self._label(self.printer_area.content, "No Windows print queues were found.", 14, TEXT).pack(pady=(55, 8))
            self._label(self.printer_area.content, "Install or connect a printer in Windows, then refresh this list.", 11, MUTED).pack()
            return
        self.printer_cache = printers
        for info in printers:
            self._printer_card(self.printer_area.content, info)

    def _printer_card(self, parent: tk.Misc, info: PrinterInfo) -> None:
        card = tk.Frame(parent, bg=PANEL_BG, highlightbackground="#2a2a2a", highlightthickness=1, padx=22, pady=17, cursor="hand2")
        card.pack(fill="x", pady=7, padx=4)
        top = tk.Frame(card, bg=PANEL_BG)
        top.pack(fill="x")
        self._label(top, "🖨", 19, bg=PANEL_BG).pack(side="left", padx=(0, 10))
        name_box = tk.Frame(top, bg=PANEL_BG)
        name_box.pack(side="left", fill="x", expand=True)
        title = info.name + ("   DEFAULT" if info.is_default else "")
        self._label(name_box, title, 14, bg=PANEL_BG, bold=True, anchor="w").pack(fill="x")
        detail = " · ".join(item for item in (info.connection, info.port, info.driver) if item)[:180]
        self._label(name_box, detail or "Windows print queue", 10, MUTED, bg=PANEL_BG, anchor="w").pack(fill="x", pady=(4, 0))
        status_color = SUCCESS if info.status == "Ready" else ERROR if not info.available else WARNING
        bottom = tk.Frame(card, bg=PANEL_BG)
        bottom.pack(fill="x", pady=(16, 0))
        job_text = f"{info.jobs} queued job{'s' if info.jobs != 1 else ''}" if info.jobs else "No queued jobs"
        self._label(bottom, f"● {info.status}   ·   {job_text}", 10, status_color, bg=PANEL_BG).pack(side="left")
        select = DarkButton(bottom, "Select", lambda item=info: self.select_printer(item), padx=15, pady=7)
        select.pack(side="right")
        def choose(_event: tk.Event[Any], item: PrinterInfo = info) -> None:
            self.select_printer(item)
        for widget in (card, top, name_box, bottom):
            widget.bind("<Button-1>", choose)
            widget.bind("<Enter>", lambda _event, c=card: c.configure(bg=PANEL_HOVER))
            widget.bind("<Leave>", lambda _event, c=card: c.configure(bg=PANEL_BG))

    def select_printer(self, info: PrinterInfo) -> None:
        if self.printer_loading:
            return
        self.printer_loading = True
        self._show_printer_notice("Opening the selected Windows printer...")
        threading.Thread(target=self._select_worker, args=(info.name,), name="InstantPrintSelect", daemon=True).start()

    def _show_printer_notice(self, text: str) -> None:
        if self.current_page != "printers":
            return
        for child in self.printer_area.content.winfo_children():
            child.destroy()
        self._label(self.printer_area.content, text, 13, MUTED).pack(pady=55)

    def _select_worker(self, name: str) -> None:
        try:
            info = self.printers.inspect_printer(name)
            if not info.available:
                raise RuntimeError(f"This printer is {info.status.lower()}. Resolve the printer issue and refresh the list.")
            capabilities = self.printers.get_capabilities(info)
            self._ui_events.put(("selected", (info, capabilities)))
        except Exception as exc:
            self._ui_events.put(("select_error", safe_error_message(exc, "The selected printer could not be opened.")))

    def _start_qr(self, info: PrinterInfo, capabilities: dict[str, Any]) -> None:
        self.printer_loading = False
        if self.server_error or not self.server.port:
            self._show_printer_notice("The local phone connection server is unavailable. Restart Instant Print and try again.")
            return
        lan_ip = find_lan_ipv4()
        if lan_ip is None:
            self._show_printer_notice("No private LAN IPv4 address is available. Connect this PC to the same Wi-Fi/Ethernet network as the phone, then refresh.")
            return
        self.selected_printer = info
        session = self.sessions.create(info, capabilities)
        self.current_session_token = session.token
        self._show_qr(session, lan_ip)

    def _show_qr(self, session: PrintSession, lan_ip: str) -> None:
        self.current_page = "qr"
        page = self._clear_page()
        self._topbar(page, self.show_printers)
        main = tk.Frame(page, bg=WINDOW_BG)
        main.pack(fill="both", expand=True, padx=70, pady=(13, 28))
        left = tk.Frame(main, bg=WINDOW_BG)
        right = tk.Frame(main, bg=WINDOW_BG)
        left.pack(side="left", fill="both", expand=True, padx=(20, 45))
        right.pack(side="right", fill="y", padx=(30, 20))
        self._label(left, "Ready to Print", 31, bold=True).pack(anchor="w", pady=(18, 4))
        self._label(left, "Scan this QR code using your phone camera.", 12, MUTED).pack(anchor="w")
        qr_url = f"http://{lan_ip}:{self.server.port}/s/{session.token}"
        qr_image = qrcode.QRCode(version=None, error_correction=qrcode.constants.ERROR_CORRECT_H, box_size=12, border=4)
        qr_image.add_data(qr_url)
        qr_image.make(fit=True)
        image = qr_image.make_image(fill_color="#000000", back_color="#ffffff").convert("RGB").resize((400, 400), Image.Resampling.NEAREST)
        self._qr_photo = ImageTk.PhotoImage(image)
        image.close()
        qr_panel = tk.Frame(left, bg="#ffffff", padx=15, pady=15)
        qr_panel.pack(anchor="w", pady=(24, 12))
        tk.Label(qr_panel, image=self._qr_photo, bg="#ffffff").pack()
        self._label(left, "Phone and PC must be connected to the same local network.", 10, MUTED).pack(anchor="w")
        self._countdown_label = self._label(left, "", 12, "#d8d3ff", bold=True)
        self._countdown_label.pack(anchor="w", pady=(13, 0))
        self._status_label = self._label(left, "Waiting for document...", 13, TEXT, bold=True, wraplength=510, justify="left")
        self._status_label.pack(anchor="w", pady=(7, 0))
        panel = tk.Frame(right, bg=PANEL_BG, highlightbackground="#2c2c2c", highlightthickness=1, padx=24, pady=24, width=310)
        panel.pack(fill="x", pady=(55, 0))
        panel.pack_propagate(False)
        self._label(panel, "Selected Printer", 11, "#beb7ff", bg=PANEL_BG, bold=True).pack(anchor="w")
        self._label(panel, info_text(session.printer.name, 45), 16, TEXT, bg=PANEL_BG, bold=True, wraplength=265, justify="left").pack(anchor="w", pady=(9, 4))
        color = SUCCESS if session.printer.status == "Ready" else WARNING
        self._label(panel, f"● {session.printer.status}", 11, color, bg=PANEL_BG).pack(anchor="w")
        self._label(panel, session.printer.port or session.printer.connection, 10, MUTED, bg=PANEL_BG).pack(anchor="w", pady=(4, 0))
        DarkButton(panel, "Generate New QR", self.generate_new_qr, width=22).pack(pady=(27, 9))
        DarkButton(panel, "Cancel Session", self.cancel_session, accent=False, width=22).pack()
        self._label(right, "Can’t open the page?\n1. Put phone and PC on the same Wi-Fi/network.\n2. Allow Instant Print through Windows Firewall on Private networks.\n3. Disable Wi-Fi client isolation if enabled.", 9, MUTED, justify="left", wraplength=310).pack(anchor="w", pady=(18, 0))
        self._tick_qr()

    def generate_new_qr(self) -> None:
        if not self.selected_printer:
            self.show_printers()
            return
        self._invalidate_active_session()
        self._show_printer_notice("Creating a new secure QR session...")
        self.current_page = "printers"
        threading.Thread(target=self._select_worker, args=(self.selected_printer.name,), name="InstantPrintRenew", daemon=True).start()

    def cancel_session(self) -> None:
        self._invalidate_active_session()
        self.show_printers()

    def _tick_qr(self) -> None:
        if self.current_page != "qr" or not self.current_session_token:
            return
        snapshot = self.sessions.status_snapshot(self.current_session_token)
        if snapshot is None:
            return
        seconds = int(snapshot["expires_in"])
        if self._countdown_label and self._countdown_label.winfo_exists():
            self._countdown_label.configure(text=f"Session expires in {seconds // 60:02d}:{seconds % 60:02d}")
        if self._status_label and self._status_label.winfo_exists():
            self._status_label.configure(text=str(snapshot["message"]), fg=SUCCESS if snapshot["state"] == "completed" else ERROR if snapshot["state"] in {"failed", "expired"} else TEXT)
        self.root.after(700, self._tick_qr)

    def show_settings(self) -> None:
        dialog = tk.Toplevel(self.root)
        dialog.title("Instant Print Settings")
        dialog.configure(bg=PANEL_BG)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        frame = tk.Frame(dialog, bg=PANEL_BG, padx=26, pady=24)
        frame.pack(fill="both", expand=True)
        self._label(frame, "Settings", 19, bg=PANEL_BG, bold=True).pack(anchor="w")
        self._label(frame, "Settings apply to newly created QR sessions.", 10, MUTED, bg=PANEL_BG).pack(anchor="w", pady=(4, 18))
        session_value = tk.StringVar(value=str(int(self.settings["session_seconds"]) // 60))
        upload_value = tk.StringVar(value=str(int(self.settings["max_upload_bytes"]) // (1024 * 1024)))
        auto_value = tk.BooleanVar(value=bool(self.settings["auto_refresh"]))
        for label, variable, suffix in (("Session timeout", session_value, "minutes (1–60)"), ("Maximum upload size", upload_value, "MB (1–500)")):
            row = tk.Frame(frame, bg=PANEL_BG)
            row.pack(fill="x", pady=7)
            self._label(row, label, 11, bg=PANEL_BG, bold=True).pack(side="left")
            entry = tk.Entry(row, textvariable=variable, width=7, bg="#252525", fg=TEXT, insertbackground=TEXT, relief="flat", font=("Segoe UI", 11))
            entry.pack(side="right", padx=(8, 0), ipady=5)
            self._label(row, suffix, 9, MUTED, bg=PANEL_BG).pack(side="right")
        check = tk.Checkbutton(frame, text="Auto-refresh printer list", variable=auto_value, bg=PANEL_BG, fg=TEXT, activebackground=PANEL_BG, activeforeground=TEXT, selectcolor="#252525", font=("Segoe UI", 10))
        check.pack(anchor="w", pady=(10, 20))
        error_label = self._label(frame, "", 9, ERROR, bg=PANEL_BG, wraplength=330)
        error_label.pack(anchor="w")
        def save() -> None:
            try:
                minutes = clamp(int(session_value.get()), 1, 60)
                megabytes = clamp(int(upload_value.get()), 1, 500)
            except ValueError:
                error_label.configure(text="Enter whole numbers for both settings.")
                return
            self.settings["session_seconds"] = minutes * 60
            self.settings["max_upload_bytes"] = megabytes * 1024 * 1024
            self.settings["auto_refresh"] = auto_value.get()
            dialog.destroy()
        DarkButton(frame, "Save Settings", save, width=20).pack(anchor="e")

    def _drain_events(self) -> None:
        try:
            while True:
                kind, payload = self._ui_events.get_nowait()
                if kind == "printers":
                    self._render_printers(payload)
                elif kind == "printer_error":
                    self.printer_loading = False
                    if self.current_page == "printers":
                        self._show_printer_notice(payload)
                elif kind == "selected":
                    self._start_qr(*payload)
                elif kind == "select_error":
                    self.printer_loading = False
                    if self.current_page == "printers":
                        self._show_printer_notice(payload)
        except queue.Empty:
            pass
        if not self._closing:
            self.root.after(150, self._drain_events)

    def _housekeep(self) -> None:
        self.sessions.cleanup()
        if self.current_page == "printers" and self.settings["auto_refresh"] and not self.printer_loading:
            # Refresh only occasionally, and never from the UI thread.
            elapsed = getattr(self, "_last_auto_refresh", 0.0)
            if time.monotonic() - elapsed > 30:
                self._last_auto_refresh = time.monotonic()
                self.refresh_printers()
        if not self._closing:
            self.root.after(1000, self._housekeep)

    def close(self) -> None:
        if self._closing:
            return
        self._closing = True
        self.sessions.invalidate_all()
        self.server.stop()
        self.print_manager.shutdown()
        self.logger.info("Application closed")
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


def info_text(value: str, limit: int) -> str:
    return value if len(value) <= limit else value[:limit - 1] + "…"


def acquire_single_instance() -> Any | None:
    """Return a retained Windows mutex, or None when another instance exists."""
    if sys.platform != "win32":
        return object()
    mutex = ctypes.windll.kernel32.CreateMutexW(None, False, "Local\\InstantPrint_OneInstance_v1")
    if not mutex:
        return object()  # Fail open rather than blocking a legitimate user on API failure.
    if ctypes.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
        ctypes.windll.kernel32.CloseHandle(mutex)
        return None
    return mutex


def main() -> None:
    mutex = acquire_single_instance()
    if mutex is None:
        root = tk.Tk()
        root.withdraw()
        messagebox.showinfo(APP_NAME, "Instant Print is already running.")
        root.destroy()
        return
    if sys.platform != "win32" or WIN32_IMPORT_ERROR is not None or DEPENDENCY_IMPORT_ERROR is not None:
        root = tk.Tk()
        root.withdraw()
        missing = str(DEPENDENCY_IMPORT_ERROR or WIN32_IMPORT_ERROR or "Windows printer APIs")
        messagebox.showerror(APP_NAME, f"Instant Print requires Windows and its Python dependencies.\n\nMissing or unavailable component: {missing}\n\nInstall the required dependencies, then run this app on Windows 10 or 11.")
        root.destroy()
        return
    app = InstantPrintApp()
    app.run()
    if sys.platform == "win32" and mutex is not None:
        try:
            ctypes.windll.kernel32.CloseHandle(mutex)
        except Exception:
            pass


if __name__ == "__main__":
    main()
