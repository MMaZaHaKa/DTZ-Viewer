#!/usr/bin/env python3
# gta_hexviewer.py
# PyQt5: pip install pyqt5

from PyQt5 import QtWidgets, QtGui, QtCore
import sys, struct, zlib, math, re

# ---------- Конфиг ----------
DEFAULT_HEADER_SIZE = 0x20
BYTES_PER_LINE = 16
DEFAULT_FONT_FAMILY = "Courier New"
DEFAULT_FONT_SIZE = 11
PAD_BYTES = {0x00, 0xAA}
DEFAULT_PATTERN_THRESHOLD = 4
MAX_SAFE_DECOMP_SIZE = 32 * 1024 * 1024
DEFAULT_HISTORY_LIMIT = 300

# Цвета по-умолчанию
COL_BG = QtGui.QColor("#ffffff")
COL_HEX = QtGui.QColor("#008000")
COL_POINTER = QtGui.QColor("#c00000")
COL_SELECTION = QtGui.QColor("#4090ff")
COL_PAD = QtGui.QColor("#c890ff")
COL_ADDR = QtGui.QColor("#808080")
COL_ASCII = QtGui.QColor("#000000")
COL_TEXT_ON_SELECTION = QtGui.QColor("#000000")

# ---------- Утилиты ----------
def try_decompress_zlib(data: bytes):
    try:
        return zlib.decompress(data)
    except Exception:
        return None

def read_le_uint(data: bytes, offset:int, size:int):
    if offset + size > len(data): return None
    if size == 1: return data[offset]
    if size == 2: return struct.unpack_from("<H", data, offset)[0]
    if size == 4: return struct.unpack_from("<I", data, offset)[0]
    return None

def read_le_int(data: bytes, offset:int, size:int):
    if offset + size > len(data): return None
    if size == 1: return struct.unpack_from("<b", data, offset)[0]
    if size == 2: return struct.unpack_from("<h", data, offset)[0]
    if size == 4: return struct.unpack_from("<i", data, offset)[0]
    return None

def read_float(data: bytes, offset:int):
    if offset + 4 > len(data): return None
    return struct.unpack_from("<f", data, offset)[0]

# ---------- VirtualHexView ----------
class VirtualHexView(QtWidgets.QAbstractScrollArea):
    hovered_offset = QtCore.pyqtSignal(int)   # offset or -1
    jump_to_requested = QtCore.pyqtSignal(int)
    selection_changed = QtCore.pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMouseTracking(True)
        self.viewport().setMouseTracking(True)

        # data
        self.data = b""
        self.header_size = DEFAULT_HEADER_SIZE
        self.absolute_offset = False
        self.bytes_per_line = BYTES_PER_LINE

        # pad/pointer config
        self.pad_bytes = PAD_BYTES
        self.pad_threshold = DEFAULT_PATTERN_THRESHOLD

        # reloc
        self.chunk_header = None
        self.reloc_entries = []
        self.pointer_fields = set()        # starts of 4-byte pointer fields
        self.pointer_byte_offsets = set()  # all bytes covered by pointer fields

        # selection & caret
        self.sel_start = None
        self.sel_end = None
        self.hovered = -1

        # notes
        self.notes = {}

        # font/metrics
        self.font_family = DEFAULT_FONT_FAMILY
        self.font_size = DEFAULT_FONT_SIZE
        self.font = QtGui.QFont(self.font_family, self.font_size)
        self.fm = QtGui.QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance('0')
        self.char_h = self.fm.height()
        self.addr_area_w = self.char_w * 8 + self.char_w
        self.hex_byte_w = self.char_w * 2 + self.char_w
        self.middle_gap = self.char_w * 2

        # colors
        self.col_bg = COL_BG
        self.col_hex = COL_HEX
        self.col_pointer = COL_POINTER
        self.col_pad = COL_PAD
        self.col_addr = COL_ADDR
        self.col_ascii = COL_ASCII
        self.col_selection = COL_SELECTION
        self.col_text_on_selection = COL_TEXT_ON_SELECTION

        # pad offsets cache
        self.pad_offsets = set()

        # scrollbar
        self.update_scrollbars()

    def sizeHint(self):
        return QtCore.QSize(900, 600)

    # ---------- load & parse ----------
    def load_bytes(self, data: bytes, header_size:int=None, absolute_offset:bool=False):
        self.data = data or b""
        if header_size is not None:
            self.header_size = header_size
        self.absolute_offset = absolute_offset

        self.chunk_header = None
        self.reloc_entries = []
        self.pointer_fields.clear()
        self.pointer_byte_offsets.clear()

        if len(self.data) >= 32:
            self._parse_chunk_header()
        if not self.reloc_entries:
            self._heuristic_reloc()
        else:
            self.pointer_fields = set(self.reloc_entries)
            for p in self.pointer_fields:
                for i in range(4):
                    self.pointer_byte_offsets.add(p + i)

        self._compute_pad_offsets()
        self.sel_start = None; self.sel_end = None; self.hovered = -1
        self.update_scrollbars()
        self.viewport().update()
        self.selection_changed.emit()

    def _parse_chunk_header(self):
        try:
            ident_raw, shrink, fileEnd, dataEnd, relocTab, numRelocs, globalTab, numClasses, numFuncs = struct.unpack_from("<7I2H", self.data, 0)
            try:
                ident_str = ident_raw.to_bytes(4, 'little').decode('ascii', errors='replace')
            except:
                ident_str = hex(ident_raw)
            self.chunk_header = {"ident":ident_str,"ident_raw":ident_raw,"shrink":shrink,"fileEnd":fileEnd,"dataEnd":dataEnd,"relocTab":relocTab,"numRelocs":numRelocs,"globalTab":globalTab,"numClasses":numClasses,"numFuncs":numFuncs}
            if numRelocs and relocTab + 4*numRelocs <= len(self.data):
                entries=[]
                base = relocTab
                for i in range(numRelocs):
                    v = struct.unpack_from("<I", self.data, base + i*4)[0]
                    if 0 <= v < len(self.data):
                        entries.append(v)
                if len(entries) >= max(1, min(4, numRelocs//4)):
                    self.reloc_entries = sorted(set(entries))
        except Exception:
            self.chunk_header = None
            self.reloc_entries = []

    def _heuristic_reloc(self):
        n = len(self.data)
        if n < 8:
            self.reloc_entries=[]
            return
        search_sz = min(n, 8*1024)
        start = n - search_sz
        cand=[]
        for off in range(start, n-4+1, 4):
            val = struct.unpack_from("<I", self.data, off)[0]
            if 0 <= val < n:
                cand.append(val)
        if len(cand) >= 4:
            self.reloc_entries = sorted(set(cand))
            self.pointer_fields = set(self.reloc_entries)
            for p in self.pointer_fields:
                for i in range(4): self.pointer_byte_offsets.add(p+i)
        else:
            self.reloc_entries=[]; self.pointer_fields=set(); self.pointer_byte_offsets=set()

    def _compute_pad_offsets(self):
        # mark runs of bytes in pad_bytes excluding bytes that are part of pointer fields
        self.pad_offsets = set()
        data = self.data
        if not self.pad_bytes or self.pad_threshold <= 0:
            return
        n = len(data)
        i = 0
        while i < n:
            b = data[i]
            if b in self.pad_bytes:
                j = i
                while j < n and data[j] in self.pad_bytes:
                    j += 1
                # exclude region bytes that overlap pointer fields
                # compute contiguous runs of pad bytes that are not pointer bytes
                k = i
                while k < j:
                    # skip pointer bytes
                    if k in self.pointer_byte_offsets:
                        k += 1
                        continue
                    start = k
                    while k < j and k not in self.pointer_byte_offsets:
                        k += 1
                    length = k - start
                    if length >= self.pad_threshold:
                        self.pad_offsets.update(range(start, k))
                i = j
            else:
                i += 1

    # ---------- scrollbars ----------
    def update_scrollbars(self):
        total_lines = max(1, math.ceil(len(self.data) / self.bytes_per_line))
        vs = self.verticalScrollBar()
        vs.setMinimum(0); vs.setMaximum(max(0, total_lines - 1)); vs.setPageStep(1)
        self.horizontalScrollBar().setRange(0,0)
        self.viewport().update()

    # ---------- paint ----------
    def paintEvent(self, ev):
        painter = QtGui.QPainter(self.viewport())
        painter.fillRect(self.viewport().rect(), self.col_bg)
        painter.setFont(self.font)
        fm = self.fm

        vph = self.viewport().height()
        line_h = self.char_h
        lines_visible = max(1, vph // line_h)
        first_line = self.verticalScrollBar().value()

        addr_x = 4
        hex_x = addr_x + self.addr_area_w + self.char_w
        ascii_x = hex_x + (self.hex_byte_w * (self.bytes_per_line//2)) + self.middle_gap + (self.hex_byte_w * (self.bytes_per_line - self.bytes_per_line//2)) + self.char_w*2

        for row in range(lines_visible):
            line_no = first_line + row
            y = (row + 1) * line_h - fm.descent()
            start_off = line_no * self.bytes_per_line
            if start_off >= len(self.data):
                break
            display_addr = start_off - (0 if self.absolute_offset else self.header_size)
            addr_text = "%08X:" % (display_addr if display_addr >= 0 else 0)
            painter.setPen(self.col_addr); painter.drawText(addr_x, y, addr_text)

            bx = hex_x
            for bi in range(self.bytes_per_line):
                off = start_off + bi
                if off >= len(self.data): break
                b = self.data[off]; hex_s = "%02X" % b
                # selection
                sel=False
                if self.sel_start is not None and self.sel_end is not None:
                    s=min(self.sel_start,self.sel_end); e=max(self.sel_start,self.sel_end)
                    if s <= off <= e: sel=True
                # pad background
                if off in self.pad_offsets:
                    rect = QtCore.QRect(bx - 1, y - (line_h - fm.descent()), self.char_w*2 + 2, line_h)
                    painter.fillRect(rect, self.col_pad)
                # selection bg on top
                if sel:
                    rect = QtCore.QRect(bx - 1, y - (line_h - fm.descent()), self.char_w*2 + 2, line_h)
                    painter.fillRect(rect, self.col_selection)
                # pointer bytes
                if off in self.pointer_byte_offsets:
                    painter.setPen(self.col_pointer)
                    font_b = QtGui.QFont(self.font); font_b.setBold(True); painter.setFont(font_b)
                    if sel: painter.setPen(self.col_text_on_selection)
                    painter.drawText(bx, y, hex_s)
                    painter.setFont(self.font)
                else:
                    painter.setPen(self.col_text_on_selection if sel else self.col_hex)
                    painter.drawText(bx, y, hex_s)
                bx += self.hex_byte_w
                if bi == (self.bytes_per_line//2 - 1): bx += self.middle_gap

            # ascii
            ax = ascii_x
            ascii_chars = []
            for bi in range(self.bytes_per_line):
                off = start_off + bi
                if off >= len(self.data): ascii_chars.append(' ')
                else:
                    bt = self.data[off]; ascii_chars.append(chr(bt) if 0x20 <= bt < 0x7F else '.')
            ascii_text = "".join(ascii_chars)
            ax_cur = ax
            for bi,ch in enumerate(ascii_text):
                off = start_off + bi
                if off >= len(self.data): break
                sel=False
                if self.sel_start is not None and self.sel_end is not None:
                    s=min(self.sel_start,self.sel_end); e=max(self.sel_start,self.sel_end)
                    if s <= off <= e: sel=True
                if sel:
                    rect = QtCore.QRect(ax_cur - 1, y - (line_h - fm.descent()), self.char_w + 2, line_h)
                    painter.fillRect(rect, self.col_selection); painter.setPen(self.col_text_on_selection)
                else:
                    painter.setPen(self.col_ascii)
                painter.drawText(ax_cur, y, ch); ax_cur += self.char_w

        # caret (vertical bar) when no selection
        if self.sel_start is None and self.sel_end is None and self.hovered is not None and 0 <= self.hovered < len(self.data):
            line = self.hovered // self.bytes_per_line
            col = self.hovered % self.bytes_per_line
            first_line = self.verticalScrollBar().value()
            rel_line = line - first_line
            lines_visible_now = lines_visible
            if 0 <= rel_line < lines_visible_now:
                bx = hex_x + col * self.hex_byte_w
                if col >= self.bytes_per_line//2: bx += self.middle_gap
                caret_x = bx - 1
                caret_rect = QtCore.QRect(caret_x, rel_line * line_h, 2, line_h)
                painter.fillRect(caret_rect, QtGui.QColor("#000000"))
        painter.end()

    # ---------- input mapping ----------
    def _pos_to_offset(self, pos: QtCore.QPoint):
        line_h = self.char_h
        first_line = self.verticalScrollBar().value()
        row = pos.y() // line_h
        line_no = first_line + row
        start_off = line_no * self.bytes_per_line
        if start_off >= len(self.data): return None
        addr_x = 4
        hex_x = addr_x + self.addr_area_w + self.char_w
        ascii_x = hex_x + (self.hex_byte_w * (self.bytes_per_line//2)) + self.middle_gap + (self.hex_byte_w * (self.bytes_per_line - self.bytes_per_line//2)) + self.char_w*2
        x = pos.x()
        if x >= hex_x:
            rel = x - hex_x
            half = self.bytes_per_line // 2
            per = self.hex_byte_w
            half_width = per * half
            if rel < half_width:
                bi = int(rel // per)
            else:
                rel2 = rel - half_width
                if rel2 < self.middle_gap: return None
                rel3 = rel2 - self.middle_gap
                bi = half + int(rel3 // per)
            off = start_off + bi
            if off < len(self.data): return off
        if x >= ascii_x:
            rel = x - ascii_x
            bi = int(rel // self.char_w)
            off = start_off + bi
            if off < len(self.data): return off
        return None

    def mouseMoveEvent(self, ev):
        off = self._pos_to_offset(ev.pos())
        if off is None:
            self.hovered = -1; self.hovered_offset.emit(-1)
        else:
            self.hovered = off; self.hovered_offset.emit(off)
            # tooltip with absolute & relative offsets + interprets
            abs_off = off
            rel_off = off - (0 if self.absolute_offset else self.header_size)
            u1 = read_le_uint(self.data, off, 1); u2 = read_le_uint(self.data, off, 2); u4 = read_le_uint(self.data, off, 4)
            f4 = read_float(self.data, off)
            tip = f"Absolute: 0x{abs_off:X}\n"
            tip += f"GTA payload offset: 0x{rel_off:X}\n"
            tip += f"1b: {u1} 2b: {u2} 4b: {u4}\n"
            tip += f"float: {('%.6g' % f4) if f4 is not None else 'N/A'}"
            QtWidgets.QToolTip.showText(ev.globalPos(), tip, self)
        # selection dragging
        if ev.buttons() & QtCore.Qt.LeftButton:
            if self.sel_start is None:
                if self.hovered >= 0:
                    self.sel_start = self.hovered; self.sel_end = self.hovered
            else:
                if self.hovered >= 0:
                    self.sel_end = self.hovered
            self.viewport().update(); self.selection_changed.emit()

    def mousePressEvent(self, ev):
        if ev.button() == QtCore.Qt.LeftButton:
            off = self._pos_to_offset(ev.pos())
            if off is not None:
                self.sel_start = off; self.sel_end = off; self.selection_changed.emit(); self.viewport().update()
        super().mousePressEvent(ev)

    def mouseReleaseEvent(self, ev):
        super().mouseReleaseEvent(ev)

    def mouseDoubleClickEvent(self, ev):
        off = self._pos_to_offset(ev.pos())
        if off is None: return
        for pf in self.pointer_fields:
            if pf <= off < pf+4:
                val = read_le_uint(self.data, pf, 4)
                if val is not None and 0 <= val < len(self.data):
                    self.jump_to_requested.emit(val)
                return

    def contextMenuEvent(self, ev):
        off = self._pos_to_offset(ev.pos())
        menu = QtWidgets.QMenu(self)
        if off is not None:
            act_note = menu.addAction("Add/Edit note")
            def edit_note():
                cur = self.notes.get(off, "")
                tx, ok = QtWidgets.QInputDialog.getMultiLineText(self, f"Note for 0x{off:X}", "Note:", cur)
                if ok:
                    if tx.strip(): self.notes[off]=tx.strip()
                    elif off in self.notes: del self.notes[off]
            act_note.triggered.connect(edit_note)
            menu.addSeparator()
            act_copy_addr = menu.addAction("Copy address (hex)")
            act_copy_hex1 = menu.addAction("Copy hex 1b")
            act_copy_hex2 = menu.addAction("Copy hex 2b")
            act_copy_hex4 = menu.addAction("Copy hex 4b")
            def to_clip(tx): QtWidgets.QApplication.clipboard().setText(tx)
            act_copy_addr.triggered.connect(lambda: to_clip(f"0x{off:X}"))
            act_copy_hex1.triggered.connect(lambda: to_clip(self._format_hex(off,1)))
            act_copy_hex2.triggered.connect(lambda: to_clip(self._format_hex(off,2)))
            act_copy_hex4.triggered.connect(lambda: to_clip(self._format_hex(off,4)))
            menu.addSeparator()
            if off in self.pointer_byte_offsets:
                act_jump = menu.addAction("Jump to pointer target")
                def jtarget():
                    pf=None
                    for p in self.pointer_fields:
                        if p <= off < p+4: pf=p; break
                    if pf is not None:
                        val = read_le_uint(self.data, pf, 4)
                        if val is not None and 0 <= val < len(self.data): self.jump_to_requested.emit(val)
                act_jump.triggered.connect(jtarget)
        menu.exec_(ev.globalPos())

    def _format_hex(self, offset:int, size:int):
        if offset is None or offset <0 or offset>=len(self.data): return ""
        available = min(size, len(self.data)-offset)
        b = self.data[offset:offset+available]
        # construct LE integer (as previous)
        val = 0
        for i in range(len(b)-1, -1, -1): val = (val<<8) | b[i]
        return "0x%X" % val

    def wheelEvent(self, ev):
        if ev.modifiers() & QtCore.Qt.ControlModifier:
            delta = ev.angleDelta().y()
            step = 1 if delta>0 else -1
            self.font_size = max(6, min(28, self.font_size + step))
            self.font = QtGui.QFont(self.font_family, self.font_size)
            self.fm = QtGui.QFontMetrics(self.font)
            self.char_w = self.fm.horizontalAdvance('0'); self.char_h = self.fm.height()
            self.addr_area_w = self.char_w * 8 + self.char_w
            self.hex_byte_w = self.char_w * 2 + self.char_w; self.middle_gap = self.char_w * 2
            self.update_scrollbars(); self.viewport().update()
            ev.accept()
        else:
            super().wheelEvent(ev)

    def scroll_to_offset(self, file_offset:int):
        if file_offset < 0: file_offset = 0
        if file_offset >= len(self.data): file_offset = max(0, len(self.data)-1)
        line = file_offset // self.bytes_per_line
        self.verticalScrollBar().setValue(line)
        self.viewport().update()

# ---------- MainWindow (toolbar, history, inspector) ----------
class MainWindow(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("GTA DTZ Hex Viewer")
        self.resize(1200, 750)

        self.view = VirtualHexView(self)
        self.setCentralWidget(self.view)

        # right inspector dock
        self.inspector = QtWidgets.QTreeWidget()
        self.inspector.setHeaderLabels(["Field", "Value"])
        dock = QtWidgets.QDockWidget("Inspector", self)
        dock.setWidget(self.inspector)
        self.addDockWidget(QtCore.Qt.RightDockWidgetArea, dock)

        # data
        self.raw_data = b""; self.decompressed = None; self.using_decompressed = True

        # history
        self.history = []   # list of offsets
        self.history_pos = -1
        self.history_limit = DEFAULT_HISTORY_LIMIT

        # toolbar
        tb = self.addToolBar("main")
        act_open = QtWidgets.QAction("Open...", self); act_open.triggered.connect(self.open_file); tb.addAction(act_open)
        self.zlib_checkbox = QtWidgets.QCheckBox("Use decompressed"); self.zlib_checkbox.stateChanged.connect(self.on_zlib_toggle); tb.addWidget(self.zlib_checkbox)
        tb.addSeparator()
        self.back_btn = QtWidgets.QPushButton("← Back"); self.back_btn.clicked.connect(self.go_back); tb.addWidget(self.back_btn)
        tb.addSeparator()
        tb.addWidget(QtWidgets.QLabel("Header size:"))
        self.header_edit = QtWidgets.QLineEdit(hex(DEFAULT_HEADER_SIZE)); self.header_edit.setMaximumWidth(90); tb.addWidget(self.header_edit)
        self.abs_checkbox = QtWidgets.QCheckBox("AbsoluteOffset"); self.abs_checkbox.setChecked(False); self.abs_checkbox.stateChanged.connect(self.refresh_view); tb.addWidget(self.abs_checkbox)
        tb.addSeparator()
        tb.addWidget(QtWidgets.QLabel("Go to:"))
        self.goto_edit = QtWidgets.QLineEdit(); self.goto_edit.setMaximumWidth(140); tb.addWidget(self.goto_edit)
        btn = QtWidgets.QPushButton("GO"); btn.clicked.connect(self.on_goto); tb.addWidget(btn)
        tb.addSeparator()
        tb.addWidget(QtWidgets.QLabel("Pad threshold:"))
        self.pad_spin = QtWidgets.QSpinBox(); self.pad_spin.setRange(1,1024); self.pad_spin.setValue(DEFAULT_PATTERN_THRESHOLD); self.pad_spin.valueChanged.connect(self.on_pad_changed); tb.addWidget(self.pad_spin)
        settings_btn = QtWidgets.QPushButton("Settings"); settings_btn.clicked.connect(self.open_settings); tb.addWidget(settings_btn)

        # status
        self.status = self.statusBar(); self.hover_label = QtWidgets.QLabel(""); self.status.addPermanentWidget(self.hover_label)

        # signals
        self.view.hovered_offset.connect(self.on_hover)
        self.view.jump_to_requested.connect(self.push_and_jump)
        self.view.selection_changed.connect(self.update_inspector)

        # shortcuts
        QtWidgets.QShortcut(QtGui.QKeySequence("Ctrl+G"), self, activated=self.ctrl_g)
        QtWidgets.QShortcut(QtGui.QKeySequence("Ctrl+C"), self, activated=self.copy_4bytes)
        QtWidgets.QShortcut(QtGui.QKeySequence("Ctrl+Shift+C"), self, activated=self.copy_address)

    # ---------- file open ----------
    def open_file(self):
        p, _ = QtWidgets.QFileDialog.getOpenFileName(self, "Open DTZ/Binary", ".", "All files (*)")
        if not p: return
        try:
            with open(p, "rb") as f: data = f.read()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Error", f"Failed to open: {e}"); return
        self.raw_data = data
        dec = try_decompress_zlib(data)
        if dec is not None:
            self.decompressed = dec; self.zlib_checkbox.setEnabled(True)
            if len(dec) > MAX_SAFE_DECOMP_SIZE:
                res = QtWidgets.QMessageBox.question(self, "Large decompressed",
                    f"Decompressed size {len(dec)} bytes (> {MAX_SAFE_DECOMP_SIZE}). Load anyway?",
                    QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No, QtWidgets.QMessageBox.No)
                if res == QtWidgets.QMessageBox.No:
                    self.zlib_checkbox.setChecked(False); self.using_decompressed = False
                else:
                    self.zlib_checkbox.setChecked(True); self.using_decompressed = True
            else:
                self.zlib_checkbox.setChecked(True); self.using_decompressed = True
        else:
            self.decompressed = None; self.zlib_checkbox.setEnabled(False); self.zlib_checkbox.setChecked(False); self.using_decompressed = False
        self.refresh_view()

    def parse_header_size(self):
        t = self.header_edit.text().strip()
        if not t: return DEFAULT_HEADER_SIZE
        try:
            if t.lower().startswith("0x"): return int(t,16)
            return int(t,10)
        except: return DEFAULT_HEADER_SIZE

    def refresh_view(self):
        data = self.decompressed if (self.using_decompressed and self.decompressed is not None) else self.raw_data
        hdr = self.parse_header_size()
        self.view.header_size = hdr
        self.view.absolute_offset = self.abs_checkbox.isChecked()
        self.view.pad_threshold = self.pad_spin.value()
        self.view.pad_bytes = PAD_BYTES
        self.view.load_bytes(data, header_size=hdr, absolute_offset=self.abs_checkbox.isChecked())
        if self.view.chunk_header:
            ch = self.view.chunk_header
            self.status.showMessage(f"Chunk ident: {ch['ident']} relocTab:0x{ch['relocTab']:X} numRelocs:{ch['numRelocs']}", 8000)
        else:
            self.status.showMessage("Chunk header not detected.", 4000)
        # reset history
        self.history = []; self.history_pos = -1

    def on_zlib_toggle(self, state):
        self.using_decompressed = bool(state); self.refresh_view()

    def on_pad_changed(self, v):
        self.view.pad_threshold = v; self.view._compute_pad_offsets(); self.view.viewport().update()

    # ---------- history ----------
    def push_history(self, offset:int):
        # push current offset into history, respecting limit
        if offset is None: return
        # if we're not at the end, drop forward history
        if self.history_pos != len(self.history)-1:
            self.history = self.history[:self.history_pos+1]
        self.history.append(offset)
        # enforce limit
        if len(self.history) > self.history_limit:
            excess = len(self.history) - self.history_limit
            self.history = self.history[excess:]
        self.history_pos = len(self.history)-1
        # enable/disable back
        self.back_btn.setEnabled(self.history_pos > 0)

    def push_and_jump(self, offset:int):
        # push current view position before jumping (if any)
        cur_off = None
        # if there is hovered or selection start, push that as previous
        if self.view.hovered and self.view.hovered >= 0:
            cur_off = self.view.hovered
        # push current into history (if not None)
        if cur_off is not None:
            self.push_history(cur_off)
        # then jump to new
        self.view.scroll_to_offset(offset)
        # also push the new offset as top of history so Back will go back
        self.push_history(offset)
        self.update_inspector()

    def go_back(self):
        if self.history_pos <= 0: return
        self.history_pos -= 1
        off = self.history[self.history_pos]
        self.view.scroll_to_offset(off)
        self.back_btn.setEnabled(self.history_pos > 0)
        self.update_inspector()

    # ---------- goto / ctrl+g ----------
    def on_goto(self):
        text = self.goto_edit.text().strip()
        if not text: return
        try:
            if text.lower().startswith("0x"): val=int(text,16)
            else: val=int(text,10)
        except:
            QtWidgets.QMessageBox.warning(self, "Bad input", "Offset must be decimal or hex (0x...)."); return
        if self.abs_checkbox.isChecked(): target = val
        else: target = val + self.parse_header_size()
        if target <0 or target >= len(self.view.data):
            QtWidgets.QMessageBox.warning(self,"Out of range",f"Offset 0x{target:X} out of range."); return
        # push current and target
        cur = self.view.hovered if (self.view.hovered is not None and self.view.hovered>=0) else None
        if cur is not None: self.push_history(cur)
        self.view.scroll_to_offset(target); self.push_history(target)
        self.update_inspector()

    def ctrl_g(self):
        clip = QtWidgets.QApplication.clipboard().text().strip()
        pre = clip if (clip.startswith("0x") or clip.startswith("0X")) else ""
        text, ok = QtWidgets.QInputDialog.getText(self, "Go to offset", "Offset (hex 0x... or decimal):", QtWidgets.QLineEdit.Normal, pre)
        if ok and text.strip():
            self.goto_edit.setText(text.strip()); self.on_goto()

    # ---------- copy shortcuts ----------
    def copy_4bytes(self):
        off = self.get_current_offset_for_copy()
        if off is None: return
        s = self.view._format_hex(off, 4)
        QtWidgets.QApplication.clipboard().setText(s); self.status.showMessage(f"Copied {s}", 2000)

    def copy_address(self):
        off = self.get_current_offset_for_copy()
        if off is None: return
        txt = f"0x{off:X}"; QtWidgets.QApplication.clipboard().setText(txt); self.status.showMessage(f"Copied {txt}", 2000)

    def get_current_offset_for_copy(self):
        off = self.view.hovered if (self.view.hovered is not None and self.view.hovered>=0) else None
        if off is None and self.view.sel_start is not None:
            off = min(self.view.sel_start, self.view.sel_end)
        return off

    # ---------- hover / inspector ----------
    def on_hover(self, offset):
        if offset is None or offset < 0:
            self.hover_label.setText(""); self.update_inspector(); return
        b = self.view.data
        if offset >= len(b): self.hover_label.setText(""); return
        u1 = read_le_uint(b, offset, 1); u2 = read_le_uint(b, offset, 2); u4 = read_le_uint(b, offset, 4)
        i1 = read_le_int(b, offset, 1); i2 = read_le_int(b, offset, 2); i4 = read_le_int(b, offset, 4)
        f4 = read_float(b, offset)
        note = self.view.notes.get(offset, "")
        # pointer info
        pointer_info = ""
        if offset in self.view.pointer_byte_offsets:
            pf = None
            for p in self.view.pointer_fields:
                if p <= offset < p+4: pf = p; break
            if pf is not None:
                val = read_le_uint(b, pf, 4)
                if val is not None:
                    pointer_info = f" -> 0x{val:X}"
        note_str = (" Note: " + note) if note else ""
        s = f"0x{offset:X} dec:{offset} | 1b:{u1}/{i1} 2b:{u2}/{i2} 4b:{u4}/{i4} float:{f4 if f4 is not None else 'N/A'}{pointer_info}{note_str}"
        self.hover_label.setText(s)
        # update inspector: show hover details
        self.update_inspector(offset)

    def update_inspector(self, hover_offset=None):
        # if explicit hover provided, use it; else prefer selection start; else hovered from view
        if hover_offset is None:
            if self.view.sel_start is not None:
                off = min(self.view.sel_start, self.view.sel_end)
            else:
                off = self.view.hovered if (self.view.hovered is not None and self.view.hovered>=0) else None
        else:
            off = hover_offset
        self.inspector.clear()
        if off is None or off < 0 or off >= len(self.view.data):
            root = QtWidgets.QTreeWidgetItem(["No selection/hover", ""])
            self.inspector.addTopLevelItem(root); return
        b = self.view.data
        # basic info
        t_addr = QtWidgets.QTreeWidgetItem(["Absolute offset", f"0x{off:X}"])
        rel = off - (0 if self.view.absolute_offset else self.view.header_size)
        t_rel = QtWidgets.QTreeWidgetItem(["GTA payload offset", f"0x{rel:X}"])
        self.inspector.addTopLevelItem(t_addr); self.inspector.addTopLevelItem(t_rel)
        # interprets
        uint8 = read_le_uint(b, off, 1); int8 = read_le_int(b, off, 1)
        uint16 = read_le_uint(b, off, 2); int16 = read_le_int(b, off, 2)
        uint32 = read_le_uint(b, off, 4); int32 = read_le_int(b, off, 4)
        flt = read_float(b, off)
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["uint8", str(uint8)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["int8", str(int8)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["uint16", str(uint16)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["int16", str(int16)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["uint32", str(uint32)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["int32", str(int32)]))
        self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["float", ("%.6g" % flt) if flt is not None else "N/A"]))
        # pointer info (if any)
        for pf in self.view.pointer_fields:
            if pf <= off < pf+4:
                val = read_le_uint(b, pf, 4)
                item = QtWidgets.QTreeWidgetItem(["pointer_field_start", f"0x{pf:X} -> 0x{val:X}" if val is not None else f"0x{pf:X}"])
                self.inspector.addTopLevelItem(item)
                break
        # note
        note = self.view.notes.get(off, "")
        if note:
            self.inspector.addTopLevelItem(QtWidgets.QTreeWidgetItem(["note", note]))

    # ---------- settings (extended) ----------
    def open_settings(self):
        dlg = QtWidgets.QDialog(self); dlg.setWindowTitle("Settings"); layout=QtWidgets.QFormLayout(dlg)
        bg = QtWidgets.QLineEdit(self.view.col_bg.name()); hexc = QtWidgets.QLineEdit(self.view.col_hex.name())
        pointer = QtWidgets.QLineEdit(self.view.col_pointer.name()); pad = QtWidgets.QLineEdit(self.view.col_pad.name())
        ascii_col = QtWidgets.QLineEdit(self.view.col_ascii.name())
        font_size = QtWidgets.QSpinBox(); font_size.setRange(8,28); font_size.setValue(self.view.font_size)
        hist_limit = QtWidgets.QSpinBox(); hist_limit.setRange(1,5000); hist_limit.setValue(self.history_limit)
        layout.addRow("Background color:", bg); layout.addRow("Hex color:", hexc); layout.addRow("Pointer color:", pointer)
        layout.addRow("Pad color:", pad); layout.addRow("ASCII color:", ascii_col); layout.addRow("Font size:", font_size)
        layout.addRow("History limit:", hist_limit)
        btns = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel); layout.addRow(btns)
        btns.accepted.connect(dlg.accept); btns.rejected.connect(dlg.reject)
        if dlg.exec_() == QtWidgets.QDialog.Accepted:
            try:
                self.view.col_bg = QtGui.QColor(bg.text()); self.view.col_hex = QtGui.QColor(hexc.text())
                self.view.col_pointer = QtGui.QColor(pointer.text()); self.view.col_pad = QtGui.QColor(pad.text())
                self.view.col_ascii = QtGui.QColor(ascii_col.text())
                self.view.font_size = font_size.value(); self.view.font = QtGui.QFont(self.view.font_family, self.view.font_size)
                self.history_limit = hist_limit.value()
                self.view.fm = QtGui.QFontMetrics(self.view.font)
                self.view.char_w = self.view.fm.horizontalAdvance('0'); self.view.char_h = self.view.fm.height()
                self.view.addr_area_w = self.view.char_w * 8 + self.view.char_w
                self.view.hex_byte_w = self.view.char_w * 2 + self.view.char_w; self.view.middle_gap = self.view.char_w * 2
                self.view.update_scrollbars(); self.view.viewport().update()
            except Exception as e:
                QtWidgets.QMessageBox.warning(self, "Settings", f"Bad value: {e}")

# ---------- запуск ----------
def main():
    app = QtWidgets.QApplication(sys.argv)
    win = MainWindow(); win.show()
    sys.exit(app.exec_())

if __name__ == "__main__":
    main()
