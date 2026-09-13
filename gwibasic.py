# ==============================================================================
# PROJECT: GW-BASIC Remake (Python Implementation)
# Inspired by the original Microsoft GW-BASIC interpreter (First Released: 1983)
# ==============================================================================
# Apache License, Version 2.0 Compliance Notice:
# 
# This program made extensive use of the Qwen 3.8 27B AI model. 
# The AI model component is licensed under the Apache License, Version 2.0 
# (the "License"); you may not use this component except in compliance with 
# the License. You may obtain a copy of the License at:
#
#     http://apache.org
#
# Original AI Model Copyright Notice:
# Copyright (c) 2026 Alibaba Group Holding Limited or its affiliates.
# ==============================================================================

#!/usr/bin/env python3
"""

Usage:
    python gwbasic_test.py                 # interactive REPL
    python gwbasic_test.py program.bas     # run a file
"""

import ctypes
import math
import os
import queue
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
import time


# --------------------------------------------------------------------------- #
# Stdin/stdout/stderr guards for frozen (windowed) builds.
#
# A PyInstaller ``--windowed`` build runs with no console, so ``sys.stdout``,
# ``sys.stderr`` and ``sys.stdin`` are all ``None``.  The very first
# ``sys.stdout.write`` (the default ``output_func`` bound at REPL construction,
# see ``__init__`` / ``output_func``) would then raise ``AttributeError:
# 'NoneType' object has no attribute 'write'`` and the windowed app would die
# on startup before the graphics window even appears.  When a real console is
# present (``python wayne.py`` or a redirected/terminal run) these are already
# valid objects and nothing below changes.  Only the frozen windowed case is
# affected: output goes to a no-op stream (the open graphics window is the real
# display, and IoDevice routes program/interpreter text there) and input is a
# stream that reports "not a tty" and yields EOF, so the REPL's non-interactive
# fallbacks engage instead of crashing on a missing console.
class _NoOpTextIO:
    """Drop-in replacement for a missing stdout/stderr stream.

    Accepts any write() call and discards the text; isatty() reports False so
    code that probes for an interactive console takes its plain-display path.
    """

    def __init__(self):
        self.encoding = 'utf-8'

    def write(self, text):
        return 0

    def flush(self):
        pass

    def isatty(self):
        return False

    def __getattr__(self, name):
        # Any other stream method that gets probed is a no-op returning an
        # empty/neutral value instead of raising AttributeError.
        return lambda *a, **k: ''


class _EOFTextIO:
    """Drop-in replacement for a missing stdin stream.

    isatty() reports False and readline() always yields EOF, so ``input()`` and
    the line-reading PAUSE/INPUT paths terminate cleanly rather than blocking
    on, or crashing from, a console that does not exist.  Key input in the
    windowed app comes from the graphics window, not stdin, so this only
    affects the (unused-when-a-window-is-open) console fallbacks.
    """

    def __init__(self):
        self.encoding = 'utf-8'

    def readline(self, size=-1):
        return ''

    def read(self, size=-1):
        return ''

    def isatty(self):
        return False

    def fileno(self):
        raise OSError(0, 'No file descriptor (no console in windowed build)')

    def __getattr__(self, name):
        return lambda *a, **k: ''


if sys.stdout is None:
    sys.stdout = _NoOpTextIO()
if sys.stderr is None:
    sys.stderr = _NoOpTextIO()
if sys.stdin is None:
    sys.stdin = _EOFTextIO()


# #############################################################################
# Errors (from gw_errors.py)
# #############################################################################

class BasicError(Exception):
    """A runtime or syntax error in the BASIC program.

    ``code`` optionally carries the GW-BASIC error number (used by the
    ERROR statement so that ERR keeps the requested number).
    """

    def __init__(self, message, code=None):
        super().__init__(message)
        self.code = code


# #############################################################################
# File I/O (from gw_files.py)
# #############################################################################

def _is_single_valued(value):
    """True if <value> is exactly representable as an IEEE-754 single.

    The interpreter stores single-precision results already rounded to a
    single, and double-precision results at full double precision.  A value
    that equals its single-precision rounding came from the single path (or
    is an integer) and only needs single-precision text to round-trip; a
    value that does not is a genuine double and must be written with its full
    shortest round-tripping decimal so a later read recovers it exactly.
    """
    if isinstance(value, int):
        return True
    if not math.isfinite(value):
        return True
    return struct.unpack('f', struct.pack('f', value))[0] == value


def _fmt_single_file(value):
    """Write a single-precision value as decimal text that round-trips exactly.

    A single is a 4-byte IEEE-754 value (manual 6.1.1/6.2.4); the file text
    must reproduce it exactly on INPUT#/GET.  Fixed-point is used when it can
    carry seven significant digits (1e-5 <= |v| < 1e7) - the normal range,
    where the text matches what a PRINT shows (975.3421 -> "975.3421");
    otherwise the shortest exponential form that round-trips is used.  This is
    verified to recover every representable single (unlike a fixed 6-digit
    format, which loses 8-digit values such as 123456.789).
    """
    if value == 0:
        return "0"
    if 1e-5 <= abs(value) < 1e7:
        for i in range(12):
            s = '%.*f' % (i, value)
            if struct.unpack('f', struct.pack('f', float(s)))[0] == value:
                return s
    for i in range(12):
        s = format(value, '.%dE' % i)
        if struct.unpack('f', struct.pack('f', float(s)))[0] == value:
            return s
    return format(value, '.11E')


def _fmt_num(value):
    """Format a numeric value to file text (PUT/WRITE#) at its precision
    (manual 6.1.1): integers as bare digits, singles and doubles as the
    shortest decimal that round-trips exactly so a later read recovers the
    value bit-for-bit."""
    if isinstance(value, int):
        return str(value)
    if not math.isfinite(value):
        return str(value)
    if value == int(value) and abs(value) < 1e15:
        return str(int(value))
    if _is_single_valued(value):
        return _fmt_single_file(value)
    # Double precision: shortest round-tripping decimal; exponential form only
    # outside the fifteen-digit fixed range.
    if abs(value) >= 1e15 or (value != 0 and abs(value) < 1e-5):
        return "%.10E" % value
    return repr(value)


class FileHandle:
    def __init__(self, mode, filename, record_len, f):
        self.mode = mode
        self.filename = filename
        self.record_len = record_len
        self.f = f
        self.pos = 0
        self.rec = 0
        # INPUT# values left over on a line (more values than targets) are
        # kept here and consumed first by the next INPUT# on this channel.
        self._input_pending = []


class FileIO:
    def __init__(self):
        self.files = {}

    # -- open / close -------------------------------------------------------- #
    def open(self, mode, filenum, filename, record_len=0):
        mode = mode.upper()
        filename = str(filename)
        # Opening a file for OUTPUT or APPEND fails if the file is already
        # open in any mode ("File already open", manual OPEN page).
        if mode in ('OUTPUT', 'APPEND'):
            for fh in self.files.values():
                if fh.filename.lower() == filename.lower():
                    raise BasicError("File already open (55)")
        try:
            if mode == 'INPUT':
                if not os.path.exists(filename):
                    raise BasicError("File not found (53)")
                f = open(filename, 'r', newline='')
            elif mode == 'OUTPUT':
                f = open(filename, 'w', newline='')
            elif mode == 'APPEND':
                f = open(filename, 'a', newline='')
            elif mode == 'RANDOM':
                f = open(filename, 'r+b') if os.path.exists(filename) else open(filename, 'w+b')
            elif mode == 'BINARY':
                f = open(filename, 'r+b') if os.path.exists(filename) else open(filename, 'w+b')
            else:
                raise BasicError("Bad file mode (54)")
        except BasicError:
            raise
        except OSError as e:
            raise BasicError("File error: %s" % e)
        # Re-OPENing an already-open file number reassigns the channel: the
        # previous file on that number is closed (and its output flushed)
        # instead of leaking.  Done only after the new open succeeded, so a
        # failed OPEN leaves the previous file untouched.
        old = self.files.pop(filenum, None)
        if old is not None:
            old.f.close()
        self.files[filenum] = FileHandle(mode, filename, int(record_len), f)

    def _get(self, filenum):
        if filenum not in self.files:
            raise BasicError("Bad file number (52)")
        return self.files[filenum]

    def close(self, filenum=None):
        if filenum is None:
            for fh in self.files.values():
                fh.f.close()
            self.files = {}
        else:
            fh = self._get(filenum)
            fh.f.close()
            del self.files[filenum]

    # -- sequential output --------------------------------------------------- #
    def print_to(self, filenum, text, newline=True):
        fh = self._get(filenum)
        if fh.mode not in ('OUTPUT', 'APPEND'):
            raise BasicError("Bad file mode (54)")
        fh.f.write(text + ('\n' if newline else ''))
        fh.f.flush()

    def write_to(self, filenum, items, fmt=None):
        # Legacy single-formatter entry point (e.g. direct calls without kinds).
        return self.write_typed(filenum, items,
                                [ (fmt or _fmt_num) for _ in items ])

    def write_typed(self, filenum, items, fmts):
        """WRITE #n, items: each item uses its own formatter (fmts[i] formats
        items[i] at that value's precision)."""
        fh = self._get(filenum)
        if fh.mode not in ('OUTPUT', 'APPEND'):
            raise BasicError("Bad file mode (54)")
        parts = []
        for value, fmt in zip(items, fmts):
            if isinstance(value, str):
                parts.append('"%s"' % value.replace('"', '""'))
            else:
                parts.append(fmt(value))
        # WRITE separates items with a comma and a space (manual WRITE).
        fh.f.write(", ".join(parts) + "\n")
        fh.f.flush()

    # -- sequential input ---------------------------------------------------- #
    def read_line(self, filenum):
        fh = self._get(filenum)
        if fh.mode not in ('INPUT',):
            raise BasicError("Bad file mode (54)")
        line = fh.f.readline()
        if line == '':
            raise BasicError("Input past end (62)")
        return line.rstrip('\r\n')

    def line_input(self, filenum, var_name=None):
        line = self.read_line(filenum)
        return line

    @staticmethod
    def _split_unquoted_commas(line):
        """Split a keyboard INPUT response on commas outside of quotes.

        A double quote opens a quoted item; the next quote closes it, and
        any commas in between belong to the string (manual INPUT: quoted
        data may contain commas), so '"A,B"' is one item.  Everything else
        is handled exactly as a plain comma split - including empty items
        from a trailing comma and unquoted text - so only quoted-comma
        input changes behavior versus the historical line.split(',').
        Unlike _split_input_line() there is no zone re-splitting and no
        self-delimiting-quote rule: those are INPUT# file-format rules.
        """
        parts = []
        cur = []
        in_quote = False
        for c in line:
            if c == '"':
                in_quote = not in_quote
                cur.append(c)
            elif c == ',' and not in_quote:
                parts.append(''.join(cur))
                cur = []
            else:
                cur.append(c)
        parts.append(''.join(cur))
        return parts

    @staticmethod
    def _split_input_line(line):
        """Split one INPUT# source line into raw value tokens.

        Handles both comma-delimited and zone-delimited (the default PRINT#
        output, which pads each value into a 14-character field with no
        commas) layouts.  A quoted string field is kept whole even if it
        contains commas.  Per manual INPUTF a quoted string may not
        contain a double quotation mark as a character: the second
        quotation mark always terminates the string, so "" has no special
        meaning - line "ABC""DEF",5 yields the items ABC, DEF and 5.  A
        quoted item therefore ends at its closing quote even when no
        comma follows it, and the spaces after the closing quote are the
        leading spaces of the next item.
        """
        fields = []
        cur = []
        i = 0
        n = len(line)
        in_quote = False
        just_quoted = False
        while i < n:
            c = line[i]
            if in_quote:
                if c == '"':
                    # Second quote terminates the quoted item (manual
                    # INPUTF); the item ends here even if the next
                    # character is not a comma.
                    in_quote = False
                    cur.append(c)
                    fields.append(''.join(cur))
                    cur = []
                    just_quoted = True
                else:
                    cur.append(c)
            else:
                if c == '"':
                    in_quote = True
                    cur.append(c)
                elif c == ',':
                    if cur or not just_quoted:
                        # A comma immediately after a quoted item is just
                        # a separator: the quoted item is self-
                        # delimiting, so it does not open an empty slot.
                        fields.append(''.join(cur))
                        cur = []
                    just_quoted = False
                elif not cur and just_quoted and c.isspace():
                    # Leading spaces of the next item after a quoted
                    # item are ignored (manual INPUTF).
                    pass
                else:
                    cur.append(c)
                    just_quoted = False
            i += 1
        if in_quote:
            # Unterminated quote: keep the remainder as one field.
            fields.append(''.join(cur))
        elif cur or not just_quoted:
            # Line ends right after a quoted item: no empty tail field.
            fields.append(''.join(cur))
        # A single field that holds several space-padded values (the zone
        # layout has no commas) is re-split on runs of 2+ spaces, keeping a
        # single space that belongs to the value (e.g. a number sign or the
        # gap inside an unquoted string).  A lone comma (or a truly empty
        # line) yields one empty field, matching the comma layout.
        parts = []
        for field in fields:
            if ',' not in field and field != field.strip():
                # Zone layout: values are separated by runs of 2+ spaces.
                # Splitting on the 2-char run leaves empty tokens inside
                # longer runs (pure zone padding) - drop them so a zone
                # line like " 1             2             3" yields
                # ["1", "2", "3"].
                parts.extend(p for p in field.split('  ') if p.strip())
            else:
                parts.append(field)
        return [p.strip() for p in parts]

    def input_from(self, filenum, var_names, target_types=None):
        # INPUT# reads the needed values from the file regardless of whether
        # they were written comma- or zone-delimited, and may span multiple
        # records/lines (manual INPUTF / Chapter 6).  Values are accumulated
        # across lines until every target has one; a line that runs out first
        # is "Input past end (62)".  Values left over on a line (more values
        # than targets) stay in the channel's pending list and are consumed
        # first by the next INPUT# on the same file number, matching the
        # manual's item stream (scanning continues at the current position).
        # The type of each value comes from the data, not the target's
        # previous value: quoted data is a string; unquoted data is a number
        # if it parses as one, otherwise a string.  Untyped targets accept
        # either (an untyped variable can hold a string, as in X=5 : X="HI");
        # $-suffixed or DEFSTR targets always take a string; declared numeric
        # targets (%, !, #, DEFINT/DEFSNG/DEFDBL) take numeric data only.
        fh = self._get(filenum)
        if fh.mode not in ('INPUT',):
            raise BasicError("Bad file mode (54)")
        values = []
        pending = list(fh._input_pending)
        # Live list: if a value below raises mid-line, the failed value has
        # been consumed and the rest of the line remains for the next INPUT#.
        fh._input_pending = pending
        while len(values) < len(var_names):
            if not pending:
                raw = fh.f.readline()
                if raw == '':
                    raise BasicError("Input past end (62)")
                pending = list(self._split_input_line(raw.rstrip('\r\n')))
                fh._input_pending = pending
            part = pending.pop(0)
            name = var_names[len(values)]
            if target_types is not None:
                vt = target_types.get(name.upper(), 'default')
            else:
                vt = 'string' if name.endswith('$') else 'default'
            if vt not in ('string', 'default'):
                # Declared numeric target (%, !, # or DEFINT/DEFSNG/DEFDBL):
                # numeric data only (manual INPUTF: the type must match the
                # type specified by the variable name).
                try:
                    v = float(part)
                    if math.isinf(v):
                        # Out-of-range value in the file: same
                        # "Overflow" error as an out-of-range
                        # constant (see parse_number).
                        raise BasicError("Overflow")
                    val = int(v) if v == int(v) else v
                    if isinstance(val, float) and classify_number(part) == 'single':
                        val = round_single(val)
                    values.append(val)
                except ValueError:
                    raise BasicError("Type mismatch")
            elif (part.startswith('"') and part.endswith('"')
                    and len(part) >= 2):
                # Quoted data is a string for any remaining target
                # (manual INPUTF): the item is the characters between
                # the first and second quotation marks, verbatim - the
                # second quote always terminates the string, so "" is
                # not an escape.
                values.append(part[1:-1])
            elif vt == 'string':
                # String-only target ($ name or DEFSTR): unquoted data is
                # taken verbatim as a string (a string item ends at
                # comma/CR/LF, so e.g. "42" becomes the string "42").
                values.append(part)
            else:
                # Untyped target: numeric if the data parses as a number,
                # otherwise a string - an untyped variable can hold either.
                try:
                    v = float(part)
                    if math.isinf(v):
                        # Out-of-range value in the file: same
                        # "Overflow" error as an out-of-range
                        # constant (see parse_number).
                        raise BasicError("Overflow")
                    val = int(v) if v == int(v) else v
                    if isinstance(val, float) and classify_number(part) == 'single':
                        val = round_single(val)
                    values.append(val)
                except ValueError:
                    values.append(part)
        return values

    def input_chars(self, filenum, n):
        """INPUT$(n, [#]filenum): read up to n characters from a file."""
        fh = self._get(filenum)
        if fh.mode not in ('INPUT',):
            raise BasicError("Bad file mode (54)")
        data = fh.f.read(max(0, int(n)))
        return data

    # -- random / binary records -------------------------------------------- #
    def _record_bytes(self, filenum, recnum):
        fh = self._get(filenum)
        if fh.record_len <= 0:
            raise BasicError("Illegal function call")
        recnum = int(recnum)
        # Manual Appendix A 63: PUT/GET record number > 16,777,215 or 0.
        if recnum < 1 or recnum > 16777215:
            raise BasicError("Bad record number (63)")
        offset = (recnum - 1) * fh.record_len
        return fh, offset

    def next_rec(self, filenum):
        """The next available record number (last used + 1)."""
        fh = self._get(filenum)
        return fh.rec + 1

    def put(self, filenum, recnum, is_string, value, fmt=None):
        fh = self._get(filenum)
        if fh.mode not in ('RANDOM', 'BINARY'):
            raise BasicError("Bad file mode (54)")
        fmt = fmt or _fmt_num
        if fh.mode == 'BINARY':
            data = (value if isinstance(value, str) else fmt(value))
            data = data.encode('latin-1', errors='replace')
            fh.f.seek(fh.pos)
            fh.f.write(data)
            fh.pos += len(data)
            fh.f.flush()
            return
        _, offset = self._record_bytes(filenum, recnum)
        s = value if isinstance(value, str) else fmt(value)
        if len(s) < fh.record_len:
            s = s + ' ' * (fh.record_len - len(s))
        else:
            s = s[:fh.record_len]
        data = s.encode('latin-1', errors='replace')
        fh.f.seek(offset)
        fh.f.write(data)
        fh.f.flush()
        fh.rec = int(recnum)

    def get(self, filenum, recnum, is_string):
        fh = self._get(filenum)
        if fh.mode not in ('RANDOM', 'BINARY'):
            raise BasicError("Bad file mode (54)")
        if fh.mode == 'BINARY':
            n = fh.record_len if fh.record_len > 0 else 1
            data = fh.f.read(n)
            if not data:
                raise BasicError("Input past end (62)")
            fh.pos += len(data)
            s = data.decode('latin-1', errors='replace')
            return s if is_string else _to_num(s)
        _, offset = self._record_bytes(filenum, recnum)
        fh.f.seek(offset)
        data = fh.f.read(fh.record_len)
        if len(data) < fh.record_len:
            # A RANDOM record that was never written (or whose tail was never
            # allocated) reads as blanks (manual GETF / real GW-BASIC);
            # BINARY stream EOF above already errors, so only fill here.
            data = data + b' ' * (fh.record_len - len(data))
        fh.rec = int(recnum)
        s = data.decode('latin-1', errors='replace').rstrip()
        return s if is_string else _to_num(s)

    def get_record(self, filenum, recnum):
        """Return the raw record string (used to populate FIELD variables)."""
        fh = self._get(filenum)
        if fh.mode not in ('RANDOM', 'BINARY'):
            raise BasicError("Bad file mode (54)")
        _, offset = self._record_bytes(filenum, recnum)
        fh.f.seek(offset)
        data = fh.f.read(fh.record_len)
        if len(data) < fh.record_len:
            # Never-written RANDOM record reads as blanks (see get()).
            data = data + b' ' * (fh.record_len - len(data))
        fh.rec = int(recnum)
        return data.decode('latin-1', errors='replace')

    def record_len(self, filenum):
        return self._get(filenum).record_len

    def put_record(self, filenum, recnum, record):
        """Write a full record string (used for FIELD-based PUT)."""
        fh = self._get(filenum)
        if fh.mode not in ('RANDOM', 'BINARY'):
            raise BasicError("Bad file mode (54)")
        if fh.mode == 'BINARY':
            data = record.encode('latin-1', errors='replace')
            fh.f.seek(fh.pos)
            fh.f.write(data)
            fh.pos += len(data)
            fh.f.flush()
            return
        _, offset = self._record_bytes(filenum, recnum)
        s = record
        if len(s) < fh.record_len:
            s = s + ' ' * (fh.record_len - len(s))
        else:
            s = s[:fh.record_len]
        data = s.encode('latin-1', errors='replace')
        fh.f.seek(offset)
        fh.f.write(data)
        fh.f.flush()
        fh.rec = int(recnum)

    def seek(self, filenum, var_name=None):
        fh = self._get(filenum)
        if fh.mode == 'RANDOM':
            # The record number last read/written (0 before any GET/PUT).
            return fh.rec
        # BINARY: return byte position
        fh.f.flush()
        return fh.f.tell()

    def loc(self, filenum):
        # Random files: the record number last read/written.  Sequential
        # files: the number of 128-byte blocks read/written (manual LOC).
        fh = self._get(filenum)
        fh.f.flush()
        if fh.mode == 'RANDOM':
            return fh.rec
        pos = fh.f.tell()
        if pos <= 0:
            return 0
        return (pos + 127) // 128

    def eof(self, filenum):
        # Returns -1 (true) when the end of a sequential or communications
        # file has been reached, or 0 if it has not (manual EOF).  We check
        # whether the current position is already at the end of the file; the
        # seek is fully restored, so a following INPUT#/GET still reads the
        # next record.  Text files do not support peek(), so this is the
        # portable way to test for end of file.
        fh = self._get(filenum)
        fh.f.flush()
        pos = fh.f.tell()
        fh.f.seek(0, 2)
        size = fh.f.tell()
        fh.f.seek(pos)
        return -1 if pos >= size else 0

    def lof(self, filenum):
        fh = self._get(filenum)
        fh.f.flush()
        pos = fh.f.tell()
        fh.f.seek(0, 2)
        size = fh.f.tell()
        fh.f.seek(pos)
        return size

    # -- file management ----------------------------------------------------- #
    def kill(self, filename):
        filename = str(filename)
        for fh in self.files.values():
            if fh.filename.lower() == filename.lower():
                raise BasicError("File already open (55)")
        if not os.path.exists(filename):
            raise BasicError("File not found (53)")
        os.remove(filename)

    def dir(self, pattern):
        pattern = str(pattern) if pattern else '*'
        try:
            entries = []
            base = '.'
            if os.path.isdir(pattern):
                base = pattern
            for name in os.listdir(base):
                full = os.path.join(base, name)
                if _fnmatch(name, pattern if not os.path.isdir(pattern) else '*'):
                    entries.append(name + ('/' if os.path.isdir(full) else ''))
            return "\n".join(entries)
        except OSError:
            return ""


def _to_num(s):
    try:
        f = float(s)
    except (ValueError, TypeError):
        return 0
    if math.isinf(f):
        # A numeric record holding a value outside the number format
        # overflows on read (see parse_number).
        raise BasicError("Overflow")
    return int(f) if f == int(f) else f


def _fnmatch(name, pattern):
    import fnmatch
    return fnmatch.fnmatch(name, pattern)


# #############################################################################
# Screen emulation (from gw_screen.py)
# #############################################################################

# 16-color VGA palette (R, G, B)
PALETTE = [
    (0, 0, 0), (0, 0, 170), (0, 170, 0), (0, 170, 170),
    (170, 0, 0), (170, 0, 170), (170, 85, 0), (170, 170, 170),
    (85, 85, 85), (85, 85, 255), (85, 255, 85), (85, 255, 255),
    (255, 85, 85), (255, 85, 255), (255, 255, 85), (255, 255, 255),
]

# Precomputed "#rrggbb" strings for the 16 palette colors (used for the
# text renderer and the PPM fallback path in _render_gfx).
PALETTE_HEX = ["#%02x%02x%02x" % c for c in PALETTE]
# Precomputed 3-byte RGB chunks for the 16 palette colors.  Used to build a
# single raw PPM image in one shot for the graphics blit (far faster than one
# Tk put() call per pixel).
PALETTE_RGB3 = [bytes(c) for c in PALETTE]

# ---------------------------------------------------------------------------
# Dynamic RGB colors (RGB function).
#
# The pixel buffer stores COLOR INDEXES, not per-pixel RGB triples: 0-15 are
# the fixed palette entries above, and index 16+k names the k-th distinct
# color created by the RGB(r,g,b) function.  Storing small indexes keeps
# POINT/GET and the incremental-blit diffing cheap (a 2000x1300 screen
# is 2.6M pixels) and lets any number of distinct colors coexist; the render
# path maps index -> real RGB through the LUTs built from DYN_RGB3/DYN_HEX.
# Legacy programs passing an undefined index >= 16 (or a negative color) get
# the classic value % 16 wrap, so old code is unaffected.
DYN_RGB3 = []    # DYN_RGB3[k] = bytes(r,g,b) for color index 16+k
DYN_HEX = []     # DYN_HEX[k] = "#rrggbb" for color index 16+k
_RGB_DUPES = {}  # (r,g,b) -> palette index
_RGB_NEXT = 16


def _rgb_alloc(r, g, b):
    """Allocate (or reuse) a dynamic palette index for the exact RGB color.

    Returns an index >= 16.  The same (r,g,b) always gives the same index,
    and indexes are dense (16, 17, 18, ...).  Each of r/g/b must be within
    0-255, otherwise "Illegal function call"."""
    global _RGB_NEXT
    r, g, b = int(r), int(g), int(b)
    for v in (r, g, b):
        if v < 0 or v > 255:
            raise BasicError("Illegal function call")
    key = (r, g, b)
    idx = _RGB_DUPES.get(key)
    if idx is None:
        idx = _RGB_NEXT
        _RGB_NEXT += 1
        _RGB_DUPES[key] = idx
        DYN_RGB3.append(bytes((r, g, b)))
        DYN_HEX.append("#%02x%02x%02x" % (r, g, b))
    return idx


def _resolve_color(c):
    """Resolve a color expression to the pixel-buffer index to store.

    0-15: the fixed palette, unchanged.  16..15+len(DYN_RGB3): a defined
    dynamic RGB color, stored verbatim.  Anything else (an undefined index
    >= 16, a negative, a 256-color-era value): the classic % 16 wrap, so
    legacy programs store exactly what they always stored."""
    c = int(c)
    if c >= 0 and c <= 15:
        return c
    if 16 <= c <= 15 + len(DYN_RGB3):
        return c
    return c % 16


def _reset_dynamic_rgb():
    """Restore the dynamic RGB table to its fresh-interpreter state.

    Called at the start of every RUN (reset_state, including the in-program
    RUN / NEW statement paths) and on the NEW command: a new run numbers
    RGB() colors from index 16 again, exactly like a freshly started
    interpreter, instead of continuing where the previous run left off.
    The fixed 0-15 palette is untouched, and no live pixel can hold an
    index from the cleared table: a graphics SCREEN replaces the whole
    buffer (set_mode), so the render LUTs (PALETTE + DYN_*) and the pixel
    buffer always belong to the same generation."""
    global _RGB_NEXT
    _RGB_DUPES.clear()
    _RGB_NEXT = 16
    DYN_RGB3.clear()
    DYN_HEX.clear()


# 8x8 bitmap font for the monitor text page (printable ASCII 32-126).
# Rasterized from a proportional sans-serif at high supersampling: caps are
# 6px tall with the baseline on row 6, leaving the 8th row for descenders.
# Each glyph is 8 bytes, top row first, bit 7 (MSB) = leftmost pixel.  The
# glyphs are composited straight into the pixel buffer in graphics mode
# (see Screen._blit_glyph), so text lives in the same surface GET
# captures - exactly like the old CGA/EGA monitor.
FONT_8X8 = {
    32: b'\x00\x00\x00\x00\x00\x00\x00\x00',
    33: b'\x18\x18\x10\x00\x00\x18\x00\x00',
    34: b'\x18\x00\x00\x00\x00\x00\x00\x00',
    35: b'\x14\x3e\x24\x7e\x28\x28\x00\x00',
    36: b'\x20\x30\x1c\x04\x24\x3c\x00\x00',
    37: b'\xa4\xa8\x68\x16\x15\x26\x00\x00',
    38: b'\x28\x38\x38\x4c\x4c\x3e\x00\x00',
    39: b'\x10\x10\x00\x00\x00\x00\x00\x00',
    40: b'\x10\x10\x10\x10\x10\x10\x10\x08',
    41: b'\x08\x08\x08\x08\x08\x08\x18\x10',
    42: b'\x00\x24\x18\x18\x24\x00\x00\x00',
    43: b'\x10\x18\x3c\x18\x10\x00\x00\x00',
    44: b'\x00\x00\x00\x00\x00\x18\x08\x00',
    45: b'\x00\x00\x00\x18\x00\x00\x00\x00',
    46: b'\x00\x00\x00\x00\x00\x18\x00\x00',
    47: b'\x08\x08\x10\x10\x10\x10\x00\x00',
    48: b'\x24\x24\x24\x24\x24\x3c\x00\x00',
    49: b'\x18\x08\x08\x08\x08\x08\x00\x00',
    50: b'\x24\x04\x0c\x18\x30\x3c\x00\x00',
    51: b'\x24\x0c\x0c\x04\x24\x3c\x00\x00',
    52: b'\x1c\x1c\x2c\x7c\x0c\x0c\x00\x00',
    53: b'\x20\x38\x24\x04\x24\x3c\x00\x00',
    54: b'\x24\x38\x24\x24\x24\x3c\x00\x00',
    55: b'\x0c\x08\x18\x10\x10\x10\x00\x00',
    56: b'\x24\x3c\x3c\x24\x24\x3c\x00\x00',
    57: b'\x24\x24\x24\x1c\x24\x3c\x00\x00',
    58: b'\x00\x18\x00\x00\x00\x18\x00\x00',
    59: b'\x00\x18\x00\x00\x00\x18\x08\x00',
    60: b'\x04\x18\x20\x18\x04\x00\x00\x00',
    61: b'\x00\x3c\x00\x3c\x00\x00\x00\x00',
    62: b'\x20\x18\x04\x18\x20\x00\x00\x00',
    63: b'\x24\x04\x08\x18\x00\x18\x00\x00',
    64: b'\x18\x26\x5e\xa4\xaa\x3c\x42\x1c',
    65: b'\x18\x2c\x24\x3c\x42\x42\x00\x00',
    66: b'\x44\x64\x7c\x46\x46\x7c\x00\x00',
    67: b'\x42\x40\x40\x40\x62\x3c\x00\x00',
    68: b'\x46\x42\x42\x42\x46\x7c\x00\x00',
    69: b'\x40\x40\x7c\x40\x40\x7e\x00\x00',
    70: b'\x60\x60\x7c\x60\x60\x60\x00\x00',
    71: b'\x42\x40\x4e\x42\x42\x3e\x00\x00',
    72: b'\x42\x42\x7e\x42\x42\x42\x00\x00',
    73: b'\x18\x18\x18\x18\x18\x18\x00\x00',
    74: b'\x04\x04\x04\x04\x24\x3c\x00\x00',
    75: b'\x48\x50\x78\x48\x44\x46\x00\x00',
    76: b'\x20\x20\x20\x20\x20\x3c\x00\x00',
    77: b'\xe7\xe7\xe7\xdb\xdb\xdb\x00\x00',
    78: b'\x62\x52\x5a\x4a\x46\x46\x00\x00',
    79: b'\x42\x42\xc3\x42\x42\x3c\x00\x00',
    80: b'\x42\x46\x7c\x40\x40\x40\x00\x00',
    81: b'\x42\x42\xc2\x42\x4e\x3e\x00\x00',
    82: b'\x46\x46\x7c\x4c\x44\x42\x00\x00',
    83: b'\x66\x30\x1c\x02\x42\x3c\x00\x00',
    84: b'\x18\x18\x18\x18\x18\x18\x00\x00',
    85: b'\x42\x42\x42\x42\x66\x3c\x00\x00',
    86: b'\x42\x24\x24\x3c\x18\x18\x00\x00',
    87: b'\x00\x5a\x5a\x5a\x66\x24\x00\x00',
    88: b'\x34\x18\x18\x3c\x24\x42\x00\x00',
    89: b'\x24\x3c\x18\x18\x18\x18\x00\x00',
    90: b'\x04\x08\x18\x30\x20\x7e\x00\x00',
    91: b'\x10\x10\x10\x10\x10\x10\x10\x18',
    92: b'\x10\x10\x00\x08\x08\x08\x00\x00',
    93: b'\x08\x08\x08\x08\x08\x08\x08\x18',
    94: b'\x18\x24\x24\x00\x00\x00\x00\x00',
    95: b'\x00\x00\x00\x00\x00\x00\x00\x7e',
    96: b'\x08\x08\x00\x00\x00\x00\x00\x00',
    97: b'\x00\x3c\x04\x3c\x24\x3c\x00\x00',
    98: b'\x20\x3c\x24\x24\x24\x3c\x00\x00',
    99: b'\x00\x3c\x20\x20\x24\x3c\x00\x00',
    100: b'\x04\x3c\x24\x24\x24\x3c\x00\x00',
    101: b'\x00\x3c\x24\x3c\x24\x3c\x00\x00',
    102: b'\x10\x18\x10\x10\x10\x10\x00\x00',
    103: b'\x00\x3c\x24\x24\x24\x3c\x24\x3c',
    104: b'\x20\x3c\x24\x24\x24\x24\x00\x00',
    105: b'\x00\x18\x18\x18\x18\x18\x00\x00',
    106: b'\x00\x08\x08\x08\x08\x08\x08\x18',
    107: b'\x20\x28\x30\x38\x28\x24\x00\x00',
    108: b'\x18\x18\x18\x18\x18\x18\x00\x00',
    109: b'\x00\xfe\xdb\xd9\xd9\xd9\x00\x00',
    110: b'\x00\x3c\x24\x24\x24\x24\x00\x00',
    111: b'\x00\x3c\x64\x64\x24\x3c\x00\x00',
    112: b'\x00\x3c\x24\x24\x24\x3c\x20\x20',
    113: b'\x00\x3c\x24\x24\x24\x3c\x04\x04',
    114: b'\x00\x38\x30\x30\x30\x30\x00\x00',
    115: b'\x00\x3c\x20\x1c\x24\x3c\x00\x00',
    116: b'\x18\x18\x10\x10\x10\x18\x00\x00',
    117: b'\x00\x24\x24\x24\x24\x3c\x00\x00',
    118: b'\x00\x24\x24\x38\x18\x18\x00\x00',
    119: b'\x00\x5a\x5a\x5a\x6c\x24\x00\x00',
    120: b'\x00\x24\x18\x18\x3c\x24\x00\x00',
    121: b'\x00\x24\x24\x18\x18\x18\x10\x30',
    122: b'\x00\x3c\x08\x10\x30\x3c\x00\x00',
    123: b'\x18\x18\x10\x10\x10\x18\x18\x08',
    124: b'\x10\x10\x10\x10\x10\x10\x10\x10',
    125: b'\x18\x18\x08\x08\x08\x18\x18\x10',
    126: b'\x00\x00\x7e\x00\x00\x00\x00\x00',
}

# TEXTFONT instruction: the faces the user can select for the monitor
# text.  Keyed by the face name (matched case-insensitively); each value
# maps a weight suffix ('' = regular, 'b' = bold, 'i' = italic,
# 'bi' = bold italic) to the Windows .ttf file for that face.  A None
# entry means the family ships no separate file for that weight (Tahoma
# and Impact are single-face fonts), so the regular face stands in.
TEXTFONT_FACES = {
    'ARIAL':    {'': 'arial.ttf',   'b': 'arialbd.ttf',  'i': 'ariali.ttf',
                 'bi': 'arialbi.ttf'},
    'SEGOE':    {'': 'segoeui.ttf', 'b': 'segoeuib.ttf', 'i': 'segoeuii.ttf',
                 'bi': 'segoeuiz.ttf'},
    'COURIER':  {'': 'cour.ttf',    'b': 'courbd.ttf',   'i': 'couri.ttf',
                 'bi': 'courbi.ttf'},
    'GEORGIA':  {'': 'georgia.ttf', 'b': 'georgiab.ttf', 'i': 'georgiai.ttf',
                 'bi': 'georgiaz.ttf'},
    'TAHOMA':   {'': 'tahoma.ttf',  'b': None,           'i': None,
                 'bi': None},
    'CALIBRI':  {'': 'calibri.ttf', 'b': 'calibrib.ttf', 'i': 'calibrii.ttf',
                 'bi': 'calibriz.ttf'},
    'NEWTIMES': {'': 'times.ttf',   'b': 'timesbd.ttf',  'i': 'timesi.ttf',
                 'bi': 'timesbi.ttf'},
    'VERDANA':  {'': 'verdana.ttf', 'b': 'verdanab.ttf', 'i': 'verdanai.ttf',
                 'bi': 'verdanaz.ttf'},
    'TREBUCHET': {'': 'trebuc.ttf', 'b': 'trebucbd.ttf', 'i': 'trebucit.ttf',
                  'bi': 'trebucbi.ttf'},
    'CANADA':   {'': 'Candara.ttf', 'b': 'Candarab.ttf', 'i': 'Candarai.ttf',
                 'bi': 'Candaraz.ttf'},
    'IMPACT':   {'': 'impact.ttf',  'b': None,           'i': None,
                 'bi': None},
}
# TEXTFONT defaults: Arial, not bold, not italic (see Screen.textfont).
TEXTFONT_DEFAULT = ('ARIAL', False, False)
# The TEXTSIZE a program starts with: every RUN resets the monitor to
# TEXTSIZE_DEFAULT, TEXTRotate 0 and the default TEXTFONT face.
TEXTSIZE_DEFAULT = 11

# SCREEN modes (manual SCREENS): legal values are 0, 1, 2, 7, 8, 9, 10.
# Only mode 0 is a text mode; mode 7 is 320x200 EGA graphics (NOT text).
TEXT_MODES = (0,)
GFX_DIMS = {
    1: (200, 320), 2: (200, 640), 7: (200, 320), 8: (200, 640),
    9: (350, 640), 10: (350, 640),
}
LEGAL_SCREEN_MODES = (0, 1, 2, 7, 8, 9, 10)
# Maximum color index per graphics mode (manual SCREENS, Table 2).
GFX_COLOR_MAX = {1: 3, 2: 1, 7: 15, 8: 15, 9: 15, 10: 8}
# Default foreground attribute per graphics mode (manual SCREENS, Table 4,
# "Default foreground attribute" column): the whitest attribute of each
# mode's attribute set.  The "Default foreground color" column is the
# displayed palette entry; for modes 1, 2 and 9 it lies outside the
# mode's legal color range (Table 2), so the attribute column is the
# program-level current color.  Mode 0 (text) is handled separately.
DEFAULT_GFX_FG = {1: 3, 2: 1, 7: 15, 8: 15, 9: 3, 10: 3}
# Custom-size screen mode used by the SCREENSIZE instruction.  Any mode in the
# 64..127 range requests a user-chosen pixel size (see Screen.set_mode) instead
# of a fixed hardware mode; SCREENSIZE uses this mode with the size given by
# its x, y arguments.  Custom-size modes use the full 16-color palette.
CUSTOM_SCREEN_MODE = 64


class Screen:
    def __init__(self, virtual=True, echo=True, gui_allowed=True):
        self.virtual = virtual
        self.echo = echo  # mirror text output to stdout (for headless/testing)
        # gui_allowed=False (--nogui) keeps the screen permanently headless:
        # graphics SCREEN commands still work on the pixel buffer, but no
        # tkinter window is ever created (see set_mode / _ensure_gui).
        self._gui_allowed = gui_allowed
        # gui_enabled is set to True as soon as a program executes a graphics
        # SCREEN command, even before the tkinter window is built.  The window
        # itself is created lazily on the first render (see _ensure_gui), so no
        # window exists until the program actually draws something.
        self.gui_enabled = not virtual
        self.mode = 0
        self.rows = 25
        self.cols = 40
        # Text cell size in pixels (TEXTSIZE).  The monitor text page is a
        # grid of square cells.  Every cell size is rendered from the real
        # anti-aliased font (see _glyph_mask); the fixed 8x8 bitmap is only
        # a last-resort fallback when no font could be loaded.  A program
        # starts with TEXTSIZE_DEFAULT - every RUN resets to it (see
        # reset_state).  It scales the whole text page: _gfx_text_page
        # (cells per row/col), the blit origin (cell * cursor), and the text
        # scroll shift all read it.
        self.cell = TEXTSIZE_DEFAULT
        # TEXTFONT: (face key, bold, italic) - the monitor's text face
        # (see textfont).  Every RUN resets it to TEXTFONT_DEFAULT.
        self.text_font = TEXTFONT_DEFAULT
        # Text rotation in degrees (TEXTRotate, 0-359): each LINE of text
        # is rotated CLOCKWISE as a rigid whole about its pivot - the
        # cursor's position at the line's start - with every glyph turned
        # by the same angle (0 = upright).  Like cell / fg / bg it is
        # monitor state: it persists across CLS, SCREEN and RUN, and
        # affects only lines drawn while it is set (see _print_rot_char).
        self.text_rotate = 0
        # Anchor of the rotated line currently being printed (TEXTRotate
        # != 0): (pivot_x, pivot_y, angle, chars_printed) in pixel units;
        # None while no rotated line is in progress (see _print_rot_char).
        self._rot_pivot = None
        self.grid = []          # text: rows x cols of [char, fg, bg]
        self.pixels = None      # graphics: rows x cols of color index
        self.cursor_row = 0
        self.cursor_col = 0
        self.fg = 7
        self.bg = 0
        self.view_rect = None   # (x1, y1, x2, y2)
        self.cursor_visible = True
        self.cursor_start = 0   # LOCATE cursor start scan line (0-31)
        self.cursor_stop = 0    # LOCATE cursor stop scan line (0-31)
        self.last_x = 0         # last referenced graphics point (LINE/PSET)
        self.last_y = 0
        self.last_point = None  # last graphics point (logical coords) for DRAW
        self._draw_scale = 1.0  # DRAW scale factor (S: n/4; default S4 -> 1)
        self._draw_color = self.fg  # DRAW current color (C sets it)
        self._draw_angle = 0    # DRAW angle (A: 0-3)
        self._draw_turn = 0.0   # DRAW turn angle in degrees (TA)
        self._interp = None     # back-reference used by DRAW substring execution
        self.view_screen = False  # VIEW SCREEN flag: True=absolute, False=relative
        self.window_rect = None  # WINDOW world-coordinate space (x1,y1,x2,y2)
        self.window_screen = False  # WINDOW SCREEN flag: True=not inverted
        self._window_origin = None  # WINDOW: (px,py) drawing-area pixel of
        # world (0,0); pending one-shot placement so that point sits at the
        # monitor center.  Consumed (set to None) as soon as the single
        # geometry() call has been issued (window() or _init_gui at creation).
        self.locate_pos = (1, 1)  # last LOCATE position (row, col), 1-based:
        # the next SCREENSIZE places the OS window's top-left corner there
        # (default: the top-left corner, the initial cursor position).
        self._window_topleft = None  # SCREENSIZE: pending one-shot (x, y)
        # desktop position for the OS window's top-left corner.  Consumed
        # (set to None) as soon as the single geometry() call has been
        # issued (screensize handler or _init_gui at creation).
        self._interrupt = False  # Ctrl+C arrived while Tcl was dispatching
        # a window event (the console had focus, so the KeyboardInterrupt
        # landed inside a tkinter callback).  It is swallowed there and
        # re-raised at the next clean Python boundary (pump() / the run
        # loop) so the program stops like a normal console Ctrl+C instead
        # of printing "Exception in Tkinter callback".
        self.apage = 0          # SCREEN alternate page
        self.vpage = 0          # SCREEN visible page
        self.border = None      # COLOR border color (SCREEN 0)
        self._ink = list(range(16))
        self._root = None
        self._canvas = None
        self._dirty = False
        # Clicks queued by the window's <ButtonPress> binding, drained one
        # per MOUSE statement (see _on_window_mouse / pop_mouse_event).
        self._mouse_events = []
        # Stop requested while the tkinter window had the keyboard focus.
        # The window does NOT handle Ctrl+C (it is ignored, so it cannot
        # corrupt the console input state).  ESC (or the window's close box)
        # sets this flag instead; the run loop / SLEEP / SETFPS poll it and
        # raise KeyboardInterrupt so the program stops (see _run_loop,
        # _sleep_seconds, _pace_fps).
        self._stop_requested = False
        # Set together with _stop_requested when the user closes the window
        # (ESC / close box) while a program is running: run()/cont() handle
        # the stop and close the window there, exactly like they do for a
        # console Ctrl+C (both routes end in the same except block, see
        # BasicREPL.run).  Cleared by close() and reset_state().
        self._close_requested = False
        # Set when the user closes the window (ESC / close box) while no
        # program is running (the window was left open by a finished
        # program): the REPL's prompt loop pumps the window between keys
        # and pump() performs the destroy there - never from inside the
        # window's own event callback, which would run in the middle of
        # Tcl's event dispatch (see pump, _on_escape).
        self._close_pending = False
        # Incremental graphics blit state (see _render_gfx):
        #   _dirty_pts  - set of points physically drawn since the last blit,
        #                 encoded as ints (y*cols+x) - decoded in _render_gfx
        #   _dirty_full - True when the whole buffer changed (CLS / SCREEN /
        #                 window (re)creation); forces a full-frame blit
        #   _snap       - last buffer that was blitted to the PhotoImage; a
        #                 size mismatch means the window changed and the
        #                 image must be rebuilt
        #   _img        - the persistent opaque PhotoImage (black base), pinned
        #                 to the canvas at the current size and mutated in place
        self._dirty_pts = set()
        self._dirty_full = False
        self._snap = None
        self._img = None
        self._img_item = None
        self._text_img = None  # PhotoImage shown by the text-mode window
        # One-shot focus flag (see _maybe_focus_window).  True once the freshly
        # opened window has been given the keyboard focus, so the user does not
        # have to click it.  Reset in close() so a re-created window re-focuses.
        self._focused = False
        # Real-font text rendering (see _glyph_mask).  A PIL ImageFont, if
        # available, is used to draw the text-page glyphs as smooth
        # anti-aliased shapes at EVERY cell size (the user wants the real
        # font at every TEXTSIZE, not the 8x8 bitmap).  _use_font gates the
        # font path: when False (PIL absent, or no font could be loaded)
        # _blit_glyph falls back to FONT_8X8 so the monitor still
        # renders text.
        self._use_font = False
        self._font = None      # PIL ImageFont, or None for the bitmap path
        self._font_cache = {}  # key -> PIL ImageFont (see _ensure_font/_cell_font)
        self._mask_cache = {}  # (cell, ordinal) -> [cell]x[cell] 0/1 ink masks
        # Pre-threshold font coverage (0-255 per pixel, cell*cell bytes),
        # keyed like _mask_cache.  The window DISPLAY re-composites the text
        # page with this coverage so its text is smoothly anti-aliased like
        # OS/console text; the pixel buffer keeps only the crisp 2-color mask
        # (the capture model for GET and headless runs).
        self._cov_cache = {}
        # Graphics text page records: (x0, y0, cell, ch, fg, bg) in buffer
        # pixel coordinates, in draw order.  They let the window display
        # re-composite the last-written text anti-aliased (see
        # _display_body); the pixel buffer itself is untouched.
        self._gfx_text = []
        # Probe for a usable font up front so the first draw already knows
        # which path to take (no-op when PIL is absent -> the FONT_8X8
        # bitmap path is used instead).
        self._ensure_font()
        # SCREENSIZE FULLSCREEN: when True, open the window maximized to fill
        # the screen (see _init_gui / _render_gfx).  The drawing surface then
        # tracks the live window size via the <Configure> handler, so XSZ()/
        # YSZ() report the real screen dimensions.
        self._fullscreen = False
        # SETFPS pacing state (see set_fps / _pace_fps).  _fps_target is the
        # frame-rate cap in fps; the default is UNLIMITED (None, no pacing).
        # _fps_base/_fps_count track the current paced burst (see _pace_fps):
        # the start time and how many blits have run since it, so the cap acts
        # as a ceiling that only throttles a program running faster than it.
        self._fps_target = None
        self._fps_base = None
        self._fps_count = 0
        # Paint-coalescing flag (see render / _run_loop).  When True the next
        # render() forces the window to actually paint (cv.update()); when
        # False it only updates the canvas item cheaply and skips the paint,
        # so a frame made of many lines blits once, at the end of the loop,
        # instead of forcing a Tk event-loop cycle on every single line.
        self._paint_due = False
        # Timestamp of the last throttled window pump (see pump_if_due):
        # the run loop drains the window's Tk queue at most ~50 times per
        # second so a non-drawing program still sees the window's ESC.
        self._last_pump_t = 0.0
        self._init_grid()
        # The tkinter window is created lazily (in _ensure_gui) when the
        # program first renders graphics, never at construction.  This keeps
        # a window from appearing until a graphics SCREEN command runs.

    def _ensure_gui(self):
        """Create the tkinter window on first use (lazy).  A screen that has
        been enabled for graphics (gui_enabled) but has not yet built its
        window gets one here, so the first graphics render shows up.  If
        tkinter is unavailable the screen silently stays virtual."""
        if self.gui_enabled and self._root is None:
            self._init_gui()
            self.virtual = self._root is None

    # -- setup --------------------------------------------------------------- #
    def _init_grid(self):
        self.grid = [[[' ', self.fg, self.bg] for _ in range(self.cols)]
                     for _ in range(self.rows)]

    def _init_gui(self):
        try:
            import tkinter as tk
        except Exception:
            self.virtual = True
            return
        self._root = tk.Tk()
        self._root.title("GW-BASIC")
        # Black background on the window and the canvas.  The graphics
        # surface is a fixed size, but the OS window can be resized; when it
        # is made larger the exposed margin is black (matching the screen's
        # default background) instead of a jarring white border.
        self._root.configure(bg="black")
        self._canvas = tk.Canvas(self._root, highlightthickness=0,
                                 bg="black")
        self._canvas.pack()
        # Track live window resizes so the drawing surface follows the window
        # (see _on_configure).  Only size changes matter; the handler ignores
        # plain window moves and text mode.
        self._root.bind("<Configure>", self._on_configure)
        # While the graphics window has the keyboard focus, Ctrl+C is
        # deliberately IGNORED.  Handling Ctrl+C here (and tearing the window
        # down from the key handler) corrupts the console input state, which
        # made a second Ctrl+C at the Ok prompt replay the previous line and
        # exit the interpreter.  ESC is the supported way to dismiss the window:
        # it sets the stop flag so the program stops, the window closes, and
        # control returns to the Ok prompt (see _on_escape).
        self._root.bind("<Escape>", self._on_escape)
        self._root.protocol("WM_DELETE_WINDOW", self._on_escape)
        # The window is the monitor's keyboard: while it has the focus, its
        # keys are translated into the same key events the console pump
        # produces and handed to the system queue, so INKEY$, GET, INPUT and
        # ON KEY(n) traps read them without knowing the window exists (see
        # _on_window_key).  <Control-c> stops a running program the same way
        # a console Ctrl+C does (see _on_window_ctrl_c).  Both are bound
        # BEFORE the plain <Key> binding: a handler that returns "break"
        # suppresses the later bindings for that event.
        self._root.bind("<Control-c>", self._on_window_ctrl_c)
        self._root.bind("<Key>", self._on_window_key)
        # Mouse clicks on the drawing area are queued for the MOUSE
        # statement (see _on_window_mouse / pop_mouse_event).
        self._canvas.bind("<ButtonPress>", self._on_window_mouse)
        # SCREENSIZE FULLSCREEN: open the window maximized so it fills the
        # screen.  The real pixel size is read back after the window maps;
        # the <Configure> handler (bound above) then resizes the drawing
        # surface to the live window, so XSZ()/YSZ() report the screen size.
        # winfo_screenwidth/height are available as soon as Tk() exists, even
        # before the window is mapped.
        if self._fullscreen:
            try:
                self._root.update_idletasks()
                sw = self._root.winfo_screenwidth()
                sh = self._root.winfo_screenheight()
                if sw > 1 and sh > 1:
                    self._root.geometry("%dx%d+0+0" % (sw, sh))
                self._root.update_idletasks()
                self._root.wm_state("zoomed")  # maximize: fill the work area
                self._root.update_idletasks()
            except Exception:
                pass  # non-maximizable display: fall back to a normal window
        # WINDOW (x1,y1)-(x2,y2): place the fresh window so world (0,0) sits
        # at the monitor center - a single geometry() call, done here once
        # the window exists (see _place_window_at_origin).
        if self._window_origin is not None:
            self._place_window_at_origin()
        # SCREENSIZE: place the fresh window's top-left corner at the
        # position the last LOCATE set - a single geometry() call, done
        # here once the window exists (see the screensize handler).
        if self._window_topleft is not None:
            try:
                x, y = self._window_topleft
                self._root.geometry("+%d+%d" % (x, y))
            except Exception:
                pass
            finally:
                self._window_topleft = None
        # The window IS the monitor the moment it opens, so it must take the
        # keyboard focus itself - the user should not have to click it.  The
        # focus is taken once, the first time the window actually paints (see
        # render / _maybe_focus_window): a Win32 SetForegroundWindow on a
        # window that has not yet been mapped by Tk does nothing, so it
        # cannot be done here at creation.

    def _maybe_focus_window(self):
        """Give the graphics window the keyboard focus the first time it
        paints, so the user does not have to click it.  Runs at most once per
        window (see self._focused): the window must be mapped by Tk first
        (render() has just painted it) or a focus/foreground call does nothing,
        and repeating it would steal focus back from the console on every
        repaint.

        On Windows a bare SetForegroundWindow is unreliable when the console
        already owns the foreground lock.  So this simulates a real mouse
        CLICK on the window: it posts a left-button mouse-down (and up) at the
        window's centre into the window's own input queue.  A posted
        WM_LBUTTONDOWN is processed by the window itself and, as a side
        effect, the window takes the foreground/keyboard focus - exactly what a
        user's click does, but with no z-order thrash and no repaint (so no
        flicker).  A brief ALT tap also releases the OS foreground lock first
        so the window is allowed to take focus."""
        if self._focused or self._root is None:
            return
        self._focused = True  # one-shot: never re-grab on later repaints

        def _hwnd():
            # wm_frame() returns a Tk window id (a hex string like 0x...); the
            # real HWND is its parent (the frame window Tk wraps the toplevel
            # in).
            try:
                frame = int(str(self._root.wm_frame()), 0)
            except (TypeError, ValueError):
                return 0
            u = ctypes.windll.user32
            return u.GetParent(frame) or frame

        def _do():
            """Bring the window forward and give it the keyboard focus, the way
            a click would.  Deferred (via after()) so the window is fully
            mapped by Tk before we touch the foreground.

            On Windows a bare SetForegroundWindow is blocked while the console
            owns the foreground lock.  The reliable way to get past that is
            the documented foreground-permission trick: temporarily attach this
            thread's input to the current foreground thread (which grants this
            thread foreground permission), then ShowWindow + BringWindowToTop +
            SetForegroundWindow, and detach again.  This makes the window the
            foreground (focused) window with no z-order thrash and no repaint
            (so no flicker).  Tk's lift/focus_force are tried first as a cheap
            path; the Win32 sequence is the one that actually sticks."""
            try:
                self._root.lift()
            except Exception:
                pass
            if os.name != 'nt':
                try:
                    self._root.focus_force()
                except Exception:
                    pass
                return
            try:
                import ctypes
                u = ctypes.windll.user32
                k = ctypes.windll.kernel32
                hwnd = _hwnd()
                if not hwnd:
                    return
                fg = u.GetForegroundWindow()
                fg_tid = u.GetWindowThreadProcessId(fg, 0) if fg else 0
                cur_tid = k.GetCurrentThreadId()
                attached = False
                # Attach to the current foreground thread to gain the right to
                # set the foreground window (the documented workaround).
                if fg_tid and fg_tid != cur_tid:
                    if u.AttachThreadInput(cur_tid, fg_tid, True):
                        attached = True
                try:
                    u.ShowWindow(hwnd, 9)  # SW_RESTORE (un-minimize)
                    u.BringWindowToTop(hwnd)
                    u.SetForegroundWindow(hwnd)
                    # Belt and braces: also ask Tk for the keyboard focus so the
                    # window's <Key> bindings receive the input.
                    self._root.focus_force()
                finally:
                    if attached:
                        u.AttachThreadInput(cur_tid, fg_tid, False)
            except Exception:
                # Last resort: ask Tk to force the focus.
                try:
                    self._root.focus_force()
                except Exception:
                    pass
        try:
            # Defer ~150ms so Tk has finished mapping the window; a focus or
            # click on an unmapped window is a no-op.
            self._root.after(150, _do)
        except Exception:
            _do()

    def _on_escape(self, event=None):
        # ESC pressed while the window is focused (or the window's close box
        # clicked).  ESC always closes the window; how it happens depends on
        # whether a program is running:
        #
        # * Running: set the stop flags.  The run loop / SLEEP / SETFPS poll
        #   _stop_requested and raise KeyboardInterrupt; run()/cont() handle
        #   it by closing the window (because _close_requested is set) and
        #   printing "Break".
        #
        # * Not running (the window was left open by a finished program):
        #   mark it for closure.  The REPL's prompt loop pumps the window
        #   between keys and pump() performs the destroy there - never
        #   from inside this event callback, which would run in the middle
        #   of Tcl's event dispatch.
        interp = self._interp
        if interp is not None and getattr(interp, '_running', False):
            self._stop_requested = True
            self._close_requested = True
        else:
            self._close_pending = True
        return "break"

    def _on_window_ctrl_c(self, event=None):
        # Ctrl+C while the window has the focus.  While a program is running
        # it stops the program exactly like a console Ctrl+C: the stop flags
        # are set (the run loop polls _stop_requested every line; run()/
        # cont() close the window and print "Break"), and "break" keeps the
        # plain <Key> binding from also delivering the character.  While no
        # program is running (Ok prompt / LEDIT) the key is delivered to the
        # key queue so the prompt's own Ctrl+C handling runs (a fresh prompt,
        # not an exit).
        interp = self._interp
        if interp is not None and getattr(interp, '_running', False):
            self._stop_requested = True
            self._close_requested = True
            return "break"
        return None

    # Scan codes (set 1) for the keys the KEY(n) definitions trap on.  Tk
    # does not expose the hardware scan code, so it is derived from the key:
    # special keys by keysym name, the rest by the character they produce on
    # a US layout.  These make window keys match KEY(n),CHR$(hex)+CHR$(scan)
    # definitions (manual KEY), e.g. KEY 16, CHR$(0)+CHR$(&H39) for SPACE.
    _KEYSYM_SCAN = {
        'Return': 0x1C, 'Tab': 0x0F, 'Escape': 0x01, 'BackSpace': 0x0E,
        'Home': 0x47, 'End': 0x4F, 'Prior': 0x49, 'Next': 0x51,
        'Insert': 0x52, 'Delete': 0x53,
        'F1': 0x3B, 'F2': 0x3C, 'F3': 0x3D, 'F4': 0x3E, 'F5': 0x3F,
        'F6': 0x40, 'F7': 0x41, 'F8': 0x42, 'F9': 0x43, 'F10': 0x44,
    }
    _CHAR_SCAN = {
        ' ': 0x39, '\r': 0x1C, '\n': 0x1C, '\t': 0x0F, '\x1b': 0x01,
        '\x08': 0x0E, ';': 0x27, "'": 0x28, ',': 0x2F, '.': 0x30,
        '/': 0x31, '\\': 0x2B, '[': 0x1A, ']': 0x1B, '-': 0x0C,
        '=': 0x0D, '`': 0x29, '*': 0x37, '+': 0x4E, ':': 0x27,
    }

    @classmethod
    def _key_scan(cls, keysym, ch):
        scan = cls._KEYSYM_SCAN.get(keysym)
        if scan is not None:
            return scan
        c = ch[0] if ch else ''
        if 'a' <= c <= 'z':
            c = c.upper()
        if 'A' <= c <= 'Z':
            return 0x1E + (ord(c) - ord('A'))
        if c == '0':
            return 0x0B
        if '1' <= c <= '9':
            return 0x02 + (ord(c) - ord('1'))
        return cls._CHAR_SCAN.get(c)

    def _on_window_key(self, event):
        # A key typed while the window has the focus: translate the Tk
        # event into a key event of the same shape the console pump
        # produces ({'ch','token','scan','mask'}, see
        # System.pump_key_events) and hand it to the system queue.  INKEY$,
        # GET, INPUT and ON KEY(n) traps consume that queue, so the program
        # reads window keys exactly like console keys.  ESC is the window's
        # own close key (see _on_escape) and is not delivered.
        if self._interp is None:
            return
        system = self._interp.system
        k = event.keysym
        ch = event.char or ''
        if k == 'Escape':
            return "break"
        # Modifier mask in the manual KEY(n) bit layout: &H01 right SHIFT,
        # &H02 left SHIFT, &H04 CTRL, &H08 ALT, &H20 NUM LOCK, &H40 CAPS
        # LOCK, &H80 extended (see System._modifier_mask).  Tk reports the
        # left and right shift keys the same, so &H02 stands for both.
        mask = 0
        state = event.state
        if state & 0x0001:  # Shift
            mask |= 0x02
        if state & 0x0008:  # Control
            mask |= 0x04
        if state & 0x0010:  # Mod1 (Alt)
            mask |= 0x08
        if state & 0x0020:  # Mod2 (NUM LOCK)
            mask |= 0x20
        if state & 0x0080:  # Mod4 (CAPS LOCK)
            mask |= 0x40
        if k in ('Up', 'Down', 'Left', 'Right'):
            # Arrow keys: token + scan code + &H80 extended, exactly like
            # the console's extended keys (ON KEY(11)-(14) traps and the
            # INKEY$ CHR$(0)+CHR$(scan) checks depend on this).
            token = {'Up': 'up', 'Down': 'down', 'Left': 'left',
                     'Right': 'right'}[k]
            scan = {'Up': 72, 'Down': 80, 'Left': 75, 'Right': 77}[k]
            system.push_key('', token=token, scan=scan, mask=mask | 0x80)
            return
        if k == 'Return':
            # Carry a real newline (not the console's carriage return): the
            # text output path treats only '\n' as a line break, so a window
            # Enter must advance the cursor to a fresh line exactly like a
            # console Enter does.  INPUT still sees the 'enter' token.
            system.push_key('\n', token='enter', scan=0x1C)
            return
        if k == 'BackSpace':
            system.push_key('\x08', scan=0x0E)
            return
        if k == 'Tab':
            system.push_key('\t', scan=0x0F)
            return
        if k == 'Delete':
            system.push_key('\x7f', scan=0x53)
            return
        if k in ('Home', 'End', 'Prior', 'Next', 'Insert'):
            system.push_key('', scan=self._KEYSYM_SCAN[k])
            return
        if len(k) > 1 and k[0] == 'F' and k[1:].isdigit():
            # F-keys: scan codes 59-68 (manual ON KEY), no character.
            system.push_key('', scan=self._KEYSYM_SCAN.get(k))
            return
        if ch:
            system.push_key(ch, scan=self._key_scan(k, ch), mask=mask)
            return

    def _on_window_mouse(self, event):
        # A mouse button press on the drawing area: queue the click in
        # canvas (drawing-area pixel) coordinates.  The MOUSE statement
        # drains this queue and converts to world coordinates at read time
        # (see _phys_to_world).
        self._mouse_events.append((event.x, event.y, event.num))

    def pop_mouse_event(self):
        """Pop the oldest queued click (x, y, button), or None.

        x and y are drawing-area (canvas) pixel coordinates; button is the
        Tk button number (1 left, 2 middle, 3 right)."""
        if not self._mouse_events:
            return None
        return self._mouse_events.pop(0)

    def pump_events(self):
        """Process pending window events, no side effects.

        Used by the key pump (System.pump_key_events) so that keys typed
        while the window has the focus reach the key queue even when a tight
        INKEY$ loop is running and nothing else pumps the window.  Unlike
        pump(), this never raises and never destroys the window; it simply
        drains the Tk event queue (which runs the <Key> adapter)."""
        if self._root is None or self.virtual:
            return
        try:
            if not self._root.winfo_exists():
                return
            self._root.update()
        except KeyboardInterrupt:
            # A console Ctrl+C landed inside a Tk event: remember it for
            # the next clean boundary, exactly like _on_configure does.
            self._interrupt = True
        except Exception:
            pass

    def pump_if_due(self, interval=0.02):
        """Drain the window's event queue at most once per `interval` seconds.

        Called from the run loop between lines: a program that draws nothing
        (a tight GOTO loop, a long computation) never pumps the window on its
        own, so the window's <Escape> / close-box events would sit in the Tk
        queue unprocessed - the ESC handler (see _on_escape) would never run,
        the stop flag would never be set, and the window would appear
        uncloseable.  Throttled so a fast loop pays at most ~50 Tk updates
        per second.  No-op with no window; never raises (see pump_events)."""
        if self._root is None or self.virtual:
            return
        now = time.time()
        if now - self._last_pump_t < interval:
            return
        self._last_pump_t = now
        self.pump_events()

    def close(self):
        """Destroy the tkinter graphics window (if any) and drop the GUI
        state.  Called when a program is stopped (console Ctrl+C or window
        ESC / close box), on NEW, or on BYE - always at a clean Python
        boundary, never from inside the window's own event callback.  The
        screen stays graphics-enabled, so the next graphics render rebuilds
        the window on demand.  Closing the window always stops any music
        currently playing (the user can close the window to quiet the
        room), whether or not a program is running."""
        interp = self._interp
        if interp is not None and getattr(interp, 'system', None) is not None:
            interp.system.music_stop()
        root = self._root
        self._root = None
        self._canvas = None
        self._img = None
        self._img_item = None
        self._text_img = None
        self._dirty = False
        self._dirty_pts = set()
        self._dirty_full = False
        self._snap = None
        self._stop_requested = False
        self._close_requested = False
        self._close_pending = False
        self._paint_due = False
        self._window_origin = None
        self._interrupt = False
        self._focused = False
        if root is not None:
            try:
                root.destroy()
            except Exception:
                pass

    def wclose(self):
        """WCLOSE: destroy the graphics window (like the window's own ESC /
        Ctrl+C) and drop back to the console for I/O.  The program keeps
        running in its current screen mode; gui_enabled is cleared so the
        close is not undone by the very next render - a later SCREEN /
        SCREENSIZE / WINDOW re-opens the window on demand."""
        self.close()
        self.gui_enabled = False

    def textsize(self, size=None):
        """TEXTSIZE x: set the size, in pixels, of a text character cell on
        the monitor (the window).  The text is drawn from the real
        anti-aliased font (the current TEXTFONT face) fitted to the cell, so
        a larger x gives bigger, smoother text.  x must be a positive
        integer (>= 1); None (a bare TEXTSIZE) or a value below 1 resets to
        the default cell size (TEXTSIZE_DEFAULT, 11 - the size a program
        starts with).  Changing it re-lays-out the text page and repaints,
        so the new size shows at once.  It does not change the window's
        pixel size - only how large the characters drawn on the text page
        are."""
        if size is None:
            n = TEXTSIZE_DEFAULT
        else:
            n = int(size)
            if n < 1:
                n = TEXTSIZE_DEFAULT
        if n == self.cell:
            # Unchanged cell size: nothing to re-lay-out or repaint.  Programs
            # (e.g. Monopoly) re-issue TEXTSIZE on every line of an animation
            # with the same value; the old code forced a full-frame rebuild and
            # an immediate repaint on each one, which froze the window.
            self._ensure_font()
            self._rot_pivot = None  # a new cell size starts a new line
            return
        self.cell = n
        # Make sure a usable font is known (a no-op when PIL is absent or
        # one was already loaded).  Per-cell font instances are created and
        # cached lazily by _cell_font.
        self._ensure_font()
        self._rot_pivot = None  # a new cell size starts a new line
        self._dirty = True
        self._dirty_full = True
        self._dirty_pts = set()
        if self.pixels is not None:
            self._gfx_dirty()
        # Repaint now so the new size is visible immediately (a TEXTSIZE
        # typed at the Ok prompt has no later render to batch with).
        self.paint_now()

    def textrotate(self, degrees=None):
        """TEXTRotate x: rotate the lines of text drawn from now on by x
        degrees (an integer 0-359) CLOCKWISE, each line as a rigid whole
        around its pivot - the text cursor's position at the start of the
        line - on the monitor (the window).  A bare TEXTRotate (no argument
        / None) resets to upright (0); a value outside 0-359 is an
        "Illegal function call".

        The rotation is persistent monitor state, like TEXTSIZE and COLOR:
        it applies to every line PRINT / INPUT draws until another
        TEXTRotate changes it, and it persists across CLS and SCREEN.
        Every RUN resets it to upright (0), along with TEXTSIZE and
        TEXTFONT (see reset_state).
        A rotated line is the upright line rotated about its pivot: the
        glyphs advance along a baseline turned by x degrees from
        horizontal, each glyph itself turned by x degrees about its own
        cell centre, so the whole line spins as one object (see
        _print_rot_char).  The character grid underneath is untouched -
        the cursor still sits on the grid, LOCATE still addresses grid
        rows and columns, and after the line's newline the cursor is at
        the start of the next grid row exactly as for an upright line.
        The line is composited into the pixel buffer as well as the window
        display, so GET captures the rotated text exactly as the
        monitor shows it.  Lines already on the surface keep the angle
        they were printed with (the monitor model), and setting the angle
        repaints nothing: the new angle applies from the next line, so no
        repaint is needed (and forcing one would flash the window).
        """
        if degrees is None:
            n = 0
        else:
            n = int(degrees)
            if not 0 <= n <= 359:
                raise BasicError("Illegal function call")
        self.text_rotate = n
        # Pure state change: nothing on the surface changes (existing lines
        # keep the angle they were printed with), so there is no repaint;
        # the new angle applies from the next line's first character.

    def textfont(self, name=None, bold=None, italic=None):
        """TEXTFONT [font][, [bold][, [italic]]]: choose the face the monitor
        text is drawn in.  font is one of the TEXTFONT_FACES names (Arial,
        Segoe, Courier, Georgia, Tahoma, Calibri, NewTimes, Verdana,
        Trebuchet, Canada, Impact), matched case-insensitively.  The bold
        flag is B/BOLD (bold) or NB/NONBOLD (regular); the italic flag is
        I/ITALIC/ITALICS (italic) or NI/NONITALIC/NOTITALIC (upright).
        Each omitted argument (None) takes its default - font defaults to
        Arial, weight to not bold, not italic - so a bare TEXTFONT restores
        the default face (Arial regular).

        The setting is persistent monitor state like TEXTSIZE and COLOR: it
        applies to text drawn from now on (lines already on the surface
        keep the face they were printed with - the monitor model), it
        persists across CLS and SCREEN, and every RUN resets it to the
        default (see reset_state).  Changing the face drops every cached
        font and glyph so all new text renders from the new face, and
        repaints at once.  An unknown face or unrecognised weight flag is
        an "Illegal function call"."""
        # Omitted arguments take their per-slot defaults (Arial, not bold,
        # not italic) - NOT the current values - so TEXTFONT ,,I is always
        # Arial regular italic and a bare TEXTFONT restores the default
        # face, exactly as the examples in the help entry specify.
        face, b, i = TEXTFONT_DEFAULT
        if name is not None:
            key = str(name).strip().upper()
            if key not in TEXTFONT_FACES:
                raise BasicError("Illegal function call")
            face = key
        if bold is not None:
            w = str(bold).strip().upper()
            if w in ('B', 'BOLD'):
                b = True
            elif w in ('NB', 'NONBOLD'):
                b = False
            else:
                raise BasicError("Illegal function call")
        if italic is not None:
            w = str(italic).strip().upper()
            if w in ('I', 'ITALIC', 'ITALICS'):
                i = True
            elif w in ('NI', 'NONITALIC', 'NONITALICS', 'NOTITALIC'):
                i = False
            else:
                raise BasicError("Illegal function call")
        if (face, b, i) == self.text_font:
            return  # no change: nothing to re-render or repaint
        self.text_font = (face, b, i)
        # The face changed: drop every font and glyph derived from the old
        # one so all text re-renders from the new face.  (The caches are
        # keyed by (cell, char, angle) without the face, so a stale mask
        # would be the wrong font.)  Surface text keeps what it shows -
        # the monitor model - until new text is drawn.
        self._font = None
        self._use_font = False
        self._font_cache = {}
        self._mask_cache.clear()
        self._cov_cache.clear()
        self._ensure_font()
        self._rot_pivot = None  # a new face starts a new line
        self._dirty = True
        self._dirty_full = True
        self._dirty_pts = set()
        if self.pixels is not None:
            self._gfx_dirty()
        self.paint_now()

    def _resize_buf(self, w, h):
        """Resize the graphics drawing surface to the window size.

        The user can drag the OS window bigger or smaller at any time; the
        drawing surface (self.pixels) follows it so the whole window is an
        active, drawable area.  The existing content is preserved in the top-
        left; the newly exposed area (when growing) is the background color
        (0 = black), and the excess is cropped (when shrinking).  A full-frame
        blit is forced on the next render because the buffer and the on-screen
        image changed wholesale.  Returns True if anything changed."""
        w = max(1, int(w))
        h = max(1, int(h))
        if w == self.cols and h == self.rows:
            return False
        old = self.pixels if isinstance(self.pixels, list) else None
        new = [[0] * w for _ in range(h)]
        if old is not None:
            ow, oh = len(old[0]), len(old)
            for y in range(min(h, oh)):
                for x in range(min(w, ow)):
                    new[y][x] = old[y][x]
        self.pixels = new
        self._gfx_text = []  # coordinates changed wholesale: the display
                             # falls back to the (2-color) buffer until the
                             # program re-PRINTs
        self.cols = w
        self.rows = h
        self.view_rect = None
        self._dirty_full = True
        self._dirty_pts = set()
        self._dirty = True
        return True

    def _on_configure(self, event):
        # Fires whenever the window is resized (dragging a border) or moved.
        # For a graphics screen we resize the drawing surface to the window's
        # content size, so the whole window is drawable and XSZ()/YSZ() report
        # the new size.
        #
        # <Configure> fires more than once per resize: once for the new window
        # size and again for the canvas's (now stale) requested size.  To
        # avoid reacting to the stale size we (a) reconfigure the canvas to the
        # window content size on every event, and (b) only accept a size the
        # canvas actually reports via winfo_width/height.  Once the canvas is
        # set to that size it reports it reliably, and the stale old-size event
        # (which the canvas no longer matches) is ignored as a no-op.  The
        # actual blit is deferred to the next render (driven by the program's
        # animation loop via flush()), so this stays cheap and never re-enters
        # the run loop from inside a Tcl event handler.
        try:
            if self.is_text():
                return
            w = int(event.width)
            h = int(event.height)
            if w < 1 or h < 1:
                return
            # Keep the canvas sized to the window content so the drawing fills
            # it and so winfo_width/height below report the window size.
            self._canvas.config(width=w, height=h)
            self._root.update_idletasks()
            cw = self._canvas.winfo_width()
            ch = self._canvas.winfo_height()
            if cw < 1 or ch < 1 or (cw, ch) != (w, h):
                # The canvas did not actually take the new size (e.g. the
                # stale re-layout event); ignore it.
                return
            if cw == self.cols and ch == self.rows:
                return
            self._resize_buf(cw, ch)
        except KeyboardInterrupt:
            # Ctrl+C (console focused) raised inside this Tcl callback.
            # Letting it propagate prints "Exception in Tkinter callback"
            # and unwinds Tcl's event dispatch; swallow it here and re-raise
            # at the next clean Python boundary (pump() / the run loop),
            # exactly like a console Ctrl+C would be.
            self._interrupt = True
            return "break"
        except Exception:
            # Window mid-teardown: ignore; close()/the next render recover.
            pass

    def set_mode(self, mode, size=None, fullscreen=False):
        self.apage = 0  # new surface: reset the SCREEN apage argument value
        self._gfx_text = []  # new surface: no window-display text records
        self._rot_pivot = None  # new surface: no rotated line in progress
        # Manual SCREENS: legal values are 0, 1, 2, 7, 8, 9, 10; all other
        # values are illegal.  Mode 0 is the only text mode; mode 7 is
        # 320x200 EGA graphics (NOT text).
        #
        # Extension (custom window size): a mode in the 64..127 range is NOT
        # a real GW-BASIC screen mode -- it is a placeholder that requests a
        # user-chosen pixel size.  Pass size=(width, height) to set_mode to
        # pick the actual dimensions (default 1200x1200 when omitted).  This
        # is how you get a 1200x1200 window: e.g. `SCREEN 65` then set the
        # size, or use a convenience mode.  All drawing code works unchanged
        # because the buffer is sized to the custom dimensions.
        mode = int(mode)
        self._fullscreen = bool(fullscreen)
        if mode not in LEGAL_SCREEN_MODES and 64 <= mode <= 127:
            # Custom-size mode: the exact pixels come from `size`.
            if size is None:
                # Fullscreen (or size omitted): the real pixel size is the
                # screen size, learned when the window is created (see
                # _init_gui).  Hold a small placeholder buffer so XSZ()/YSZ()
                # return a safe value before the first render; the drawing
                # surface is resized to the live window on the first blit.
                if self._fullscreen:
                    w, h = 1, 1
                else:
                    w, h = 1200, 1200
            else:
                w, h = int(size[0]), int(size[1])
                if w < 1 or h < 1 or w > 4096 or h > 4096:
                    raise BasicError("Illegal function call")
            self._custom_size = (w, h)
        elif mode not in LEGAL_SCREEN_MODES:
            raise BasicError("Illegal function call")
        self.mode = mode
        if mode in TEXT_MODES:
            self.rows = 25
            self.cols = 40
            self.pixels = None
            self._init_grid()
            self.fg = 7
            self.bg = 0
            # Back to text mode: a graphics program no longer wants the window.
            self.gui_enabled = False
        else:
            if mode in GFX_DIMS:
                self.rows, self.cols = GFX_DIMS[mode]
            else:
                # Custom-size mode: use the requested pixel dimensions.
                w, h = getattr(self, '_custom_size', (320, 200))
                self.rows, self.cols = h, w
            self.pixels = [[0] * self.cols for _ in range(self.rows)]
            self.grid = None
            # The whole graphics buffer was replaced: the next blit must
            # cover the full frame, not just the (old) tracked dirty points.
            self._dirty_full = True
            # Default foreground attribute per mode (manual SCREENS,
            # Table 4, "Default foreground attribute" column).  Custom-size
            # modes (absent from the table) keep the documented default 7.
            self.fg = DEFAULT_GFX_FG.get(mode, 7)
            # A graphics SCREEN command has run: the window will be created
            # lazily on the first render (see _ensure_gui / render).  In
            # --nogui mode (gui_allowed=False) the screen stays headless:
            # the pixel buffer is updated, but no window is created.
            self.gui_enabled = self._gui_allowed
            # Mark the surface dirty so the end-of-line flush() renders and
            # paints the new mode right away (opening the window) instead of
            # waiting for the next drawing statement - the window must appear
            # as soon as SCREEN / SCREENSIZE / WINDOW itself runs.
            self._gfx_dirty()
        self.cursor_row = 0
        self.cursor_col = 0
        self.view_rect = None
        self.view_screen = False
        self.window_rect = None
        self.window_screen = False
        self._window_origin = None
        self.last_point = None
        self._draw_scale = 1.0
        self._draw_color = self.fg
        self._draw_angle = 0
        self._draw_turn = 0.0
        if not self.virtual and self._canvas is not None:
            self.render()

    def is_text(self):
        return self.mode in TEXT_MODES

    # -- window size accessors ----------------------------------------------- #
    # XSZ()/XSIZE() and YSZ()/YSIZE() report the current drawing-surface size
    # in pixels (see Interpreter call_function).  In graphics mode the drawing
    # surface follows the OS window, so these track a live window resize; in
    # text mode they are 0 (there is no pixel surface).
    def xsize(self):
        return self.cols if self.pixels is not None else 0

    def ysize(self):
        return self.rows if self.pixels is not None else 0

    # -- text output --------------------------------------------------------- #
    def _advance(self, ch):
        if ch == '\n':
            self.cursor_col = 0
            self.cursor_row += 1
            if self.cursor_row >= self.rows:
                self._scroll()
                self.cursor_row = self.rows - 1
            return
        self.cursor_col += 1
        if self.cursor_col >= self.cols:
            self.cursor_col = 0
            self.cursor_row += 1
            if self.cursor_row >= self.rows:
                self._scroll()
                self.cursor_row = self.rows - 1

    def _scroll(self):
        del self.grid[0]
        self.grid.append([[' ', self.fg, self.bg] for _ in range(self.cols)])

    def put_char(self, ch):
        if not self.is_text():
            return
        if ch == '\n':
            self._advance('\n')
            return
        if self.cursor_row < self.rows and self.cursor_col < self.cols:
            self.grid[self.cursor_row][self.cursor_col] = [ch, self.fg, self.bg]
        self._advance(ch)

    def print_text(self, text, newline=True):
        """Write text at the cursor (used by PRINT).

        In text mode the characters go to the character grid; in graphics
        mode they go to the text page composited directly into the pixel
        buffer (the monitor model), so GET captures the text.  The
        console echo used to happen here; it now belongs to the I/O middle
        layer (IoDevice), which decides whether the window or the console
        is the active monitor."""
        if self.is_text():
            for ch in text:
                self.put_char(ch)
            if newline:
                self._advance('\n')
        else:
            for ch in text:
                self._print_gfx_char(ch)
            if newline:
                self._print_gfx_char('\n')
        if not self.virtual and self._canvas is not None:
            self.render()

    # -- text page on the graphics surface (the monitor model) ---------------- #
    # In graphics mode the pixel surface doubles as the old CGA/EGA monitor:
    # a page of 8x8-pixel character cells laid over the pixel buffer (40x25
    # on a 320x200 screen).  PRINT / LOCATE / COLOR / CLS address that page,
    # and the glyphs are composited straight into self.pixels, so GET
    # captures the text exactly like on the real monitor.
    # The WINDOW DISPLAY is a layer above that: it re-composites the text
    # page from the font's anti-aliased coverage (see _display_body), so the
    # on-screen text is smooth grayscale like console text, while the pixel
    # buffer (and hence GET) keeps the crisp 16-color monitor model.

    def _gfx_text_page(self):
        """Dimensions of the graphics text page in character cells (each
        cell is self.cell x self.cell pixels; TEXTSIZE_DEFAULT (11) by
        default)."""
        cell = self.cell
        return max(1, self.cols // cell), max(1, self.rows // cell)

    # The real (anti-aliased) font is used for EVERY cell size.  The
    # 8x8 FONT_8X8 bitmap is only a last-resort fallback for machines
    # where no font could be loaded (PIL absent / every candidate font
    # missing) - see _glyph_mask.  This cutoff therefore sits at 1: a
    # cell below it is invalid (cell <= 0 is rejected in _glyph_mask),
    # so the font path is taken whenever a font is available, and the
    # bitmap path only when it is not.
    FONT_MIN_CELL = 1

    def _glyph_font_vals(self, ch, cell):
        """Render one character from the cell-matched (anti-aliased) font
        at 4x supersample, on the SAME fixed baseline for every glyph, and
        return it LANCZOS-downsampled to a cell x cell 2D list of 0-255
        coverage (vals[cy][cx]).  Because the font size is fixed (not fit
        per letter) and the glyph is drawn centered, a cap and an x-height
        letter keep their natural relative sizes with balanced margins.
        Returns None when the PIL image ops fail (the caller then stops
        using the font, as the upright path always did)."""
        try:
            from PIL import Image, ImageDraw
            # 4x supersample for crisp edges.
            s = max(2, cell) * 4
            img = Image.new("L", (s, s), 0)
            ascent, descent = self._cell_font(cell).getmetrics()
            # Baseline: sit the cap near the top and leave room for
            # descenders (p, g, y, j) in the bottom of the cell.  Caps occupy
            # ~65% of the cell from the baseline, descenders ~20%.
            baseline = int(round(cell * 0.72)) * (s // cell)
            baseline = min(baseline, s - max(1, descent // (s // cell)))
            # Horizontally CENTER the glyph in the monospace cell:
            # anchor="ms" = middle/baseline, so the pen sits at the middle of
            # the glyph's advance width and the baseline stays at y=baseline
            # for every letter.  Each letter then gets balanced left and
            # right margins: narrow letters (i, l, .) no longer leave a big
            # trailing gap and wide letters (m, w) are no longer cramped.
            ImageDraw.Draw(img).text((s // 2, baseline), ch, fill=255,
                                     font=self._cell_font(cell),
                                     anchor="ms")
            try:
                lanc = Image.Resampling.LANCZOS
            except AttributeError:
                lanc = Image.ANTIALIAS  # older Pillow: no Resampling enum
            px = img.resize((cell, cell), lanc).load()
            return [[px[cx, cy] for cx in range(cell)] for cy in range(cell)]
        except Exception:
            return None

    def _bitmap_mask(self, ch, cell):
        """The 8x8 FONT_8X8 glyph for ch (a space when unknown) as a
        cell x cell 0/1 mask - the exact raster the upright bitmap path in
        _blit_glyph draws (cells below the font cutoff), and the base the
        no-PIL rotation path rotates.

        For cell 1-8 this is an AREA-BASED MAX-FILTER downscale: the
        destination pixel (px, py) covers the source area [px*8/cell,
        (px+1)*8/cell) x [py*8/cell, (py+1)*8/cell) and is inked when ANY
        source pixel whose unit square overlaps that area is inked.  Each
        destination pixel spans 8/cell >= 1 source pixels, so it ORs the
        whole band of source rows/columns it covers.  An 8x8 source pixel at
        (dx, dy) therefore feeds every destination pixel with py in
        [dy*cell//8, ceil((dy+1)*cell/8)-1] (same for px).  Those ranges tile
        [0, 8) with no gaps and no drops, so small text keeps the glyph's full
        8-row/8-column span and no horizontal slice is ever shaved off - in
        particular the top row of caps and digits is never cut.  (The earlier
        centre-assignment variant sent each source pixel to a single
        destination pixel, which gave the top destination row only raster row
        0, a 1px sliver, so the tops of most of the font looked cut off at
        cells 3-7.)  At cell 8 the ranges collapse to single pixels (the
        authentic 1:1 CGA raster); at cell 1 a letter is one pixel and a
        space stays empty.

        For cell > 8 (only reachable when no font is available) the old
        stretch is kept instead: each source pixel scales to [d*cell//8,
        (d+1)*cell//8), which is gap-free for cell >= 8."""
        glyph = FONT_8X8.get(ord(ch), FONT_8X8[32])
        mask = [[0] * cell for _ in range(cell)]
        if cell <= 8:
            # Area-based max filter (see docstring).  For each inked source
            # pixel, OR it into every destination pixel whose area overlaps
            # it.  ceil((d+1)*cell/8) is ((d+1)*cell + 7)//8, and the -1
            # turns the inclusive source edge into the last destination pixel
            # index; clamp to the cell bounds (no-op for cell 1-8).
            for dy in range(8):
                bits = glyph[dy]
                if not bits:
                    continue
                y0 = (dy * cell) // 8
                y1 = min(((dy + 1) * cell + 7) // 8 - 1, cell - 1)
                for dx in range(8):
                    if not (bits >> (7 - dx)) & 1:
                        continue
                    x0 = (dx * cell) // 8
                    x1 = min(((dx + 1) * cell + 7) // 8 - 1, cell - 1)
                    for py in range(max(y0, 0), y1 + 1):
                        mrow = mask[py]
                        for px in range(max(x0, 0), x1 + 1):
                            mrow[px] = 1
        else:
            for dy in range(8):
                bits = glyph[dy]
                sy0 = (dy * cell) // 8
                sy1 = ((dy + 1) * cell) // 8
                for py in range(sy0, sy1):
                    mrow = mask[py]
                    for dx in range(8):
                        if not (bits >> (7 - dx)) & 1:
                            continue
                        bx0 = (dx * cell) // 8
                        bx1 = ((dx + 1) * cell) // 8
                        for px in range(bx0, bx1):
                            if 0 <= px < cell:
                                mrow[px] = 1
        return mask

    def _bitmap_image(self, ch):
        """The 8x8 FONT_8X8 glyph for ch (a space when unknown) as a PIL
        "L" image, 255 ink on a 0 background - the rotation pipeline's
        bitmap base (see _rotated_glyph_vals)."""
        from PIL import Image
        glyph = FONT_8X8.get(ord(ch), FONT_8X8[32])
        img = Image.new("L", (8, 8), 0)
        px = img.load()
        for dy in range(8):
            bits = glyph[dy]
            for dx in range(8):
                if (bits >> (7 - dx)) & 1:
                    px[dx, dy] = 255
        return img

    def _rotate_mask_nn(self, mask, angle):
        """Rotate a 0/1 mask (list of rows) by angle degrees CLOCKWISE (as
        displayed) about the mask centre, nearest-neighbour inverse
        mapping; exact for multiples of 90.  This is the no-PIL fallback
        for _rotated_glyph_vals, so TEXTRotate still works without PIL
        (coarse at other angles, since it rotates the final cell raster).
        """
        n = len(mask)
        if n <= 1:
            return mask
        import math
        a = math.radians(angle % 360)
        cos, sin = math.cos(a), math.sin(a)
        c = (n - 1) / 2
        out = [[0] * n for _ in range(n)]
        for v in range(n):            # destination row (screen y, down)
            for u in range(n):        # destination column (screen x, right)
                # Inverse map of a clockwise rotation about the centre:
                # rotate the destination pixel back by -angle (in math
                # coords, y up) to find the source pixel it samples.
                x = (u - c) * cos + (v - c) * sin + c
                y = c - (u - c) * sin + (v - c) * cos
                sx = int(round(x))
                sy = int(round(y))
                sx = 0 if sx < 0 else (n - 1 if sx > n - 1 else sx)
                sy = 0 if sy < 0 else (n - 1 if sy > n - 1 else sy)
                out[v][u] = mask[sy][sx]
        return out

    def _rotated_glyph_vals(self, ch, cell, angle):
        """cell x cell 2D list of 0-255 coverage (vals[cy][cx]) for ch
        rotated angle degrees CLOCKWISE (as displayed) about the cell
        centre.  The glyph is first rasterized at 4x supersample on the
        same fixed baseline as the upright path (the cell-matched font at
        every cell size; the 8x8 FONT_8X8 bitmap scaled up only when no
        font is available), rotated with cubic interpolation - a pixel
        permutation, so
        exact - for multiples of 90, then LANCZOS-downsampled to the cell.
        When PIL is absent the crisp 0/1 cell raster is rotated with
        _rotate_mask_nn instead (values 0/255): exact at 90/180/270,
        coarse otherwise."""
        s = max(2, cell) * 4
        try:
            from PIL import Image
            try:
                lanc = Image.Resampling.LANCZOS
                bic = Image.Resampling.BICUBIC
                nearest = Image.Resampling.NEAREST
            except AttributeError:
                lanc = Image.ANTIALIAS
                bic = Image.BICUBIC
                nearest = Image.NEAREST
            img = None
            if self._use_font and self._font is not None:
                font = self._cell_font(cell)
                if font is not None:
                    try:
                        from PIL import ImageDraw
                        img = Image.new("L", (s, s), 0)
                        ascent, descent = font.getmetrics()
                        baseline = int(round(cell * 0.72)) * (s // cell)
                        baseline = min(baseline, s - max(1,
                                                         descent // (s // cell)))
                        ImageDraw.Draw(img).text((s // 2, baseline), ch,
                                                 fill=255, font=font,
                                                 anchor="ms")
                    except Exception:
                        img = None
            if img is None:
                # Bitmap base: the 8x8 glyph nearest-scaled to the
                # supersample size, so it rotates through the same
                # pipeline as the font path.
                img = self._bitmap_image(ch).resize((s, s), nearest)
            # PIL rotate() turns counter-clockwise: a negative angle is
            # CLOCKWISE as displayed.
            rot = img.rotate(-angle, resample=bic, expand=False, fillcolor=0)
            px = rot.resize((cell, cell), lanc).load()
            return [[px[cx, cy] for cx in range(cell)] for cy in range(cell)]
        except Exception:
            pass  # no usable PIL: fall through to the pure-Python path
        return [[v * 255 for v in row]
                for row in self._rotate_mask_nn(self._bitmap_mask(ch, cell),
                                                angle)]

    def _glyph_mask(self, ch, cell):
        """Return a cached cell x cell list of rows of 0/1 ink for one
        character, or None when the caller should use the FONT_8X8 bitmap
        path instead (no usable font: PIL absent / no font loaded - the
        real font is used for every cell size).

        The glyph is rasterized at 4x supersample, centered in the
        monospace cell on the same fixed baseline as always, rotated by the
        current TEXTRotate angle (0 = upright) about the cell centre,
        LANCZOS-downsampled to cell x cell and thresholded to a crisp 0/1
        mask.  The buffer only holds 16 palette colors, so the glyph is a
        clean two-color shape.  The pre-threshold coverage is kept for the
        window display's grayscale compositing (see _display_body); both
        caches are keyed with the angle, so a mid-page TEXTRotate keeps
        every character at the angle it was drawn with."""
        if cell <= 0:
            return None
        angle = self.text_rotate % 360
        key = (cell, ch, angle)
        mask = self._mask_cache.get(key)
        if mask is not None:
            return mask
        if angle == 0:
            if not self._use_font or self._font is None:
                return None
            if self._cell_font(cell) is None:
                self._use_font = False
                return None
            vals = self._glyph_font_vals(ch, cell)
            if vals is None:
                self._use_font = False  # image ops failed: stop using the
                # font
                return None
        else:
            vals = self._rotated_glyph_vals(ch, cell, angle)
        # Threshold the anti-aliased coverage to a crisp 0/1 shape at ~37.5%
        # ink (96/255): the old 50% cutoff (128) shaved thin strokes and
        # partially-covered edge pixels, which made letters look skeletal and
        # broken.  A space has no ink -> all zeros.  The pre-threshold values
        # are kept for the window display's grayscale compositing (see
        # _display_body).
        mask = [[0] * cell for _ in range(cell)]
        cov = bytearray(cell * cell)
        for cy in range(cell):
            orow = mask[cy]
            base = cy * cell
            vrow = vals[cy]
            for cx in range(cell):
                v = vrow[cx]
                cov[base + cx] = v
                if v >= 96:
                    orow[cx] = 1
        # Bounded cache: reset when it grows past ~1400 entries (a few hundred
        # distinct (size, char, angle) triples is the realistic maximum for a
        # program).
        if len(self._mask_cache) > 1400:
            self._mask_cache.clear()
            self._cov_cache.clear()
        self._mask_cache[key] = mask
        self._cov_cache[key] = cov
        return mask

    def _font_candidate_paths(self):
        """Ordered list of .ttf paths for the CURRENT text face
        (self.text_font, see textfont): the selected face's file first, then
        the generic fallback chain, so a missing family (or a weight that
        maps to None on a single-face font) still renders with a usable
        font instead of dropping to the 8x8 bitmap."""
        import os
        face, bold, italic = self.text_font
        wkey = ('b' if bold else '') + ('i' if italic else '')
        files = TEXTFONT_FACES.get(face) or TEXTFONT_FACES['ARIAL']
        # A None entry (single-face font, weight requested) falls back to
        # the family's regular file - get()'s default only covers MISSING
        # keys, not keys present with a None value.
        fname = files.get(wkey) or files['']
        cands = []
        if os.name == 'nt':
            fd = os.path.join(os.environ.get('WINDIR', 'C:\\Windows'), 'Fonts')
            if fname:
                cands.append(os.path.join(fd, fname))
            for n in ('arial.ttf', 'segoeui.ttf', 'tahoma.ttf',
                      'calibri.ttf'):
                cands.append(os.path.join(fd, n))
        else:
            if fname:
                cands.append(fname)
            for n in ('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf',
                      '/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf',
                      '/System/Library/Fonts/Supplemental/Arial.ttf'):
                cands.append(n)
        return cands

    def _cell_font(self, cell):
        """Return a PIL ImageFont whose cap height matches the given cell size
        (in pixels), cached per cell.  Drawing every glyph at this size keeps
        the font's natural proportions (so all letters read as one font) while
        making a cap fill the cell.  Returns None when PIL is absent or no
        font could be loaded (the caller then uses the FONT_8X8 bitmap path)."""
        from PIL import ImageFont
        f = self._font_cache.get(('cell', cell))
        if f is not None:
            return f
        # Size the font so a capital fills ~ the cell when drawn with
        # anchor="ms" on the cell baseline.  Empirically (Arial) a capital
        # ink height is ~cell at point size ~cell*4 (see _glyph_mask); smaller
        # sizes leave the cap tiny, larger ones clip it.  Clamped so a tiny
        # cell still gets a usable font.
        size = max(10, int(round(cell * 4)))
        for path in self._font_candidate_paths():
            try:
                f = ImageFont.truetype(path, size)
                break
            except Exception:
                continue
        if f is not None:
            self._font_cache[('cell', cell)] = f
        return f

    def _ensure_font(self, size=128):
        """Load a real (anti-aliased) font at a fixed pixel size (default
        128), if one is available, and mark it usable.  The size is a probe
        size only - _glyph_mask draws each cell from its own size-matched
        instance (see _cell_font) - so the font is loaded once up front and
        the result simply gates the font path for every TEXTSIZE.  Sets
        self._use_font/self._font; never raises - if PIL or every candidate
        font is missing it leaves _use_font False so the FONT_8X8 bitmap path
        is used."""
        f = self._font_cache.get(size)
        if f is not None:
            self._font = f
            self._use_font = True
            return
        import os
        try:
            from PIL import ImageFont  # noqa: F401
        except Exception:
            self._use_font = False
            self._font = None
            return
        for path in self._font_candidate_paths():
            try:
                self._font_cache[size] = f = ImageFont.truetype(path, size)
                break
            except Exception:
                continue
        if f is not None:
            self._font = f
            self._use_font = True
        else:
            self._use_font = False
            self._font = None

    def _blit_glyph(self, buf, w, h, ch, x, y, fg, bg, cell=None):
        """Composite one character cell into a pixel buffer (a w x h list of
        rows of color indices), top-left at (x, y).  The cell is
        self.cell x self.cell pixels.  The glyph is drawn from the real
        anti-aaused font (see _glyph_mask) at every cell size, so all
        text is smooth instead of a stretched bitmap; only when no font
        is available does it fall back to the FONT_8X8 bitmap downscaled
        to the cell (see _bitmap_mask).  The cell is filled with the
        background color and the glyph's ink is blended into the foreground
        color.  Cells that run off the buffer are clipped.  Returns the (x, y)
        points written (so the caller can feed them to the incremental blit
        tracker)."""
        if cell is None:
            cell = self.cell
        pts = []
        mask = self._glyph_mask(ch, cell)
        if mask is None:
            # Bitmap fallback: the fixed 8x8 glyph downscaled to the cell
            # (max filter - see _bitmap_mask).  Both paths yield the same
            # 0/1 mask shape, so the blit below is identical.
            mask = self._bitmap_mask(ch, cell)
        # The mask is a crisp 0/1 shape: fg where inked, bg elsewhere.  A
        # clean two-color glyph - the buffer only holds 16 palette colors, so
        # a smooth multi-color blend is impossible and the glyph is one color
        # (never a rainbow).  The anti-aaasing lives in the fitted shape
        # itself (see _glyph_mask).
        for cy in range(cell):
            py = y + cy
            if py < 0 or py >= h:
                continue
            row = buf[py]
            mrow = mask[cy]
            for cx in range(cell):
                px = x + cx
                if px < 0 or px >= w:
                    continue
                row[px] = fg if mrow[cx] else bg
                pts.append((px, py))
        return pts

    def _gfx_text_scroll(self):
        """Scroll the graphics text page up one row: the whole surface
        shifts up one text cell (self.cell pixels) and the newly exposed
        bottom becomes the text background (an authentic monitor scroll)."""
        h = self.rows
        w = self.cols
        cell = self.cell
        pixels = self.pixels
        if h > cell:
            for y in range(h - cell):
                pixels[y] = pixels[y + cell][:]
        bgc = _resolve_color(self.bg)  # graphics mode: keep RGB() indexes
        for y in range(max(0, h - cell), h):
            pixels[y] = [bgc] * w
        # Shift the window-display text records with the surface (they must
        # stay aligned with the pixels); drop what scrolled off the top.
        if self._gfx_text:
            self._gfx_text = [(x0, y0 - cell, c, ch, fg, bg, ang)
                              for (x0, y0, c, ch, fg, bg, ang)
                              in self._gfx_text
                              if y0 - cell + c > 0]
        # Every pixel moved: the next blit must cover the whole frame.
        self._dirty_full = True
        self._dirty_pts = set()
        self._gfx_dirty()

    def _print_gfx_char(self, ch):
        """Write one character of the graphics text page at the text cursor
        and advance it (same rules as the text-mode _advance: wrap to the
        next row, scroll at the bottom)."""
        page_cols, page_rows = self._gfx_text_page()
        if ch == '\n':
            self._rot_pivot = None  # newline ends the rotated line, if any
            self.cursor_col = 0
            self.cursor_row += 1
            if self.cursor_row >= page_rows:
                self._gfx_text_scroll()
                self.cursor_row = page_rows - 1
            self._gfx_dirty()
            return
        if self.text_rotate % 360:
            # Rotated line (TEXTRotate != 0): the characters advance along
            # a baseline rotated about the line's pivot, not along the
            # character grid (see _print_rot_char).  The grid cursor stays
            # at the line's start; the newline above moves to the next row.
            self._print_rot_char(ch)
            return
        if self.cursor_row < page_rows and self.cursor_col < page_cols:
            cell = self.cell
            x0 = self.cursor_col * cell
            y0 = self.cursor_row * cell
            fg_c, bg_c = self._fg_bg_pixels()
            pts = self._blit_glyph(self.pixels, self.cols, self.rows, ch,
                                   x0, y0, fg_c, bg_c)
            colw = self.cols
            self._dirty_pts.update(py * colw + px for (px, py) in pts)
            # Remember the character for the WINDOW display: it re-composites
            # this cell from the font's anti-aliased coverage (see
            # _display_body) while the pixel buffer keeps the crisp 2-color
            # mask for GET capture.  Bitmap-path characters (font
            # unavailable, or cells below the font cutoff) have no coverage
            # and stay as the buffer shows them.  A new print over an old
            # character replaces its record (the cell was fully repainted) -
            # including a SPACE, which erases the cell: the pixel buffer is
            # already filled with the background above, and any stale
            # anti-aliased record left at this cell would be re-composited
            # over it by _display_body on the next render, so the glyph
            # would visibly come back.  The removal therefore runs for
            # every character (a space erases, the append is still
            # coverage-guarded so a blank leaves no record behind).
            x1, y1 = x0 + cell, y0 + cell
            self._gfx_text[:] = [
                r for r in self._gfx_text
                if not (r[0] < x1 and x0 < r[0] + r[2]
                        and r[1] < y1 and y0 < r[1] + r[2])]
            if ch != ' ' and self._glyph_mask(ch, cell) is not None:
                self._gfx_text.append((x0, y0, cell, ch,
                                       fg_c, bg_c,
                                       self.text_rotate % 360))
                if len(self._gfx_text) > 4096:
                    del self._gfx_text[:len(self._gfx_text) - 4096]
        self.cursor_col += 1
        if self.cursor_col >= page_cols:
            self.cursor_col = 0
            self.cursor_row += 1
            if self.cursor_row >= page_rows:
                self._gfx_text_scroll()
                self.cursor_row = page_rows - 1
        self._gfx_dirty()

    def _print_rot_char(self, ch):
        """Print one character of a rotated line (TEXTRotate != 0).

        The line is a rigid rotation about its pivot - the cursor's cell at
        the line's start, captured in _rot_pivot together with the angle in
        force when the line BEGAN (a mid-line TEXTRotate applies to the
        NEXT line): glyph n sits at pivot + n*cell*(cos, sin) of the angle
        (clockwise, screen coordinates), i.e. along the baseline rotated by
        the angle from horizontal, and each glyph is itself turned by the
        angle about its own cell centre (see _glyph_mask) - which is
        exactly the upright line rotated about the pivot.  The grid cursor
        is untouched (the line occupies its starting grid row), and
        characters beyond the surface edge are clipped like any drawing.
        The line is composited straight into the pixel buffer (GET capture)
        and recorded for the window display's anti-aliased
        re-composite (see _display_body); unlike the upright path, no old
        records are dropped here - rotated neighbour cells overlap slightly
        and the later records win in the overlap, keeping the display
        consistent with the buffer's painter's-algorithm compositing."""
        cell = self.cell
        if self._rot_pivot is None:
            # Line start: the pivot is the cursor's cell (pixel units) and
            # the angle is captured now.
            self._rot_pivot = (self.cursor_col * cell,
                               self.cursor_row * cell,
                               self.text_rotate % 360, 0)
        x0, y0, angle, n = self._rot_pivot
        a = math.radians(angle)
        x = round(x0 + n * cell * math.cos(a))
        y = round(y0 + n * cell * math.sin(a))
        fg_c, bg_c = self._fg_bg_pixels()
        pts = self._blit_glyph(self.pixels, self.cols, self.rows, ch, x, y,
                               fg_c, bg_c)
        colw = self.cols
        self._dirty_pts.update(py * colw + px for (px, py) in pts)
        if ch != ' ' and self._glyph_mask(ch, cell) is not None:
            self._gfx_text.append((x, y, cell, ch, fg_c,
                                   bg_c, angle))
            if len(self._gfx_text) > 4096:
                del self._gfx_text[:len(self._gfx_text) - 4096]
        self._rot_pivot = (x0, y0, angle, n + 1)
        self._gfx_dirty()

    def locate(self, row, col):
        # Range checking is done by the interpreter ("Illegal function
        # call" for out-of-range values); this just moves the cursor.
        self.cursor_row = int(row)
        self.cursor_col = int(col)
        # A LOCATE starts a new line: drop any rotated line in progress.
        self._rot_pivot = None

    def csrlin(self):
        return self.cursor_row + 1

    def screen_at(self, row, col, z=False):
        # SCREEN(row, col[, z]) function (manual SCREENF): the ASCII code
        # (0-255) of the character at (row, col); when z is true (alpha
        # mode), the color attribute instead.  row must be 1-25 and col
        # 1-40 (text mode); values outside the range are an "Illegal
        # function call".
        if self.is_text():
            max_col = self.cols
        else:
            # Graphics mode: the virtual text screen is one character column
            # per self.cell pixels wide (40 in the 320-pixel modes at the
            # default 8px cell, 80 in the 640-pixel modes).
            max_col = self.cols // self.cell
        if not (1 <= row <= 25) or not (1 <= col <= max_col):
            raise BasicError("Illegal function call")
        if self.grid is not None:
            ch, fg, bg = self.grid[row - 1][col - 1]
        else:
            # Graphics mode: the display has no character contents.
            ch, fg, bg = ' ', self.fg, self.bg
        if z:
            return (bg << 4) | fg
        return ord(ch)

    def cls(self):
        if self.is_text():
            self._init_grid()
        else:
            bgc = _resolve_color(self.bg)  # keep dynamic RGB() indexes
            self.pixels = [[bgc] * self.cols
                           for _ in range(self.rows)]
            self._gfx_text = []  # window-display text records go with it
            self._rot_pivot = None  # a CLS ends any rotated line
            # CLS must NOT force a full-frame blit and must NOT render inline.
            # A full-frame rebuild here would (a) cost a whole-frame PPM
            # PhotoImage build every frame and (b) trigger a second paint on
            # top of the run loop's end-of-line flush(), so a clear-and-`
            # redraw animation (CLS + redraw each frame, e.g. spawn.bas) blits
            # twice per frame.  Instead, mark the buffer dirty and let the
            # single end-of-line flush() do one blit.  _dirty_pts holds every
            # pixel that was drawn since the last blit, so the incremental
            # blit restores them to the cleared (background) color and puts
            # the new frame's pixels - O(changed pixels), not O(frame size).
            self._dirty_full = False
            self._dirty = True
        self.cursor_row = 0
        self.cursor_col = 0

    def _fg_bg_pixels(self):
        """(fg, bg) color INDEXES for compositing text into the pixel buffer.

        Text mode strips the blink high bit (fg 0-31 -> 0-15); graphics
        mode passes the current colors through, keeping dynamic RGB() color
        indexes (>= 16) intact instead of wrapping them % 16."""
        if self.is_text():
            return self.fg % 16, self.bg % 16
        return _resolve_color(self.fg), _resolve_color(self.bg)

    def color(self, fg=None, bg=None, border=None):
        # Manual COLOR: per-mode argument validation.
        #   SCREEN 0:  fg 0-31 (blink = +16), bg 0-7, border 0-15.
        #   SCREEN 1:  fg 0-3, second argument is the palette (even/odd).
        #   SCREEN 2:  always "Illegal function call".
        #   SCREEN 7-10: fg/bg within the mode's color range, no border.
        #   Graphics modes additionally accept defined RGB() colors (16+).
        # Any argument outside its valid range is an "Illegal function
        # call"; the previous colors are retained.
        if self.mode == 2:
            raise BasicError("Illegal function call")
        if self.is_text():
            if fg is None and bg is None and border is None:
                # Bare COLOR in SCREEN 0: background and border become
                # black, foreground becomes the mode default (manual COLOR).
                fg, bg, border = 7, 0, 0
            if fg is not None:
                fg = int(fg)
                if fg < 0 or fg > 31:
                    raise BasicError("Illegal function call")
            if bg is not None:
                bg = int(bg)
                if bg < 0 or bg > 7:
                    raise BasicError("Illegal function call")
            if border is not None:
                border = int(border)
                if border < 0 or border > 15:
                    raise BasicError("Illegal function call")
        else:
            # Custom-size modes use a full 256-color (15) palette.  Defined
            # RGB() colors (indexes 16 and up) are legal in graphics modes
            # too; an UNDEFINED index >= 16 is an "Illegal function call"
            # (the drawing commands instead wrap it % 16, see
            # _resolve_color - the statement validates strictly).  In text
            # mode the fg 0-31 range is unchanged: +16 is the blink flag
            # there, so dynamic colors would collide with it.
            cmax = GFX_COLOR_MAX.get(self.mode, 15)
            if fg is not None:
                fg = int(fg)
                if not (0 <= fg <= cmax or
                        16 <= fg <= 15 + len(DYN_RGB3)):
                    raise BasicError("Illegal function call")
            if bg is not None:
                bg = int(bg)
                if not (0 <= bg <= cmax or
                        16 <= bg <= 15 + len(DYN_RGB3)):
                    raise BasicError("Illegal function call")
            if border is not None:
                # No border color can be specified in graphics modes.
                raise BasicError("Illegal function call")
        if fg is not None:
            self.fg = fg
        if bg is not None:
            self.bg = bg
        if border is not None:
            self.border = border
        if self.is_text():
            for r in range(self.rows):
                for c in range(self.cols):
                    self.grid[r][c][1] = self.fg
                    self.grid[r][c][2] = self.bg

    def ink(self, n, color=None):
        n = int(n)
        if color is not None:
            c = int(color)
            # Like COLOR, INK validates strictly: colors are 0-15 or a
            # DEFINED dynamic RGB() color; an undefined index >= 16 is an
            # "Illegal function call" (legacy drawing commands wrap % 16).
            if not (0 <= c <= 15 or 16 <= c <= 15 + len(DYN_RGB3)):
                raise BasicError("Illegal function call")
            self._ink[n % 16] = _resolve_color(c)
        return self._ink[n % 16]

    def palette(self, first, last, color):
        # In real GW-BASIC this remaps hardware palette entries; we just note it.
        pass

    def beep(self):
        import sys
        sys.stdout.write('\a')
        sys.stdout.flush()

    def cursor(self, visible):
        self.cursor_visible = bool(visible)

    def view(self, x1, y1, x2, y2, screen=False):
        # Manual VIEW: the coordinate pairs are sorted (smallest first) and
        # must be within the physical bounds of the screen.  Without the
        # SCREEN argument, points are plotted relative to the viewpoint;
        # with it, absolutely.
        x1, x2 = sorted((int(x1), int(x2)))
        y1, y2 = sorted((int(y1), int(y2)))
        if not self.is_text() and (
                x1 < 0 or x2 > self.cols - 1 or
                y1 < 0 or y2 > self.rows - 1):
            raise BasicError("Illegal function call")
        self.view_rect = (x1, y1, x2, y2)
        self.view_screen = bool(screen)

    def window(self, x1=None, y1=None, x2=None, y2=None, screen=False):
        # WINDOW [[SCREEN](x1,y1)-(x2,y2)] re-imagined for Windows: the
        # original statement assumed a full-screen CGA/EGA monitor; here the
        # OS window IS the monitor.  With coordinates it simply runs an
        # internal SCREENSIZE sized to the work area's span, positioned so
        # the monitor's center is world (0,0); with no arguments it resets
        # the world-coordinate mapping only (manual WINDOW's "disable
        # previous window statements") - the window itself is the monitor
        # and is never torn down by WINDOW.
        if x1 is None:
            # Bare WINDOW: reset the world-coordinate mapping so graphics
            # statements address the physical screen again.  The window is
            # NOT touched - only program end, Ctrl+C, WCLOSE, or the
            # window's own ESC / close box ever destroy it.
            self.window_rect = None
            self.window_screen = False
            return
        x1, y1 = float(x1), float(y1)
        x2, y2 = float(x2), float(y2)
        if x1 == x2 or y1 == y2:
            raise BasicError("Illegal function call")
        # The x and y pairs are sorted into ascending order (manual WINDOW:
        # WINDOW (50,50)-(10,10) becomes (10,10)-(50,50)), so (x1,y1) is
        # always the lower (x-min, y-min) corner.
        x1, x2 = sorted((x1, x2))
        y1, y2 = sorted((y1, y2))
        # The internal SCREENSIZE: the OS window becomes the work area
        # itself, sized to its span (one world unit ~ one pixel).
        w = int(round(x2 - x1))
        h = int(round(y2 - y1))
        self.set_mode(CUSTOM_SCREEN_MODE, size=(w, h))
        self.window_rect = (x1, y1, x2, y2)
        self.window_screen = bool(screen)
        # Now position the window so world (0,0) sits at the center of the
        # monitor: top-left = monitor center - the drawing-area pixel where
        # (0,0) lands (computed after set_mode, which clears the window
        # state).  A single geometry() call - see _place_window_at_origin.
        px0, py0, _ = self._world_to_phys(0, 0)
        self._window_origin = (px0, py0)
        self._window_topleft = None  # WINDOW's own placement supersedes a
        # pending SCREENSIZE placement (see the screensize handler).
        self._place_window_at_origin()

    def _place_window_at_origin(self):
        """One-shot placement: move the OS window so the drawing-area pixel
        of world (0,0) (self._window_origin) lands on the monitor center.

        Exactly one geometry() call, issued in plain Python - the window is
        either just being created (called from _init_gui before it maps)
        or already mapped (a single move).  There is no follow-up
        correction: the <Configure> events the move generates only go
        through the ordinary resize handler and change nothing."""
        if self._root is None or self._window_origin is None:
            return
        try:
            sw = self._root.winfo_screenwidth()
            sh = self._root.winfo_screenheight()
            if sw < 2 or sh < 2:
                return
            px0, py0 = self._window_origin
            left = int(round(sw / 2 - px0))
            top = int(round(sh / 2 - py0))
            self._root.geometry("+%d+%d" % (left, top))
        except Exception:
            pass
        finally:
            self._window_origin = None

    # -- graphics ------------------------------------------------------------ #
    def _in_view(self, x, y):
        # Gate a logical point.  An active WINDOW maps world coordinates onto
        # the physical screen, so the point is in view when its physical
        # image lands on the screen.  Otherwise the VIEW rectangle (manual
        # VIEW) applies: without the SCREEN argument points are relative to
        # the viewpoint, with it they are absolute.
        if self.window_rect is not None:
            wx1, wy1, wx2, wy2 = self.window_rect
            _, _, ok = self._world_to_phys(x, y)
            if not ok:
                return False
            return (min(wx1, wx2) <= x <= max(wx1, wx2)
                    and min(wy1, wy2) <= y <= max(wy1, wy2))
        if self.view_rect is None:
            return 0 <= x < self.cols and 0 <= y < self.rows
        x1, y1, x2, y2 = self.view_rect
        if self.view_screen:
            return x1 <= x <= x2 and y1 <= y <= y2
        return 0 <= x <= x2 - x1 and 0 <= y <= y2 - y1

    def _in_view_phys(self, x, y):
        # Physical-coordinate gate used by the line-drawing routines.
        if x < 0 or x >= self.cols or y < 0 or y >= self.rows:
            return False
        if self.view_rect is not None:
            x1, y1, x2, y2 = self.view_rect
            return x1 <= x <= x2 and y1 <= y <= y2
        return True

    def _world_to_phys(self, x, y):
        """Map a world (WINDOW) coordinate to the physical screen pixel.

        Returns (px, py) plus an in-bounds flag.  With no active WINDOW the
        point passes through unchanged.  Without the SCREEN flag the y-axis
        is inverted (Cartesian): world (wx1,wy1) is the lower-left corner,
        so the physical y is measured from the bottom.  With the SCREEN flag
        it is the ordinary upper-left origin.
        """
        if self.window_rect is None:
            return x, y, True
        wx1, wy1, wx2, wy2 = self.window_rect
        sx = (self.cols - 1) / (wx2 - wx1)
        px = (x - wx1) * sx
        if self.window_screen:
            # (wx1,wy1) is the upper-left: physical y grows downward, so
            # world (wx1,wy1) -> physical top (0) and (wx1,wy2) -> bottom.
            py = (y - wy1) * ((self.rows - 1) / (wy2 - wy1))
        else:
            # (wx1,wy1) is the lower-left (Cartesian): world y increases
            # upward, so world (wx1,wy1) -> physical bottom (rows-1) and
            # (wx1,wy2) -> top (0); physical y decreases as world y grows.
            py = (self.rows - 1) - (y - wy1) * ((self.rows - 1) / (wy2 - wy1))
        px = int(round(px))
        py = int(round(py))
        return px, py, (0 <= px < self.cols and 0 <= py < self.rows)

    def _physical(self, x, y):
        # Logical -> physical.  The WINDOW world mapping (if active) is
        # applied first, then the VIEW offset (manual VIEW: without the
        # SCREEN argument, x1 and y1 are added to the coordinates before the
        # point is plotted).
        wx, wy, _ = self._world_to_phys(x, y)
        if self.view_rect is not None and not self.view_screen:
            x1, y1, _, _ = self.view_rect
            return wx + x1, wy + y1
        return wx, wy

    def _phys_to_world(self, px, py):
        """Inverse of _world_to_phys: physical pixel -> world (WINDOW)
        coordinate, rounded to the nearest integer.  Used by the MOUSE
        statement to report click locations in the program's coordinate
        space."""
        if self.window_rect is None or self.cols < 2 or self.rows < 2:
            return int(round(px)), int(round(py))
        wx1, wy1, wx2, wy2 = self.window_rect
        wx = wx1 + px * ((wx2 - wx1) / (self.cols - 1))
        if self.window_screen:
            wy = wy1 + py * ((wy2 - wy1) / (self.rows - 1))
        else:
            wy = wy1 + (self.rows - 1 - py) * ((wy2 - wy1) / (self.rows - 1))
        return int(round(wx)), int(round(wy))

    def pset(self, x, y, color):
        if self.is_text():
            return
        x, y = int(x), int(y)
        if self._in_view(x, y):
            px, py = self._physical(x, y)
            self.pixels[py][px] = _resolve_color(color)
            self._dirty_pts.add(self._dpt(px, py))
        self._gfx_dirty()

    def preset(self, x, y, color):
        if self.is_text():
            return
        x, y = int(x), int(y)
        if self._in_view(x, y):
            px, py = self._physical(x, y)
            self.pixels[py][px] = _resolve_color(color) if color is not None else 0
            self._dirty_pts.add(self._dpt(px, py))
        self._gfx_dirty()

    def _gfx_dirty(self):
        # Batch the redraw: just mark dirty.  The run loop calls flush() once
        # per executed line, so a CIRCLE/PSET burst rebuilds the window a
        # single time instead of once per plotted pixel (which froze the
        # window for minutes).
        self._dirty = True

    def _dpt(self, x, y):
        # Encode a physical (x, y) as one int (y*cols+x) so the dirty set
        # holds small ints instead of per-pixel (x, y) tuples - a LINE with a
        # dotted style marks tens of thousands of points and the tuple
        # allocations dominated the profile.  Decoded in _render_gfx / _diff.
        return y * self.cols + x

    def line(self, x1, y1, x2, y2, color, bf='', style=None):
        # Manual LINE: style is a 16-bit mask; each plotted point consumes
        # the next circulating bit (0 -> no store, 1 -> store).  The
        # interpreter rejects BF combined with style ("Syntax" error).
        if self.is_text():
            return
        color = _resolve_color(color) if color is not None else self.fg
        bf = (bf or '').upper()
        box = 'B' in bf
        fill = 'F' in bf
        st = [0, int(style) & 0xFFFF] if style is not None else None
        x1, y1 = self._physical(int(x1), int(y1))
        x2, y2 = self._physical(int(x2), int(y2))
        if box:
            self._hline(x1, y1, x2, y1, color, st)
            self._hline(x1, y2, x2, y2, color, st)
            self._vline(x1, y1, y2, color, st)
            self._vline(x2, y1, y2, color, st)
            if fill:
                lo_x, hi_x = sorted((x1, x2))
                lo_y, hi_y = sorted((y1, y2))
                # Fill the rectangle directly in the pixel buffer: a
                # per-pixel _plot_pt loop costs a million Python calls on a
                # large box and freezes the window.
                buf = self.pixels
                dirty = self._dirty_pts
                for yy in range(max(0, lo_y), min(hi_y, self.rows - 1) + 1):
                    row = buf[yy]
                    base = yy * self.cols
                    for xx in range(max(0, lo_x), min(hi_x, self.cols - 1) + 1):
                        row[xx] = color
                        dirty.add(base + xx)
        else:
            self._plot_line(x1, y1, x2, y2, color, st)
        self._gfx_dirty()

    def _plot_pt(self, x, y, color, st):
        """Store one physical point, honoring the circulating style bit."""
        if st is not None:
            bit = (st[1] >> (st[0] % 16)) & 1
            st[0] += 1
            if bit == 0:
                return
        if self._in_view_phys(x, y):
            self.pixels[y][x] = color
            self._dirty_pts.add(self._dpt(x, y))

    def _plot_line(self, x0, y0, x1, y1, color, st=None):
        dx = abs(x1 - x0)
        dy = abs(y1 - y0)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx - dy
        while True:
            self._plot_pt(x0, y0, color, st)
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 > -dy:
                err -= dy
                x0 += sx
            if e2 < dx:
                err += dx
                y0 += sy

    def _hline(self, x1, y, x2, y2, color, st=None):
        lo, hi = sorted((int(x1), int(x2)))
        for x in range(lo, hi + 1):
            self._plot_pt(x, int(y), color, st)

    def _vline(self, x, y1, y2, color, st=None):
        lo, hi = sorted((int(y1), int(y2)))
        for y in range(lo, hi + 1):
            self._plot_pt(int(x), y, color, st)

    def circle(self, x, y, r, color=None, start=None, end=None, aspect=None):
        if self.is_text():
            return
        color = _resolve_color(color) if color is not None else self.fg
        r = int(r)
        # aspect is the x-radius : y-radius ratio (manual CIRCLE).  A default
        # (None) or 1 draws a circle; otherwise an ellipse.  Per the manual,
        # aspect < 1 means the radius is given in x-pixels, aspect > 1 means
        # it is given in y-pixels.
        if aspect is None or aspect == 1:
            x_r = y_r = r
        elif aspect > 1:
            y_r = r
            x_r = int(round(r * aspect))
        else:
            x_r = r
            y_r = int(round(r / aspect))
        # Midpoint circle for a true circle outline (no arc, aspect 1).
        if start is None and end is None and x_r == y_r:
            # Midpoint circle (Bresenham).  The decision variable decides
            # whether to step outward (x+1, y-1) or along x (x+1).  Only the
            # outward step decrements the y radius; decrementing it every
            # iteration (as before) collapses the radii and draws a diamond.
            xo = 0
            yo = r
            d = 1 - r
            while xo <= yo:
                for px, py in self._circle_points(x, y, xo, yo):
                    self.pset(px, py, color)
                if d < 0:
                    d += 2 * xo + 3
                else:
                    d += 2 * (xo - yo) + 5
                    yo -= 1
                xo += 1
        else:
            # Arc, or a non-circular ellipse: sample angles parametrically.
            if start is None and end is None:
                s, e = 0.0, 2 * math.pi
            else:
                # Manual CIRCLE: start/end are already radians (manual
                # range -2pi..2pi), so use them directly; the old code
                # passed them through math.radians() and misread them
                # as degrees.  A negative start/end is treated as its
                # positive counterpart (NOT 2pi + angle): the arc uses
                # the positive angle, and the ellipse is additionally
                # connected to the center with a straight line.
                s = abs(float(start)) if start is not None else 0.0
                e = abs(float(end)) if end is not None else 2 * math.pi
                if e < s:
                    e += 2 * math.pi
            steps = max(2, int(360 * max(x_r, y_r) / 4))
            for i in range(steps + 1):
                a = s + (e - s) * i / steps
                self.pset(x + int(round(x_r * math.cos(a))),
                          y + int(round(y_r * math.sin(a))), color)
            # Manual CIRCLE: a negative start/end angle connects the
            # ellipse to the center point with a line at the positive
            # angle.  The endpoint uses the same rounding as the arc's
            # first/last sample so line and arc meet at one pixel.
            if start is not None and start < 0:
                self.line(x, y, x + int(round(x_r * math.cos(s))),
                          y + int(round(y_r * math.sin(s))), color)
            if end is not None and end < 0:
                self.line(x, y, x + int(round(x_r * math.cos(e))),
                          y + int(round(y_r * math.sin(e))), color)

    @staticmethod
    def _circle_points(cx, cy, xo, yo):
        return [(cx + xo, cy + yo), (cx - xo, cy + yo),
                (cx + xo, cy - yo), (cx - xo, cy - yo),
                (cx + yo, cy + xo), (cx - yo, cy + xo),
                (cx + yo, cy - xo), (cx - yo, cy - xo)]

    def paint(self, x, y, color=None, border=None, bckgrnd=None):
        """PAINT (x,y) [,[color][,border][,bckgrnd]] (manual PAINT): flood fill.

        Fills the connected region of the starting point's color with the
        paint attribute, stopping at pixels of the border color (default
        the paint attribute).  The start must be a non-border point or
        PAINT has no effect.  Points outside the visible screen are
        ignored (no error).  When a VIEW rectangle is active the fill is
        confined to it.

        Manual PAINT "Paint Tiling": a string paint attribute is a tile
        mask, 8 bits wide and 1-64 bytes long.  Screen row y uses tile
        byte y MOD tile_length (bit 7, the MSB, at x MOD 8 = 0),
        replicated uniformly over the whole screen (as if PAINT (0,0).. had
        been used).  In the 2-bits-per-pixel modes (SCREEN 1/10) every two
        bits of the byte are one of the four colors of the four pixels the
        byte describes; in all other graphics modes a set bit puts down a
        point in the current foreground color and a clear bit puts down
        nothing.  More than two consecutive tile bytes equal to the
        bckgrnd attribute (default CHR$(0)) is an "Illegal function
        call".  A string paint attribute has no single border color, so
        with no explicit border the fill has no border stop (it is
        confined to the connected region of the start color - the manual's
        SCREEN 2 tile example paints the whole screen).  An explicit
        string border attribute is not defined by the manual: "Illegal
        function call".  bckgrnd is the color (or one-character color)
        to skip when checking for boundary termination: a pixel of that
        color is never painted, and the fill passes through it (a start
        on that color fills nothing)."""
        if self.is_text():
            return
        x, y = int(x), int(y)
        if not self._in_view(x, y):
            return
        px, py = self._physical(x, y)
        # -- paint attribute (manual PAINT "Paint Tiling") ---------------- #
        tile = None
        if color is None:
            color = self.fg
        elif isinstance(color, str):
            # A string paint attribute is a tile mask (manual PAINT);
            # the tile is 1-64 bytes long, anything else is an
            # "Illegal function call".
            if not (1 <= len(color) <= 64):
                raise BasicError("Illegal function call")
            tile = color
            color = self.fg
        else:
            color = _resolve_color(color)
        # -- border attribute ---------------------------------------------- #
        # Manual PAINT: the border defaults to the paint attribute.  A
        # numeric border stops the fill at its color.  A string paint
        # attribute has no single border color, so an omitted border
        # gives no border stop (the fill is confined by the target color
        # alone); an explicit string border is undefined by the manual.
        if border is None:
            if tile is not None:
                border = None
            else:
                border = color
        elif isinstance(border, str):
            raise BasicError("Illegal function call")
        else:
            border = _resolve_color(border)
        # -- bckgrnd attribute --------------------------------------------- #
        # Manual PAINT: a string formula returning one character; when
        # omitted the default is CHR$(0) (tile byte 0).
        skip = None
        bckgrnd_byte = 0
        if bckgrnd is not None:
            if isinstance(bckgrnd, str):
                if not bckgrnd:
                    raise BasicError("Illegal function call")
                skip = ord(bckgrnd[0]) & 3
                bckgrnd_byte = ord(bckgrnd[0]) & 0xFF
            else:
                skip = _resolve_color(bckgrnd)
                bckgrnd_byte = int(bckgrnd) & 0xFF
        if tile is not None:
            # Manual PAINT: more than two consecutive tile bytes matching
            # the background attribute -> "Illegal function call".
            run = 0
            for ch in tile:
                run = run + 1 if ord(ch) == bckgrnd_byte else 0
                if run > 2:
                    raise BasicError("Illegal function call")
            # The fill loop indexes this per pixel; convert once.
            tile = [ord(ch) for ch in tile]
        buf = self.pixels
        target = buf[py][px]
        # Manual PAINT: must start on a non-border point, otherwise no effect.
        # A solid fill that starts on the paint color needs nothing done;
        # a tile fill can still change other pixels of the region.
        if border is not None and target == border:
            return
        if tile is None and target == color:
            return
        minx, miny = 0, 0
        maxx, maxy = self.cols - 1, self.rows - 1
        if self.view_rect is not None and not self.view_screen:
            minx, miny, maxx, maxy = self.view_rect
        # Tile coordinates are screen coordinates (manual PAINT indexes the
        # pattern by the graphics cursor position), so undo the VIEW offset;
        # without a VIEW, physical IS the screen coordinate.
        tx0, ty0 = 0, 0
        if self.view_rect is not None and not self.view_screen:
            tx0, ty0 = self.view_rect[0], self.view_rect[1]
        dirty = self._dirty_pts
        if tile is not None:
            # Manual PAINT tiling: every point put down looks up the tile,
            # so the fill visits pixels one at a time (the span/scanline
            # fast paths assume one uniform paint color).
            tl = len(tile)
            twobpp = self.mode in (1, 10)
            seen = set()
            stack = [(px, py)]
            while stack:
                xx, yy = stack.pop()
                c = buf[yy][xx]
                if border is not None and c == border:
                    continue
                if skip is not None and c == skip:
                    # Skipped: not painted, but the fill continues through.
                    if (xx, yy) in seen:
                        continue
                    seen.add((xx, yy))
                elif c != target or (xx, yy) in seen:
                    continue
                else:
                    seen.add((xx, yy))
                    b = tile[(yy - ty0) % tl]
                    if twobpp:
                        # Every two bits (MSB pair first) are the color of
                        # one of the four pixels the byte describes.
                        nc = (b >> (6 - 2 * ((xx - tx0) % 4))) & 3
                    elif (b >> (7 - ((xx - tx0) % 8))) & 1:
                        nc = color
                    else:
                        nc = c  # clear bit: no point put down
                    if nc != c:
                        buf[yy][xx] = nc
                        dirty.add(yy * self.cols + xx)
                for nx, ny in ((xx - 1, yy), (xx + 1, yy),
                               (xx, yy - 1), (xx, yy + 1)):
                    if minx <= nx <= maxx and miny <= ny <= maxy \
                            and (nx, ny) not in seen:
                        stack.append((nx, ny))
            self._gfx_dirty()
            return
        if skip is not None:
            # bckgrnd attribute in effect: a simple scanline span cannot
            # pass through the skipped color, so use a per-pixel fill that
            # neither paints nor terminates at pixels of the skip color.
            # (A start on the skip color fills nothing.)
            if target == skip:
                return
            seen = set()
            stack = [(px, py)]
            while stack:
                xx, yy = stack.pop()
                c = buf[yy][xx]
                if c in (color, border):
                    continue
                if c == skip:
                    # Skipped: not painted, but the fill continues through.
                    if (xx, yy) in seen:
                        continue
                    seen.add((xx, yy))
                else:
                    if c != target or (xx, yy) in seen:
                        continue
                    seen.add((xx, yy))
                    buf[yy][xx] = color
                    dirty.add(yy * self.cols + xx)
                for nx, ny in ((xx - 1, yy), (xx + 1, yy),
                               (xx, yy - 1), (xx, yy + 1)):
                    if minx <= nx <= maxx and miny <= ny <= maxy \
                            and (nx, ny) not in seen:
                        stack.append((nx, ny))
            self._gfx_dirty()
            return
        # Scanline flood fill: expand each span to the full run of target
        # pixels, paint it, and seed spans on the rows above and below.
        stack = [(px, px, py)]
        while stack:
            x1, x2, yy = stack.pop()
            while x1 > minx and buf[yy][x1 - 1] == target:
                x1 -= 1
            while x2 < maxx and buf[yy][x2 + 1] == target:
                x2 += 1
            yu = yy - 1
            yd = yy + 1
            xx = x1
            while xx <= x2:
                if buf[yy][xx] == target:
                    buf[yy][xx] = color
                    dirty.add(yy * self.cols + xx)
                    if yu >= miny and buf[yu][xx] == target:
                        stack.append((xx, xx, yu))
                    if yd <= maxy and buf[yd][xx] == target:
                        stack.append((xx, xx, yd))
                xx += 1
        self._gfx_dirty()

    def _sprite_bounds(self, arr):
        """(w, h, values) of a GET'd screen array: values is a flat row-major
        list of color indices; the array is square-packed by the interpreter
        (width = height = ceiling(sqrt(n))).  Returns None when `arr` is not
        a stored screen array."""
        if isinstance(arr, dict) and '__sprite__' in arr:
            meta = arr['__sprite__']
            w, h, values = meta[0], meta[1], meta[2]
            return (w, h, values)
        return None

    def _get_graphics(self, x1, y1, x2, y2):
        """GET (x1,y1)-(x2,y2) (manual GET, graphics): capture the point
        range as a list of color indices, stored under the array name by the
        interpreter.  Out-of-range corners are allowed (manual GET): the
        capture rectangle is clamped to the screen."""
        if self.pixels is None:
            raise BasicError("Illegal function call")
        x1, y1 = int(x1), int(y1)
        x2, y2 = int(x2), int(y2)
        if x2 < x1:
            x1, x2 = x2, x1
        if y2 < y1:
            y1, y2 = y2, y1
        values = []
        for y in range(max(0, y1), min(self.rows, y2 + 1)):
            row = self.pixels[y]
            for x in range(max(0, x1), min(self.cols, x2 + 1)):
                values.append(row[x])
        return values

    def _put_graphics(self, x, y, w, h, values, color=None, mode=None):
        """PUT (x,y),arr$ [,[color][,XOR|OR|AND]] (manual PUT, graphics):
        blit a captured screen array at (x,y).  The top-left pixel of the
        array is the one drawn at (x,y); the rest of the array is laid out
        row-major from there.  color replaces every non-black pixel; mode
        blends the whole sprite (XOR is the default, then OR, AND)."""
        if self.pixels is None:
            raise BasicError("Illegal function call")
        x, y = int(x), int(y)
        color = _resolve_color(color) if color is not None else None
        mode = (mode or 'XOR').upper()
        n = len(values)
        for row in range(h):
            py = y + row
            if py < 0 or py >= self.rows:
                continue
            buf = self.pixels[py]
            base = row * w
            for col in range(w):
                idx = base + col
                if idx >= n:
                    break
                px = x + col
                if px < 0 or px >= self.cols:
                    continue
                v = values[idx]
                if v == 0:
                    continue
                if color is not None:
                    v = color
                cur = buf[px]
                if mode == 'XOR':
                    nv = v ^ cur
                elif mode == 'OR':
                    nv = v | cur
                else:  # AND
                    nv = v & cur
                # Blends involving dynamic indexes (>= 16) are best-effort:
                # bitwise math on indexes is not meaningful, but the result
                # must never exceed the buffer's legal range (the render
                # path indexes the palette LUT by this value).
                if nv > 15 + len(DYN_RGB3):
                    nv %= 16
                if nv != cur:
                    buf[px] = nv
                    self._dirty_pts.add(self._dpt(px, py))
        self._gfx_dirty()

    def point(self, x, y):
        """POINT (x,y) (manual POINT): the color of the pixel at (x,y),
        or -1 when the point is out of range (or in text mode)."""
        if self.is_text() or self.pixels is None:
            return -1
        px, py = self._physical(int(x), int(y))
        if px < 0 or px >= self.cols or py < 0 or py >= self.rows:
            return -1
        return self.pixels[py][px]

    def point_coord(self, n):
        """POINT (function) (manual POINT): the current graphics
        coordinates (the last referenced point).  0 -> physical x, 1 ->
        physical y, 2 -> the last referenced x coordinate (world
        coordinates when a WINDOW is active), 3 -> the last referenced
        y.  Manual POINT: without an active WINDOW, POINT(2)/POINT(3)
        return the physical coordinates, exactly as POINT(0)/POINT(1).
        Physical = world mapped through the WINDOW (if active), then the
        plain-VIEW offset (manual VIEW: x1, y1 are added to the
        coordinates before the point is plotted)."""
        x, y = int(self.last_x), int(self.last_y)
        n = int(n)
        if self.window_rect is None and n in (2, 3):
            # No WINDOW in effect: 2/3 report the physical coordinates
            # (manual POINT: "otherwise it returns the current physical
            # x coordinate as in 0 above").
            n = 0 if n == 2 else 1
        if n in (0, 1):
            if self.window_rect is not None:
                x, y, _ = self._world_to_phys(x, y)
            if self.view_rect is not None and not self.view_screen:
                x1, y1, _, _ = self.view_rect
                x += x1
                y += y1
        return x if n % 2 == 0 else y

    # ------------------------------------------------------------------ #
    # DRAW / GML (Graphics Macro Language).  Manual DRAW: U=up, D=down,
    # L=left, R=right, E=diag up-right, F=diag down-right, G=diag down-left,
    # H=diag up-left, M=move, A/TA=angle, C=set color, S=scale factor, P=paint,
    # B/N=movement prefixes, x string ;variable = execute substring.
    # ------------------------------------------------------------------ #
    def draw(self, s, interpreter=None, depth=0):
        """Execute a GML command string (manual DRAW).

        Returns the final current graphics position so callers (substring
        execution) can continue from where the substring left off.
        """
        if self.is_text():
            return None
        if depth > 100:
            return self._draw_pos()
        interp = interpreter if interpreter is not None else self._interp
        # The current graphics position: the last point referenced by another
        # GML command, LINE, or PSET; it defaults to the center of the screen
        # (manual DRAW) when nothing has set it yet.
        px, py = self._draw_origin()
        color = self._draw_color
        i = 0
        n = len(s)
        while i < n:
            c = s[i].upper()
            if c.isspace():
                i += 1
                continue
            # Prefix B (move but plot nothing) and N (move but return to the
            # original position when done) may precede a movement command.
            no_plot = False
            nest = False
            if c in 'BN':
                no_plot = (c == 'B')
                nest = (c == 'N')
                i += 1
                while i < n and s[i].isspace():
                    i += 1
                c = s[i].upper() if i < n else ''
            if c in 'UDLREFGH':
                # The command letter is at index i; its numeric argument
                # starts at i + 1.
                dist, i = self._gml_arg(s, i + 1, interp)
                dist = int(round(dist * self._draw_scale))
                # A sets the angle to 0-3 (0=0, 1=90, 2=180, 3=270) and TA
                # adds a turn in degrees; the resulting heading (90-degree
                # steps) rotates the axis-aligned moves (diagonals are fixed).
                rot = int((self._draw_angle * 90 + self._draw_turn) / 90) % 4
                dx, dy = self._draw_dir(c, dist, rot)
                if nest:
                    self._draw_line(px, py, px + dx, py + dy, color, no_plot)
                    # position is unchanged after an N-prefixed move
                else:
                    px, py = self._draw_move(px, py, dx, dy, color, no_plot)
            elif c == 'M':
                x2, y2, i = self._gml_m(s, i + 1, interp)
                if x2[0] in '+-':
                    # Relative M: x2, y2 are offsets added to the position.
                    ox = int(round(float(x2) * self._draw_scale))
                    oy = int(round(float(y2) * self._draw_scale))
                    if nest:
                        self._draw_line(px, py, px + ox, py + oy, color, no_plot)
                    else:
                        px, py = self._draw_move(px, py, ox, oy, color, no_plot)
                else:
                    ax, ay = int(round(float(x2))), int(round(float(y2)))
                    if nest:
                        self._draw_line(px, py, ax, ay, color, no_plot)
                    else:
                        px, py = self._draw_move(px, py, ax - px, ay - py,
                                                  color, no_plot)
            elif c == 'C':
                color, i = self._gml_arg(s, i + 1, interp)
                color = _resolve_color(int(round(color)))
            elif c == 'S':
                sv, i = self._gml_arg(s, i + 1, interp)
                sv = int(round(sv))
                # S sets the scale factor to n/4, clamped to a sensible range
                # so a stray large value cannot stall the interpreter.
                self._draw_scale = max(0.0, min(sv, 4096)) / 4.0
            elif c == 'T' and i + 1 < n and s[i + 1].upper() == 'A':
                tv, i = self._gml_arg(s, i + 2, interp)
                self._draw_turn = float(tv)
            elif c == 'A':
                av, i = self._gml_arg(s, i + 1, interp)
                self._draw_angle = int(round(av)) % 4  # 0-3 (manual DRAW)
            elif c == 'P':
                # P paint,boundary fills the figure between the start and the
                # current position (a line segment); both values are required.
                paint, boundary, i = self._gml_p(s, i + 1, interp)
                paint, boundary = (_resolve_color(int(paint)),
                                   _resolve_color(int(boundary)))
                sx, sy = self._draw_origin()
                self._draw_line(sx, sy, px, py, boundary)
                if paint != boundary:
                    self._draw_line(sx, sy, px, py, paint)
            elif c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' and i + 1 < n and (s[i + 1] == ' ' or s[i + 1].isalpha()):
                # x string ;variable -- execute a substring like a GOSUB.
                varname = self._gml_substring_var(s, i)
                if varname is not None:
                    sub = interp.get_var(varname)
                    subpos = self.draw(str(sub), interp, depth + 1)
                    if subpos is not None:
                        px, py = subpos
                    i = i + 1 + len(varname)
                    while i < n and s[i].isspace():
                        i += 1
            else:
                # Any other character is not a GML command; skip it (the loop
                # always advances, so DRAW can never spin forever).
                i += 1
        self.last_point = (int(round(px)), int(round(py)))
        self._gfx_dirty()
        return self.last_point

    # -- GML helpers --------------------------------------------------------- #
    def _draw_origin(self):
        if self.last_point is not None:
            return self.last_point[0], self.last_point[1]
        return self.cols // 2, self.rows // 2

    def _draw_pos(self):
        if self.last_point is not None:
            return self.last_point
        return (self.cols // 2, self.rows // 2)

    @staticmethod
    def _draw_dir(cmd, dist, rot):
        # Unit direction (screen y grows downward): U=(0,-1), D=(0,1), L=(-1,0),
        # R=(1,0); E/F/G/H are the fixed diagonals.  The axis-aligned commands
        # are rotated by the current angle (A/TA); diagonals are not.
        base = {
            'U': (0, -1), 'D': (0, 1), 'L': (-1, 0), 'R': (1, 0),
            'E': (1, -1), 'F': (1, 1), 'G': (-1, 1), 'H': (-1, -1),
        }[cmd]
        dx, dy = base
        if cmd in 'UDLR':
            for _ in range(int(rot) % 4):
                dx, dy = -dy, dx
        # dist is already the scaled pixel distance; the vector is unit length.
        return dx * dist, dy * dist

    def _draw_move(self, px, py, dx, dy, color, no_plot):
        nx, ny = int(round(px + dx)), int(round(py + dy))
        if not no_plot:
            self.line(int(round(px)), int(round(py)), nx, ny, color)
        return nx, ny

    def _draw_line(self, x1, y1, x2, y2, color, no_plot=False):
        if no_plot:
            return
        x1, y1, x2, y2 = (int(round(v)) for v in (x1, y1, x2, y2))
        if x1 != x2 or y1 != y2:
            self.line(x1, y1, x2, y2, color)
        else:
            self.pset(x1, y1, color)

    def _gml_arg(self, s, i, interp):
        """Read a numeric argument after a GML command: a constant (e.g. 123,
        -5, 2.5, &HFF) or =variable; (a variable reference terminated by a
        semicolon).  Returns (value, new_index)."""
        n = len(s)
        while i < n and s[i].isspace():
            i += 1
        if i < n and s[i] == '=':
            i += 1
            while i < n and s[i].isspace():
                i += 1
            if i < n and s[i] == '&':
                j = i + 2
                while j < n and s[j] in '0123456789abcdefABCDEF':
                    j += 1
                val = int(s[i + 2:j], 16)
                return val, j
            elif i < n and s[i].isdigit():
                j = i
                while j < n and (s[j].isdigit() or s[j] in '.+'):
                    j += 1
                val = float(s[i:j])
            else:
                j = i
                while j < n and (s[j].isalpha() or s[j] in '_%#$'):  # name chars
                    j += 1
                name = s[i:j]
                # The value is taken from the variable; the terminating
                # semicolon is consumed as part of the argument form.
                val = float(interp.get_var(name) or 0)
                i = j
                while i < n and s[i].isspace():
                    i += 1
                if i < n and s[i] == ';':
                    i += 1
                return val, i
            return val, j
        if i < n and s[i] == '&':
            j = i + 2
            while j < n and s[j] in '0123456789abcdefABCDEF':
                j += 1
            return int(s[i + 2:j], 16), j
        start = i
        while i < n and (s[i].isdigit() or s[i] in '.+-'):
            i += 1
        if i == start:
            return 0, i
        text = s[start:i]
        try:
            return float(text) if ('.' in text or text in ('+', '-')) else int(text), i
        except ValueError:
            return 0, i

    def _gml_m(self, s, i, interp):
        """Read the M x,y arguments.  Returns (x_text, y_text, new_index).  The
        text is kept so a leading +/- (relative move) and any =variable form is
        preserved."""
        n = len(s)
        while i < n and s[i].isspace():
            i += 1
        x_text, i = self._gml_scalar(s, i, interp)
        while i < n and s[i].isspace():
            i += 1
        if i < n and s[i] == ',':
            i += 1
        while i < n and s[i].isspace():
            i += 1
        y_text, i = self._gml_scalar(s, i, interp)
        return x_text, y_text, i

    def _gml_scalar(self, s, i, interp):
        """Read one scalar for M x,y (constant, =variable; or +/- constant).
        Returns (text, new_index); the text is converted with float() by the
        caller so a leading sign is preserved."""
        n = len(s)
        if i < n and s[i] == '=':
            i += 1
            while i < n and s[i].isspace():
                i += 1
            j = i
            while j < n and (s[j].isalpha() or s[j] in '_%#$'):
                j += 1
            name = s[i:j]
            val = interp.get_var(name) or 0
            try:
                val = float(val)
            except (TypeError, ValueError):
                val = 0.0
            i = j
            while i < n and s[i].isspace():
                i += 1
            if i < n and s[i] == ';':
                i += 1
            return repr(val), i
        start = i
        while i < n and (s[i].isdigit() or s[i] in '.+-'):
            i += 1
        return (s[start:i] or '0'), i

    def _gml_p(self, s, i, interp):
        """Read the P paint,boundary arguments.  Returns (paint, boundary,
        new_index).  Both values are mandatory (manual DRAW)."""
        n = len(s)
        while i < n and s[i].isspace():
            i += 1
        paint, i = self._gml_num(s, i, interp)
        while i < n and s[i].isspace():
            i += 1
        if i < n and s[i] == ',':
            i += 1
        boundary, i = self._gml_num(s, i, interp)
        return paint, boundary, i

    def _gml_num(self, s, i, interp):
        """Read a number or =variable; reference.  Returns (value, new_index)."""
        n = len(s)
        while i < n and s[i].isspace():
            i += 1
        if i < n and s[i] == '=':
            i += 1
            while i < n and s[i].isspace():
                i += 1
            j = i
            while j < n and (s[j].isalpha() or s[j] in '_%#$'):
                j += 1
            name = s[i:j]
            try:
                val = float(interp.get_var(name) or 0)
            except (TypeError, ValueError):
                val = 0.0
            i = j
            while i < n and s[i].isspace():
                i += 1
            if i < n and s[i] == ';':
                i += 1
            return val, i
        start = i
        while i < n and (s[i].isdigit() or s[i] in '.+-'):
            i += 1
        if i == start:
            return 0, i
        try:
            return float(s[start:i]), i
        except ValueError:
            return 0, i

    def _gml_substring_var(self, s, i):
        """Detect the 'x string ;variable' form (a letter, then a space, then a
        variable name).  Returns the variable name if present, else None."""
        n = len(s)
        j = i + 1
        while j < n and s[j].isspace():
            j += 1
        if j >= n:
            return None
        k = j
        # A BASIC variable name is a letter followed by letters/digits and an
        # optional type suffix ($, %, #, !).
        if not s[j].isalpha():
            return None
        k = j + 1
        while k < n and (s[k].isalnum() or s[k] in '_'):
            k += 1
        if k < n and s[k] in '$%#!':
            k += 1
        return s[j:k]

    # -- rendering ----------------------------------------------------------- #
    def text_dump(self):
        if not self.is_text():
            return ""
        return "\n".join("".join(cell[0] for cell in row) for row in self.grid)

    def flush(self):
        """Render once if a graphics statement marked the screen dirty.

        Called from the run loop after every executed line.  Drawing methods
        only set ``_dirty`` (see _gfx_dirty), so the window updates as a
        single batch instead of redrawing on every pixel."""
        if self._dirty:
            self._dirty = False
            self.render()

    def paint_now(self):
        """Render and paint once, immediately.  Immediate-mode statements
        have no run-loop end-of-line flush to batch with, so a graphics
        statement typed at the Ok prompt (SCREENSIZE, WINDOW, PSET, ...) must
        force its own render + paint to show up right away.  No-op when
        nothing was drawn."""
        if self._dirty:
            self._paint_due = True
            self.flush()

    def pump(self):
        """Process pending GUI events so the window stays live and closable.

        Returns False when the window has been closed, so callers (SLEEP /
        WAIT) can stop the pause early."""
        if self._interrupt:
            # Ctrl+C landed inside a tkinter callback (see _on_configure):
            # deliver it here, at a clean Python boundary, exactly like a
            # console Ctrl+C would be.
            self._interrupt = False
            raise KeyboardInterrupt
        if self.virtual or self._root is None:
            return True
        try:
            if not self._root.winfo_exists():
                return False
            if self._close_pending:
                # The user closed the window (ESC / close box) while no
                # program was running.  Destroy it now: we are in plain
                # Python code in the caller (the REPL prompt loop, SLEEP or
                # SETFPS pacing), not inside the window's own event
                # callback, so this cannot corrupt Tcl's dispatch state.
                self._close_pending = False
                self.close()
                return True
            self._root.update()
            # The update() call above may have processed a pending <Escape>
            # or close-box event, whose handler (_on_escape) set
            # _close_pending.  Re-check it here so the window is destroyed in
            # this same pump() call rather than waiting for the next one:
            # the ESC key was already consumed by the window's binding (it is
            # not delivered to the key queue), so if we do not act on it now
            # the user has to press ESC a second time and the window appears
            # unresponsive (see _prompt_readline / IoDevice.read_key).
            if self._close_pending:
                self._close_pending = False
                self.close()
            return True
        except Exception:
            # The window was closed/destroyed (e.g. the user clicked X while
            # the program was mid-paint).  Stop the pause so the program
            # exits cleanly instead of raising a TclError.
            return False

    def set_fps(self, x):
        """SETFPS x: cap the graphics window at x frames per second, or UNLIMITED.

        The default (no SETFPS executed yet) is UNLIMITED: the program runs
        as fast as it can blit, with no pacing.  SETFPS n sets the cap to n
        for any positive integer n (rounded to an integer; there is no upper
        clamp - the ceiling is as high as you like).  SETFPS UNLIMITED (or 0
        / a negative value) clears the cap back to the default.

        The cap is a ceiling, never a floor: it only throttles a program that
        would otherwise run faster than n fps (see _pace_fps).  A value high
        enough that the program can't reach it is effectively unlimited (the
        window simply paints as fast as it can).  The cap is stored on the
        screen and survives between runs (it is not reset by reset_state);
        UNLIMITED is the only way to clear it back to the default.  Returns
        the fps that was set, or None for unlimited."""
        if isinstance(x, str):
            if x.strip().upper() in ('UNLIMITED', 'INF', 'INFINITY', 'NONE', '0'):
                self._fps_target = None
                self._fps_base = None
                self._fps_count = 0
                return None
            raise BasicError("Illegal quantity")
        try:
            x = int(round(x))
        except (TypeError, ValueError):
            x = 1
        if x <= 0:
            # SETFPS 0 (or a negative value): remove the cap (unlimited).
            self._fps_target = None
            self._fps_base = None
            self._fps_count = 0
            return None
        # No upper clamp: the cap is whatever positive value was requested.
        self._fps_target = x
        # Reset the pacing baseline so the first paced blit after a SETFPS
        # starts fresh instead of waiting on a stale interval.
        self._fps_base = None
        self._fps_count = 0
        return x

    def _pace_fps(self):
        """Throttle graphics blits to the SETFPS cap (a ceiling, not a floor).

        Called once per graphics blit from render(), after the window has
        actually been repainted.  No-op when no cap is set (the default is
        unlimited, i.e. _fps_target is None) or the screen is virtual.

        ``_fps_base`` is the start time of the current paced burst and
        ``_fps_count`` how many blits have run since then.  Each call allows
        ``_fps_count + 1`` blits to have taken at most
        ``(_fps_count + 1) / target`` seconds since the base; if the program
        is running faster than the cap it sleeps (in small slices that pump
        the GUI, mirroring Interpreter._sleep_seconds, so the window stays
        live and closable, and Ctrl+C stops the program exactly as during
        SLEEP) until that budget is used up.  If the program is already at or
        below the cap the budget is never reached and no sleep happens.

        Crucially this makes the cap a pure ceiling: a high value (e.g.
        SETFPS 1000) that the program can't reach causes no pacing at all,
        so it runs as fast as it can - a higher SETFPS is never slower than a
        lower one.  A low value (e.g. SETFPS 30) throttles a fast program
        down to 30 fps.  ``_fps_base``/``_fps_count`` reset in set_fps and
        reset_state so each run starts with a clean baseline.
        """
        target = self._fps_target
        if target is None:
            return
        now = time.time()
        if self._fps_base is None:
            self._fps_base = now
            self._fps_count = 0
            self._fps_count += 1
            return
        allowed = (self._fps_count + 1) / target
        while now + 1e-6 < self._fps_base + allowed:
            if self._stop_requested:
                self._stop_requested = False
                raise KeyboardInterrupt
            if not self.pump():
                break  # window closed during the pause
            time.sleep(0.005)
            now = time.time()
        self._fps_count += 1

    def render(self):
        # Lazily build the window the first time graphics are drawn, then
        # bail out if we are virtual (headless) or have no canvas.
        self._ensure_gui()
        if self.virtual or self._canvas is None:
            return
        # The window may have been closed (user clicked X) since the last
        # render; winfo_exists() raises TclError once destroyed, so treat a
        # gone window as "stop painting" instead of crashing the program.
        try:
            if not self._root.winfo_exists():
                self._dirty = False
                return
        except Exception:
            self._dirty = False
            return
        self._dirty = False
        import tkinter as tk
        cv = self._canvas
        gfx = not self.is_text()
        if gfx:
            self._render_gfx(cv)
        else:
            cv.delete("all")
            self._render_text(cv)
        # Paint the window only when it is due (see _paint_due).  _render_gfx /
        # _render_text have already updated the canvas item cheaply; forcing
        # cv.update() runs a full Tk event-loop cycle, so doing it on every
        # line (the run loop flushes after each line) made clear-and-redraw
        # animations crawl.  Coalescing to once per loop iteration (end of the
        # frame's GOTO back-edge) keeps the animation smooth while still
        # painting at least once per frame.  A render() called outside the run
        # loop (SLEEP / WAIT / direct) has _paint_due set, so it paints.
        paint_due = self._paint_due
        self._paint_due = False
        if paint_due:
            try:
                cv.update_idletasks()
                cv.update()
            except Exception:
                pass
            else:
                # The window has just painted, so it is mapped and a Win32
                # SetForegroundWindow will actually stick: give it the keyboard
                # focus once (see _maybe_focus_window) so the user does not have
                # to click it.  Runs at most once per window, so it never
                # re-grabs focus on later repaints (which would flicker).
                self._maybe_focus_window()
                # The blit succeeded: pace graphics blits to the SETFPS target
                # (a no-op unless SETFPS has been executed; see _pace_fps).
                if gfx:
                    self._pace_fps()

    def _display_body(self, buf, w, h, records):
        """Build the raw PPM body (w*h 3-byte RGB) for the window display.

        The base is the 16-color pixel buffer (the capture model), built in
        one vectorized pass (each palette entry is a 3-byte chunk;
        extend() copies it whole).  The text page cells (records:
        (x0, y0, cell, ch, fg, bg, angle) - see _print_gfx_char / _render_text)
        are then re-composited from the font's anti-aliased coverage
        (_cov_cache): each pixel is blended from the cell background toward
        the foreground color, giving the window the same smooth grayscale
        text the OS font engine gives console text.  The pixel buffer itself
        is never touched - it keeps the crisp 2-color glyphs, so GET
        captures exactly what the old monitor showed.  Records without
        coverage (FONT_8X8 bitmap path) are left as the buffer shows them:
        the bitmap is already crisp at that size."""
        body = bytearray()
        extend = body.extend
        # LUTs extended with the dynamic RGB() colors: the buffer holds
        # color INDEXES (0-15 fixed palette, 16+ dynamic), so the single
        # concatenated LUT maps every stored index to real RGB in one
        # lookup per pixel (see _rgb_alloc / _resolve_color).
        rgb = PALETTE_RGB3 + DYN_RGB3
        pal = PALETTE + [tuple(b) for b in DYN_RGB3]
        pal_n = len(pal)
        for y in range(h):
            row = buf[y]
            for x in range(w):
                extend(rgb[row[x]])
        cov_cache = self._cov_cache
        for (x0, y0, c, ch, fgc, bgc, ang) in records:
            cov = cov_cache.get((c, ch, ang))
            if cov is None:
                continue
            # Records carry resolved indexes; fall back to the % 16 wrap
            # for a stale record that predates the index's palette entry.
            fr, fg2, fb = pal[fgc] if fgc < pal_n else pal[fgc % 16]
            br, bg2, bb = pal[bgc] if bgc < pal_n else pal[bgc % 16]
            dx0, dx1 = max(0, x0), min(w, x0 + c)
            dy0, dy1 = max(0, y0), min(h, y0 + c)
            for dy in range(dy0, dy1):
                base = (dy * w + dx0) * 3
                cbase = (dy - y0) * c
                for dx in range(dx0, dx1):
                    v = cov[cbase + (dx - x0)]
                    if v:
                        o = base + (dx - dx0) * 3
                        body[o] = br + (fr - br) * v // 255
                        body[o + 1] = bg2 + (fg2 - bg2) * v // 255
                        body[o + 2] = bb + (fb - bb) * v // 255
        return body

    def _photoimage_from_buf(self, buf, w, h, records=None):
        """Build a Tk PhotoImage from a pixel buffer (a w x h list of rows
        of color indices) as a single raw PPM (the fast path shared by the
        graphics blit and the text-mode renderer).  When records are given
        (text page cells), their characters are composited with grayscale
        anti-aliasing (see _display_body); otherwise the plain 16-color
        buffer is shown."""
        import tkinter as tk
        body = self._display_body(buf, w, h, records or [])
        # Explicit master: without it, PhotoImage binds to tkinter's
        # process-global default root (the FIRST window created in this
        # process), which breaks rendering of any later graphics window.
        return tk.PhotoImage(
            master=self._root,
            data="P6\n%d %d\n255\n%s" % (w, h, body.decode('latin1')))

    def _render_text(self, cv):
        import tkinter as tk
        # Monitor model: square character cells (self.cell x self.cell
        # pixels; 8x8 by default, so a 40x25 text screen is exactly 320x200 -
        # the old CGA/EGA monitor, see _blit_glyph).  The grid is composited
        # into a scratch pixel buffer and shown as one image (a text screen
        # is quiet, so a full-frame image is cheap and keeps this path
        # independent of the graphics blit state).
        cell = self.cell
        pw, ph = self.cols * cell, self.rows * cell
        buf = [[0] * pw for _ in range(ph)]
        records = []  # for the display's anti-aliased text (see _display_body)
        for r in range(self.rows):
            for c in range(self.cols):
                ch, fg, bg = self.grid[r][c]
                self._blit_glyph(buf, pw, ph, ch, c * cell, r * cell,
                                 fg % 16, bg % 16)
                # _blit_glyph already ran _glyph_mask for this (cell, ch), so
                # this is a cache hit: the character only gets a display
                # record when it was drawn from the (anti-aliased) font.
                if ch != ' ' and self._glyph_mask(ch, cell) is not None:
                    records.append((c * cell, r * cell, cell, ch,
                                    fg % 16, bg % 16,
                                    self.text_rotate % 360))
        cv.config(width=pw, height=ph)
        try:
            img = self._photoimage_from_buf(buf, pw, ph, records)
        except Exception:
            # Tk build without PPM data support: one put() per pixel.  Rare.
            img = tk.PhotoImage(master=self._root, width=pw, height=ph)
            hexc = PALETTE_HEX
            for y in range(ph):
                row = buf[y]
                for x in range(pw):
                    img.put(hexc[row[x] % 16], (x, y))
        self._text_img = img
        cv.create_image(0, 0, image=img, anchor="nw")

    def _render_gfx(self, cv):
        """Blit the graphics buffer to the window.

        Incremental blit: the PhotoImage is created once per window size as
        an opaque black base and is never rebuilt while the size is stable.
        Each frame we only ``put()`` the pixels that actually changed since
        the last blit, so per-frame cost scales with the number of pixels
        drawn this line -- not with the total window area.  That makes a
        700x500 window animate just as smoothly as a 320x200 one.

        A full-frame blit (every pixel) is required only when the buffer is
        replaced wholesale: a size change, a live window resize, CLS, SCREEN,
        or the window being (re)created.  Those are infrequent and the
        animation loop does not run them per frame, so they do not affect
        steady-state speed.  On a resize the existing image is grown or
        cropped in place (image.configure) so the on-screen content is
        preserved rather than rebuilt from scratch."""
        import tkinter as tk
        w, h = self.cols, self.rows
        # Fullscreen: the OS window already fills the screen (see
        # _init_gui).  Do NOT resize the canvas to the (placeholder) buffer
        # here -- that would shrink the window back to 1x1.  The <Configure>
        # handler (see _on_configure / _resize_buf) keeps the canvas and the
        # drawing surface matched to the live window size, so XSZ()/YSZ()
        # report the real screen dimensions.
        if not self._fullscreen:
            cv.config(width=w, height=h)
        buf = self.pixels
        img = self._img

        # Decide whether to blit the whole frame or just the changed pixels.
        full = self._dirty_full
        # Rebuild the base image when there is no image yet or the window size
        # has changed.  _snap is stored as (w, h, buffer); the first two
        # elements are the last-rendered dimensions.
        if self._img is None or self._snap is None or self._snap[:2] != (w, h):
            full = True
        if full and self._dirty_pts:
            # A full reset superseded any points drawn after it; drop them.
            self._dirty_pts = set()

        # Size changed but the image still exists (a live window resize):
        # grow or crop it in place so the existing pixels are preserved and
        # the newly exposed area is filled with black (the background).  This
        # avoids rebuilding the whole image from a PPM.
        if self._img is not None and self._snap is not None and self._snap[:2] != (w, h):
            try:
                self._img.configure(width=w, height=h)
                cv.config(width=w, height=h)
                cv.itemconfig(self._img_item, image=self._img)
                self._snap = (w, h, [row[:] for row in buf])
                self._dirty_full = False
                self._dirty_pts = set()
                return
            except Exception:
                # In-place resize failed (rare); fall through to rebuild.
                self._snap = None

        # (Re)build the opaque base image on a full blit (or first render).
        if full or self._img is None:
            self._rebuild_img(cv, buf, w, h)
            return

        # Incremental blit: put only the pixels that differ from the last
        # blit.  Changed pixels are tracked as they are drawn (see _plot_pt /
        # pset / preset).  If there are none but something was marked dirty
        # (e.g. a whole-buffer change that was not flagged), fall back to a
        # full diff so nothing is missed.
        changed = self._dirty_pts
        if not changed:
            changed = self._diff(buf, self._snap[2], w, h)
            if not changed:
                # Nothing actually changed; leave the image as-is.
                return
        # Dirty points are encoded as single ints (y*cols+x) to avoid a
        # (x, y) tuple per plotted pixel; decode them to (x, y) for the blit.
        colw = self.cols
        changed = [(p % colw, p // colw) for p in changed]
        # A flood of changed pixels (e.g. a large LINE ... BF fill marks
        # ~1M points) would mean hundreds of thousands of individual
        # PhotoImage.put() Tcl calls (~25us each: a 1M-pixel fill took over
        # 20s and appeared to freeze the window).  Rebuilding the whole
        # image from the buffer (a single PPM parse in C) is faster once the
        # change count is large.
        if len(changed) > max(1024, (w * h) // 256):
            self._rebuild_img(cv, buf, w, h)
            return
        # Extended LUTs: buffer indexes are 0-15 (fixed palette) or 16+
        # (dynamic RGB() colors); one concatenated LUT covers both.
        hexc = PALETTE_HEX + DYN_HEX
        pal = PALETTE + [tuple(b) for b in DYN_RGB3]
        pal_n = len(pal)
        if self._gfx_text:
            # Points inside a text page cell are put in the anti-aliased
            # blend color (see _display_body), not the 2-color buffer value,
            # so incremental updates keep the smooth text.
            cov_cache = self._cov_cache
            for (x, y) in changed:
                color = hexc[buf[y][x]]
                for (x0, y0, c, ch, fgc, bgc, ang) in reversed(self._gfx_text):
                    if x0 <= x < x0 + c and y0 <= y < y0 + c:
                        cov = cov_cache.get((c, ch, ang))
                        if cov is not None:
                            v = cov[(y - y0) * c + (x - x0)]
                            if v:
                                fr, fg2, fb = pal[fgc] if fgc < pal_n else pal[fgc % 16]
                                br, bg2, bb = pal[bgc] if bgc < pal_n else pal[bgc % 16]
                                color = '#%02x%02x%02x' % (
                                    br + (fr - br) * v // 255,
                                    bg2 + (fg2 - bg2) * v // 255,
                                    bb + (fb - bb) * v // 255)
                        break
                img.put(color, (x, y))
        else:
            for (x, y) in changed:
                img.put(hexc[buf[y][x]], (x, y))
        cv.itemconfig(self._img_item, image=img)
        self._snap = (w, h, [row[:] for row in buf])
        self._dirty_full = False
        self._dirty_pts = set()

    def _rebuild_img(self, cv, buf, w, h):
        """(Re)build the opaque base image from the whole buffer.

        Used on a full blit (first render, CLS, resize) and as a fallback
        when the incremental change set is large (see _render_gfx).  The
        text page records are composited anti-aliased into the image (see
        _display_body), so a full rebuild never loses the smooth text."""
        import tkinter as tk
        try:
            img = self._photoimage_from_buf(buf, w, h, self._gfx_text)
        except Exception:
            # Tk build without PPM data support: an opaque base built the
            # slow way (one put() per pixel).  Rare.
            img = tk.PhotoImage(master=self._root, width=w, height=h)
            hexc = PALETTE_HEX + DYN_HEX
            for y in range(h):
                row = buf[y]
                for x in range(w):
                    img.put(hexc[row[x]], (x, y))
        cv.delete("all")
        self._img_item = cv.create_image(0, 0, image=img, anchor="nw")
        self._img = img
        self._snap = (w, h, [row[:] for row in buf])
        self._dirty_full = False
        self._dirty_pts = set()

    @staticmethod
    def _diff(cur, prev, w, h):
        """Return the set of changed points, encoded as ints (y*w+x) to match
        _dirty_pts, whose color index differs between the current and previous
        buffers.  Used as a safety net when a full buffer change was not
        explicitly flagged.  O(w*h) -- only taken on rare, infrequent paths,
        never per animation frame."""
        out = set()
        for y in range(h):
            rc = cur[y]
            rp = prev[y]
            base = y * w
            for x in range(w):
                if rc[x] != rp[x]:
                    out.add(base + x)
        return out


# #############################################################################
# System operations (from gw_system.py)
# #############################################################################

class System:
    def __init__(self):
        self.memory = bytearray(65536)
        # Initial default segment: GW-BASIC's data segment (DS), 0 in this
        # implementation (manual DEFSEG: a bare DEF SEG restores this).
        self.initial_segment = 0
        self.segment = self.initial_segment
        self._var_addrs = {}
        self._next_addr = 0x100
        self.timer_start = time.time()
        self.key_events = []  # pending key events: {'ch','token','scan','mask'}
        self._screen = None  # back-reference (set by the Interpreter): the
                             # graphics window's keyboard feeds this queue
                             # too (see pump_key_events / get)
        self.key_enabled = True
        self.env = dict(os.environ)
        self._env_order = list(self.env.keys())
        self.port_regs = {}
        self._stdin_buf = []
        self.sound_freq = None
        self.sound_end = None
        # Real tone playback (SOUND) through the Windows sound driver
        # (winsound), in a background daemon thread so BASIC stays
        # responsive: _spq holds queued (freq, ms, epoch) segments; _sp_epoch
        # is bumped by stop_speaker() to supersede pending (and infinite)
        # segments.  _winsound is None off Windows, where sound falls back
        # to the simulated state + terminal bell.
        self._winsound = None
        try:
            import winsound
            self._winsound = winsound
        except ImportError:
            pass
        # Real music playback (MUSICFILE/PLAYMUSIC) through WinMM MCI
        # (mciSendStringA): PlaySound(SND_FILENAME) does not play WMA
        # files (silent failure), so every format (.wav/.mp3/.wma)
        # goes through explicit MCI.  _winmm is None off Windows, where
        # the playback is simulated like SOUND.
        self._winmm = None
        self._mci_music_open = 0
        self.music_volume = 100
        self._mci_music_vol_max = 0
        if self._winsound is not None:
            try:
                import ctypes
                self._winmm = ctypes.windll.winmm
            except Exception:
                pass
        self._spq = queue.Queue()
        self._sp_epoch = 0
        self._sp_thread = None

    # -- memory -------------------------------------------------------------- #
    def varptr(self, name, value):
        """Return a stable simulated address for a variable."""
        if name not in self._var_addrs:
            self._var_addrs[name] = self._next_addr
            self._next_addr += 8
        return self._var_addrs[name]

    def _seg_addr(self, offset):
        """Physical address for an offset into the current DEF SEG segment."""
        offset = int(offset)
        if offset < 0 or offset > 0xFFFF:
            raise BasicError("Illegal function call")
        return (self.segment * 16 + offset) & 0xFFFF

    def peer(self, addr, val=None):
        addr = self._seg_addr(addr)
        if val is None:
            return self.memory[addr]
        self.memory[addr] = int(val) & 0xFF
        return self.memory[addr]

    def peer_word(self, addr):
        """PEER(a): read a signed 16-bit word (little-endian) at the offset.

        The word-sized sibling of PEEK (8086 memory order: the byte at a is
        the low order byte).  a is the offset (0..65535) into the current
        DEF SEG segment, so a word at the segment's end wraps within the
        segment.  The result's range is -32768..32767.
        """
        lo = self._seg_addr(addr)
        hi = (lo + 1) & 0xFFFF
        word = self.memory[lo] | (self.memory[hi] << 8)
        if word >= 0x8000:
            word -= 0x10000
        return word

    def poke(self, addr, val):
        """POKE a,b (manual POKE): write one byte into a memory location.

        a is the offset (0..65535) into the current DEF SEG segment and b
        the byte to store (0..255); a value outside its range is an
        "Illegal function call" (unlike PEER, POKE range-checks both
        arguments).  Complementary to PEEK (peer)."""
        addr = int(addr)
        if addr < 0 or addr > 0xFFFF:
            raise BasicError("Illegal function call")
        val = int(val)
        if val < 0 or val > 0xFF:
            raise BasicError("Illegal function call")
        self.memory[self._seg_addr(addr)] = val
        return val

    def store_value(self, addr, value):
        """Store a value's bytes at addr so PEER(VARPTR(x)) is meaningful.

        Numbers are stored as little-endian IEEE-754 single precision (as in
        GW-BASIC); strings as a length byte followed by up to 7 characters.
        """
        import struct
        addr = int(addr) & 0xFFFF
        if isinstance(value, str):
            data = bytes([len(value) & 0xFF]) + value.encode('latin-1', errors='replace')[:7]
        else:
            try:
                data = struct.pack('<f', float(value))
            except (OverflowError, ValueError):
                data = struct.pack('<f', 0.0)
        for i, b in enumerate(data):
            self.memory[(addr + i) & 0xFFFF] = b

    def fcb_addr(self, filenum):
        """Simulated FCB address for a file number (VARPTR(#n))."""
        return (0x80 + int(filenum) * 16) & 0xFFFF

    def out(self, port, val):
        # Simulated hardware port write (no real hardware).
        port = int(port)
        val = int(val)
        if port < 0 or port > 0xFFFF:
            raise BasicError("Illegal function call")
        if val < 0 or val > 0xFF:
            raise BasicError("Illegal function call")
        self.port_regs[port] = val & 0xFF
        return None

    def inp(self, port):
        # Simulated hardware port read: returns the last value written by OUT.
        port = int(port)
        if port < 0 or port > 0xFFFF:
            raise BasicError("Illegal function call")
        return self.port_regs.get(port, 0)

    def sound(self, freq, duration):
        """SOUND freq,duration (manual SOUND): speaker state + real audio.

        freq is 37..32767 Hz; duration is 0..65535 clock ticks (18.2 per
        second).  duration 0 turns any active sound off (no effect if none
        is running); 0 < duration < 0.022 sounds infinitely until the next
        SOUND; otherwise the sound lasts duration/18.2 seconds.  Returns
        True when an audible tone starts (freq 32767 is the manual's
        "silence" frequency, above the speaker range).

        On Windows the tone is played for real through the Windows sound
        driver (winsound, a square wave like the PC speaker) by a
        background thread, so the statement never blocks the program.
        Off-Windows the playback is simulated (state only) and the caller
        approximates a starting tone with the terminal bell.
        """
        freq = int(freq)
        if freq < 37 or freq > 32767:
            raise BasicError("Illegal function call")
        duration = float(duration)
        if duration < 0 or duration > 65535:
            raise BasicError("Illegal function call")
        if duration == 0:
            self.sound_freq = None
            self.sound_end = None
            self.stop_speaker()
            return False
        self.sound_freq = freq
        if duration < 0.022:
            self.sound_end = None  # infinite until the next SOUND/PLAY
            self._play_tone(freq, -1)
        else:
            self.sound_end = time.time() + duration / 18.2
            self._play_tone(freq, duration / 18.2 * 1000)
        return freq != 32767

    # -- real tone playback (Windows sound driver via winsound) -------------- #
    def _play_tone(self, freq, ms):
        """Queue a tone segment for the background speaker thread.

        freq 32767 is the manual's silence frequency and is played as dead
        air (the speaker is gated off for the duration).  ms < 0 means an
        "infinite" tone (duration < .022): it plays until stop_speaker().
        On platforms without winsound this is a no-op (the caller falls
        back to the terminal bell)."""
        if self._winsound is None:
            return
        if self._sp_thread is None or not self._sp_thread.is_alive():
            self._sp_thread = threading.Thread(target=self._speaker_worker,
                                               daemon=True)
            self._sp_thread.start()
        self._spq.put((freq, ms, self._sp_epoch))

    def stop_speaker(self):
        """Stop all sound (SOUND f,0 / program end): bump the epoch so the
        current (possibly infinite) segment is cut off within one playback
        chunk, and drop everything queued."""
        self._sp_epoch += 1
        while True:
            try:
                self._spq.get_nowait()
            except queue.Empty:
                return

    def _speaker_worker(self):
        """Background speaker: plays queued (freq, ms, epoch) segments
        through the Windows sound driver (winsound.Beep -- a square wave,
        the real PC speaker sound).  Runs in a daemon thread so SOUND never
        blocks the program and the process never waits on audio.  Segments
        are played in chunks of at most 200 ms so a stop request takes
        effect quickly and an infinite tone can be interrupted.  A segment
        whose epoch no longer matches was superseded by a stop and is
        dropped."""
        ws = self._winsound
        while True:
            try:
                freq, ms, epoch = self._spq.get(timeout=0.25)
            except queue.Empty:
                continue
            if epoch != self._sp_epoch:
                continue
            if ms < 0:
                # Infinite tone (duration < .022): play until superseded.
                while self._sp_epoch == epoch:
                    if freq == 32767:
                        time.sleep(0.1)
                    else:
                        ws.Beep(freq, 100)
                continue
            left = int(ms)
            while left > 0 and self._sp_epoch == epoch:
                chunk = min(left, 200)
                if freq == 32767:
                    time.sleep(chunk / 1000)
                else:
                    ws.Beep(freq, chunk)
                left -= chunk

    def music_play(self, path):
        # PLAYMUSIC: play a .wav, .mp3 or .wma file through WinMM MCI
        # (mciSendStringA) -- generic open by extension, non-blocking
        # play (no /WAIT), on its own stream, independent of the SOUND
        # speaker thread.  PlaySound(SND_FILENAME) cannot play WMA
        # (silent failure), so every format goes through explicit MCI.
        # A new call interrupts the music currently playing (one at a
        # time; the previous alias is stopped and closed).  MCI
        # failures are silent, like the old PlaySound path.  Off-Windows
        # this is a no-op (the playback is simulated, like SOUND).
        # Returns True if the audio device is available, False otherwise.
        winmm = self._winmm
        if winmm is None:
            return False
        if self._mci_music_open:
            winmm.mciSendStringA(b'stop gwmusic', None, 0, 0)
            winmm.mciSendStringA(b'close gwmusic', None, 0, 0)
            self._mci_music_open = 0
        cmd = ('open "%s" alias gwmusic' % path).encode('mbcs')
        self._mci_music_open = \
            1 if winmm.mciSendStringA(cmd, None, 0, 0) == 0 else 0
        if self._mci_music_open:
            # A fresh MCI audio device opens at its maximum volume, so
            # the volume read now is the top of the device's own scale
            # (e.g. 1000 for the .mp3/.wma devices -- sending 100 to
            # them would mean 10% loudness).  Devices without volume
            # control (some .wav) report nothing and ignore
            # MUSICVOLUME.
            self._mci_music_vol_max = \
                self._mci_music_query_volume(winmm) or 0
            self._mci_music_apply_device_volume(winmm)
            winmm.mciSendStringA(b'play gwmusic', None, 0, 0)
        return True

    def music_stop(self):
        # STOPMUSIC (and the auto-stop on window close / program end):
        # stop and close the MCI alias music_play opened.  No-op when no
        # music is playing; never raises (MCI failures are silent).
        winmm = self._winmm
        if winmm is None:
            return
        if self._mci_music_open:
            winmm.mciSendStringA(b'stop gwmusic', None, 0, 0)
            winmm.mciSendStringA(b'close gwmusic', None, 0, 0)
            self._mci_music_open = 0

    def _mci_music_query_volume(self, winmm):
        # Read the current volume of the gwmusic device on the
        # device's own scale (e.g. 1000); None when the device does
        # not support the query.
        import ctypes
        buf = ctypes.create_string_buffer(16)
        if winmm.mciSendStringA(b'status gwmusic volume', buf, 16, 0) != 0:
            return None
        try:
            return int(buf.value.decode('ascii'))
        except ValueError:
            return None

    def _mci_music_apply_device_volume(self, winmm):
        # Send the current MUSICVOLUME value (0-100) to the open
        # gwmusic device, scaled to the device's own volume range
        # (discovered at open, _mci_music_vol_max).  No-op when the
        # device has no volume control.
        mx = self._mci_music_vol_max
        if mx <= 0:
            return
        winmm.mciSendStringA(
            ('setaudio gwmusic volume to %d'
             % (mx * self.music_volume // 100)).encode('mbcs'),
            None, 0, 0)

    def music_set_volume(self, n):
        # MUSICVOLUME n: set the music stream volume (0-100, MCI
        # percentage) on the gwmusic device instance.  The system
        # master volume is never touched: the effective level is
        # master x music_volume.  0 is silent but the track keeps
        # playing.  The value is stored and applied to the current
        # stream when music is playing; otherwise it is applied at
        # the next PLAYMUSIC.  Out-of-range / non-numeric values are
        # an error.
        if isinstance(n, bool) or not isinstance(n, (int, float)):
            raise BasicError("Illegal function call")
        v = int(n)
        if v != n or v < 0 or v > 100:
            raise BasicError("Illegal function call")
        self.music_volume = v
        winmm = self._winmm
        if winmm is not None and self._mci_music_open:
            self._mci_music_apply_device_volume(winmm)

    def def_seg(self, n=None):
        if n is None:
            # Manual DEFSEG: "If the address option is omitted, the segment
            # to be used is set to GW-BASIC's data segment (DS). This is
            # the initial default value."
            self.segment = self.initial_segment
        else:
            n = int(n)
            if n < 0 or n > 0xFFFF:
                raise BasicError("Illegal function call")
            self.segment = n
        return self.segment

    def bload(self, filename, mode, start):
        filename = str(filename)
        if start is None:
            start = 0x100
        start = self._seg_addr(start)
        try:
            with open(filename, 'rb') as f:
                data = f.read()
        except OSError as e:
            raise BasicError("File not found (53): %s" % e)
        for i, b in enumerate(data):
            self.memory[(start + i) & 0xFFFF] = b
        return start + len(data)

    def bsave(self, filename, start, length):
        filename = str(filename)
        start = self._seg_addr(start)
        length = int(length)
        if length < 0 or length > 0xFFFF:
            raise BasicError("Illegal function call")
        data = bytes(self.memory[start:start + length])
        with open(filename, 'wb') as f:
            f.write(data)

    # -- keyboard ------------------------------------------------------------ #
    def _modifier_mask(self):
        """Current modifier keys as a GW-BASIC key mask (manual KEY(n)).

        &H01 right SHIFT, &H02 left SHIFT, &H04 CTRL, &H08 ALT, &H20 NUM
        LOCK (latched), &H40 CAPS LOCK (latched), &H80 extended key.
        Windows only; 0 elsewhere (modifier-state matching is then
        unavailable)."""
        if os.name != 'nt':
            return 0
        try:
            import ctypes
            u = ctypes.windll.user32
            m = 0
            if u.GetKeyState(0x11) & 0x80:  # CTRL
                m |= 0x04
            if u.GetKeyState(0x12) & 0x80:  # ALT
                m |= 0x08
            if u.GetKeyState(0xA0) & 0x80:  # left SHIFT
                m |= 0x02
            if u.GetKeyState(0xA1) & 0x80:  # right SHIFT
                m |= 0x01
            if u.GetKeyState(0x14) & 0x01:  # CAPS LOCK (latched)
                m |= 0x40
            if u.GetKeyState(0x90) & 0x01:  # NUM LOCK (latched)
                m |= 0x20
            return m
        except Exception:
            return 0

    def pump_key_events(self):
        """Move all currently-available console keys into key_events,
        non-blocking.  Extended keys carry their scan code and the current
        modifier mask so ON KEY(n) traps (KEY(n),CHR$+CHR$ definitions for
        keys 15-20) can match.  Keys consumed here are the same physical
        presses INKEY$/GET KEY would otherwise read."""
        def add(ch='', token=None, scan=None, mask=0):
            self.key_events.append(
                {'ch': ch, 'token': token, 'scan': scan, 'mask': mask})
        # The graphics window's keyboard feeds the same queue: process its
        # pending events first so keys typed while the window is focused
        # reach the program even inside a tight INKEY$ loop (see
        # Screen._on_window_key / pump_events).  No-op without a window.
        scr = self._screen
        if scr is not None:
            scr.pump_events()
        try:
            import sys
            if sys.stdin is None or not sys.stdin.isatty():
                return
        except Exception:
            return
        try:
            import msvcrt
            while msvcrt.kbhit():
                ch = msvcrt.getch()
                b = ch[0] if isinstance(ch, (bytes, bytearray)) else ord(ch)
                if b in (0xE0, 0x00):
                    # Extended key (arrows/F-keys): read the scan code byte.
                    try:
                        s = msvcrt.getch()
                        scan = (s[0] if isinstance(s, (bytes, bytearray))
                                else ord(s))
                    except Exception:
                        continue
                    token = {0x48: 'up', 0x50: 'down',
                             0x4B: 'left', 0x4D: 'right'}.get(scan)
                    add(token=token, scan=scan,
                        mask=self._modifier_mask() | 0x80)
                else:
                    add(ch=chr(b),
                        token='enter' if b in (0x0D, 0x0A) else None)
            return
        except ImportError:
            pass
        except Exception:
            return
        # Unix fallback: non-blocking single-byte read; escape sequences
        # (arrow keys) are completed with zero-timeout selects.
        try:
            import sys
            import select
            if not select.select([sys.stdin], [], [], 0)[0]:
                return
            data = os.read(sys.stdin.fileno(), 1)
            if not data:
                return
            b = data[0]
            if b == 0x1B:
                fd = sys.stdin.fileno()
                if select.select([fd], [], [], 0)[0]:
                    d2 = os.read(fd, 1)
                    if d2 and d2[0] == ord('['):
                        if select.select([fd], [], [], 0)[0]:
                            d3 = os.read(fd, 1)
                            if d3:
                                tok = {ord('A'): 'up', ord('B'): 'down',
                                       ord('C'): 'right',
                                       ord('D'): 'left'}.get(d3[0])
                                if tok:
                                    add(token=tok, mask=0x80)
                                    return
                add(ch=chr(0x1B))
            elif b in (0x0D, 0x0A):
                add(ch=chr(b), token='enter')
            else:
                add(ch=chr(b))
        except Exception:
            return

    def _next_key_event(self):
        """Pop the next pending key event, pumping the console first."""
        if not self.key_events:
            self.pump_key_events()
        if self.key_events:
            return self.key_events.pop(0)
        return None

    @staticmethod
    def _event_inkey_text(ev):
        """Text INKEY$/GET KEY reports for a pending key event.

        Manual KEY: a redefined function key delivers its assigned string
        one character per INKEY$ call (the expansion is done by the
        interpreter); a disabled function key reports CHR$(0)+CHR$(scan
        code); cursor keys report CHR$(155-158)."""
        ch = ev.get('ch')
        if ch:
            return ch
        token = ev.get('token')
        if token:
            return {'up': chr(158), 'left': chr(155),
                    'right': chr(156), 'down': chr(157)}.get(token, '')
        scan = ev.get('scan')
        if scan is not None:
            return chr(0) + chr(scan)
        return ""

    def inkey(self):
        if not self.key_enabled:
            return ""
        ev = self._next_key_event()
        if ev is None:
            return ""
        return self._event_inkey_text(ev)

    def get(self):
        if not self.key_enabled:
            return ""
        ev = self._next_key_event()
        if ev is not None:
            return self._event_inkey_text(ev)
        scr = self._screen
        if scr is not None and scr._root is not None and not scr.virtual:
            # A window is open: the key may arrive through either keyboard,
            # so poll in small slices (pump_key_events pumps the window and
            # the console) instead of blocking on the console and freezing
            # the window.
            while True:
                ev = self._next_key_event()
                if ev is not None:
                    return self._event_inkey_text(ev)
                if scr._stop_requested:
                    # ESC / close box while blocked waiting for a key: stop
                    # the program exactly like a console Ctrl+C would (see
                    # Screen._on_escape).
                    scr._stop_requested = False
                    raise KeyboardInterrupt
                time.sleep(0.01)
        try:
            import sys
            line = sys.stdin.readline()
            return line[:1] if line else ""
        except Exception:
            return ""

    def key_on(self):
        # KEY ON: show the key display (line 25).  Display-only; tracked.
        self.key_display = True

    def key_off(self):
        # KEY OFF: erase the key display.  Display-only; tracked.
        self.key_display = False

    def push_key(self, ch, token=None, scan=None, mask=0):
        """Queue a key press (test harness; the console pump and F-key
        expansions add the same shape of event)."""
        self.key_events.append({'ch': str(ch), 'token': token,
                                'scan': scan, 'mask': mask})

    # -- timer --------------------------------------------------------------- #
    def timer(self):
        # Elapsed seconds since midnight (float), per the manual.
        now = time.time()
        t = time.localtime(now)
        today_midnight = time.mktime((t.tm_year, t.tm_mon, t.tm_mday,
                                      0, 0, 0, 0, 0, -1))
        return (now - today_midnight) % 86400

    # -- environment --------------------------------------------------------- #
    def _remove_env(self, key):
        self.env.pop(key, None)
        if key in self._env_order:
            self._env_order.remove(key)

    def environ(self, var=None):
        """ENVIRON statement: set or remove a parameter.

        Accepts "parmid=text" or "parmid text" (equal sign OR a blank).
        A null text, or a text of a single semicolon, removes the parameter.
        """
        if var is None:
            return ""
        var = str(var)
        if '=' in var:
            k, v = var.split('=', 1)
            k = k.strip()
            if not k:
                return ""
            if v == '' or v == ';':
                self._remove_env(k)
            else:
                self.env[k] = v
                if k not in self._env_order:
                    self._env_order.append(k)
            return ""
        m = re.match(r'^(\S+)\s+(.*)$', var)
        if m:
            k, v = m.group(1), m.group(2)
            if v == '' or v == ';':
                self._remove_env(k)
            else:
                self.env[k] = v
                if k not in self._env_order:
                    self._env_order.append(k)
            return ""
        # A bare name in the statement form is a no-op (lookups use ENVIRON$).
        return ""

    def environ_get(self, key):
        """ENVIRON$ function: named lookup or numeric nth-parameter lookup."""
        if isinstance(key, (int, float)) and not isinstance(key, bool):
            n = int(key)
            if n < 1 or n > 255:
                raise BasicError("Illegal function call")
            if n > len(self._env_order):
                return ""
            return self.env.get(self._env_order[n - 1], "")
        return self.env.get(str(key), "")

    # -- misc ---------------------------------------------------------------- #
    def fre(self, expr=None):
        # Simulated free memory.
        return 60000

    def now(self):
        t = time.localtime()
        return {
            'DAY': t.tm_mday, 'MONTH': t.tm_mon, 'YEAR': t.tm_year,
            'HOUR': t.tm_hour, 'MINUTE': t.tm_min, 'SECOND': t.tm_sec,
        }


# #############################################################################
# Interpreter core (from gwbasic.py)
# #############################################################################

# --------------------------------------------------------------------------- #
#  Exceptions (used for control flow + errors)
# --------------------------------------------------------------------------- #
class Goto(Exception):
    def __init__(self, line, stmt_idx=0, resuming_from_handler=False):
        self.line = line
        self.stmt_idx = stmt_idx
        self.resuming_from_handler = resuming_from_handler


class Gosub(Exception):
    def __init__(self, line, trap_key=None, resume=None):
        self.line = line
        # Key number of the ON KEY(n) trap that entered this GOSUB, or None
        # for a plain GOSUB.  The RETURN that pops the matching stack entry
        # re-arms the trap's event (manual ON KEY / RETURN).
        self.trap_key = trap_key
        # Set by _exec_actions_seq / _exec_one_action when the GOSUB
        # statement sat inside a single-line IF's THEN/ELSE actions: a
        # list of continuation steps (see _exec_action_steps) a RETURN
        # executes before continuing after the IF.  None otherwise.
        self.resume = resume


class GosubEntry:
    """A gosub_stack entry: where a RETURN resumes - (line, stmt_idx), the
    statement following the GOSUB statement (manual RETURN) - plus, for a
    GOSUB entered by an ON KEY(n) trap, the trapped key whose event the
    RETURN re-arms (None for a plain GOSUB), and, for a GOSUB inside a
    single-line IF's THEN/ELSE actions, the list of continuation steps
    (see _exec_action_steps) a RETURN executes before continuing after
    the IF; if_line is that IF's own line (for ERL / break messages while
    the steps run)."""
    __slots__ = ('line', 'stmt_idx', 'trap_key', 'cont', 'if_line')

    def __init__(self, line, stmt_idx=0, trap_key=None, cont=None,
                 if_line=None):
        self.line = line
        self.stmt_idx = stmt_idx
        self.trap_key = trap_key
        self.cont = cont
        self.if_line = if_line


class Return(Exception):
    def __init__(self, line=None):
        self.line = line


class Stop(Exception):
    pass


class Break(Exception):
    """Raised by STOP. Leaves the program loaded so CONT can resume it.

    action_idx is set by _exec_actions_seq when the STOP sits inside an IF
    action list: the action's index in that list, so CONT can resume the
    remaining actions after the STOP instead of re-running it."""
    def __init__(self, line=None, action_idx=None):
        self.line = line
        self.action_idx = action_idx


class TraceStop(Exception):
    """Raised when execution halts (STOP/break) so the REPL can return to
    the command level with the program left loaded for CONT.
    """
    def __init__(self, line=None):
        self.line = line


# --------------------------------------------------------------------------- #
#  Small helpers
# --------------------------------------------------------------------------- #
def round_single(v):
    """Round a value to the nearest IEEE-754 single-precision float.

    Manual 6.2.4: single-precision numbers occupy 4 bytes, so a value
    stored in a single-precision variable (or computed at single
    precision) is the representable single nearest to it - e.g. 2.04 is
    stored as 2.039999961853027 (manual 6.3 worked example).
    """
    try:
        return struct.unpack('<f', struct.pack('<f', v))[0]
    except (OverflowError, ValueError):
        return v


def classify_number(s):
    """Classify a numeric literal as 'int', 'single', or 'double'.

    Manual 6.1.1: a single-precision constant has seven or fewer digits,
    exponential form using E, or a trailing '!'; a double-precision
    constant has eight or more digits, exponential form using D, or a
    trailing '#'.  A type suffix always wins; the digit count is the
    number of digit characters in the mantissa (the part before the
    exponent marker), so 12345678 is double while 1.09E-06 is single.
    """
    t = s.strip()
    if not t:
        return 'int'
    up = t.upper()
    if up.startswith('&H') or up.startswith('&O'):
        return 'int'
    if t[-1] in '!#%':
        return {'!': 'single', '#': 'double', '%': 'int'}[t[-1]]
    body = t[1:] if t[0] in '+-' else t
    if 'D' in body or 'd' in body:
        return 'double'
    if 'E' in body or 'e' in body:
        mantissa = body.split('E')[0].split('e')[0]
        has_exp = True
    else:
        mantissa = body
        has_exp = False
    if sum(c.isdigit() for c in mantissa) >= 8:
        return 'double'
    if '.' in mantissa or has_exp:
        return 'single'
    return 'int'


def parse_number(s):
    """Parse a numeric literal into int (when whole) or float.

    Supports the &H (hex) and &O (octal) descriptors from the manual.
    Single-precision literals (manual 6.1.1) are rounded to the
    single-precision value they represent (e.g. 2.04 becomes
    2.039999961853027); double-precision literals keep full precision.
    The literal's class is classify_number(s).
    """
    t = s.strip()
    if t.upper().startswith('&H'):
        try:
            return int(t[2:], 16)
        except ValueError:
            raise BasicError("Invalid number: %s" % s)
    if t.upper().startswith('&O'):
        try:
            return int(t[2:], 8)
        except ValueError:
            raise BasicError("Invalid number: %s" % s)
    kind = classify_number(s)
    # Strip a trailing type-declaration suffix (manual 6.1.1): ! (single),
    # # (double), % (integer).
    if t and t[-1] in '!#%':
        t = t[:-1]
    # GW-BASIC allows 'D' as an alternate exponent marker for double-
    # precision floating-point constants (manual 6.1.1), e.g. 3490.0D0.
    t = t.replace('D', 'E').replace('d', 'e')
    try:
        f = float(t)
    except ValueError:
        raise BasicError("Invalid number: %s" % s)
    if math.isinf(f):
        # The constant lies outside the GW-BASIC number format (manual 6.1:
        # floating-point constants run 3.0x10^-39 to 1.7x10^38).  Real
        # GW-BASIC rejects an out-of-range constant with the "Overflow"
        # error (its line compiler's OVERR path), so raise a trappable
        # BasicError (ERR 6) instead of letting int(inf) crash Python with
        # an OverflowError traceback.
        raise BasicError("Overflow")
    if kind == 'single':
        # A single-precision constant holds the single-precision value
        # (manual 6.1.1), not the full double the text would suggest.
        # It is kept as a float, never converted to int: an integral
        # single beyond 24 magnitude bits (e.g. 2.5E10) is not exactly
        # representable, GW-BASIC stores the nearest single, and it must
        # still print in single-precision form - seven significant digits,
        # exponential beyond 1e7 - so 2.5E10 prints 2.50000E+10 (an int
        # would print the bare 24999999488; the unrounded text, the bare
        # 25000000000, is likewise wrong).
        return round_single(f)
    if f == int(f):
        return int(f)
    return f


def parse_number_safe(s):
    """Like parse_number but returns 0 on failure (for VAL)."""
    try:
        return parse_number(s)
    except BasicError:
        return 0


_VAL_RE = re.compile(r'^\s*[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?')


def parse_val(s):
    """GW-BASIC VAL: parse the leading numeric prefix; return 0 if none.

    Leading spaces are skipped; an optional sign, digits, an optional
    decimal point, and an optional exponent are consumed. Parsing stops at
    the first character that cannot be part of a number.
    """
    m = _VAL_RE.match(s)
    if not m:
        return 0
    return parse_number(m.group(0))


def find_instr(haystack, needle):
    """1-based INSTR; returns the position as a number (int), 0 when not found."""
    idx = haystack.find(needle)
    return int(idx + 1) if idx != -1 else 0


# --------------------------------------------------------------------------- #
#  Tokenizer
# --------------------------------------------------------------------------- #
def _tokenize_positions(line):
    """Tokenize a BASIC source line, tracking each token's position.

    Returns a list of (type, value, start, end) tuples where start/end are
    the character offsets of the token within `line`.  This is the single
    source of truth for the lexical rules; tokenize() is a thin wrapper that
    drops the position information.
    """
    tokens = []
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        if c.isspace():
            i += 1
        elif c.isdigit() or (c == '.' and i + 1 < n and line[i + 1].isdigit()):
            j = i
            while j < n and (line[j].isdigit() or line[j] == '.'):
                j += 1
            if j < n and line[j] in 'eEdD':
                # 'E' (single) or 'D' (double, manual 6.1.1) exponent marker.
                j += 1
                if j < n and line[j] in '+-':
                    j += 1
                while j < n and line[j].isdigit():
                    j += 1
            if j < n and line[j] in '!#%':
                # Trailing type-declaration suffix on a numeric literal
                # (manual 6.1.1): ! (single), # (double), % (integer).
                # It may follow a plain mantissa (3490.0#) OR an exponent
                # marker (5E-05#) - in both cases it must be absorbed into
                # the number token itself, otherwise a bare '#' is
                # re-tokenized below as the file-number operator and the
                # literal loses its declared precision (and e.g. "6#/7"
                # would stop after "6").
                j += 1
            tokens.append(('number', line[i:j], i, j))
            i = j
        elif c == '"':
            # A doubled quote ("") inside a literal is a literal quote.
            j = i + 1
            while j < n:
                if line[j] == '"':
                    if j + 1 < n and line[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            if j >= n:
                raise BasicError("Unterminated string")
            tokens.append(('string', line[i + 1:j].replace('""', '"'), i, j + 1))
            i = j + 1
        elif c.isalpha() or c == '_':
            j = i
            while j < n and (line[j].isalnum() or line[j] in '_$!#%'):
                j += 1
            word = line[i:j]
            if word.upper() == 'REM':
                # Everything after REM is a comment to end of line.
                tokens.append(('rem', line[j:], i, n))
                i = n
                continue
            tokens.append(('name', word, i, j))
            i = j
        elif c == "'":
            # An apostrophe starts a remark: identical to REM, everything
            # to the end of the line is a comment (manual REM).
            tokens.append(('rem', line[i + 1:], i, n))
            i = n
            continue
        elif c == '&':
            # &H / &O: hexadecimal / octal numeric descriptor (manual App. I).
            # A bare '&' is the string-concatenation operator.
            if i + 1 < n and line[i + 1] in 'hH':
                j = i + 2
                while j < n and line[j] in '0123456789abcdefABCDEF':
                    j += 1
                if j == i + 2:
                    raise BasicError("Invalid number: &H")
                tokens.append(('number', line[i:j], i, j))
                i = j
            elif i + 1 < n and line[i + 1] in 'oO':
                j = i + 2
                while j < n and line[j] in '01234567':
                    j += 1
                if j == i + 2:
                    raise BasicError("Invalid number: &O")
                tokens.append(('number', line[i:j], i, j))
                i = j
            else:
                tokens.append(('op', '&', i, i + 1))
                i += 1
        elif c in '+-*/^\\?':
            tokens.append(('op', c, i, i + 1))
            i += 1
        elif c == '=':
            tokens.append(('op', '=', i, i + 1))
            i += 1
        elif c == '<':
            if i + 1 < n and line[i + 1] == '=':
                tokens.append(('op', '<=', i, i + 2))
                i += 2
            elif i + 1 < n and line[i + 1] == '>':
                tokens.append(('op', '<>', i, i + 2))
                i += 2
            else:
                tokens.append(('op', '<', i, i + 1))
                i += 1
        elif c == '>':
            if i + 1 < n and line[i + 1] == '=':
                tokens.append(('op', '>=', i, i + 2))
                i += 2
            else:
                tokens.append(('op', '>', i, i + 1))
                i += 1
        elif c in '(),;:#':
            tokens.append(('op', c, i, i + 1))
            i += 1
        else:
            # Unknown character - skip it.
            i += 1
    return tokens


def tokenize(line):
    """Turn a BASIC source line into a list of (type, value) tokens.

    File-channel idiom: the '#' must be separated from the instruction by
    a space and written directly before the file number, i.e. 'PRINT #1'
    and 'INPUT #2, A$'.  Both the fused form ('PRINT#1') and a space
    between '#' and the number ('PRINT # 1') are illegal and are rejected
    here, at the only point where a file-channel '#' can be told apart
    from a double-precision type suffix (a '#' fused into a name token).
    """
    toks = _tokenize_positions(line)
    # (a) Fused 'KEYWORD#...' names: the lexer fuses a '#' written directly
    #     after a word into that name token (e.g. 'PRINT#1', 'INPUT#').  For
    #     a file instruction this is the illegal fused form, so reject it.
    #     Only name tokens that start a statement (start of line, after a
    #     ':' separator, after THEN/ELSE, or the second word of 'LINE
    #     INPUT') are checked, and only when the part before the '#' is a
    #     file-instruction keyword: other '#'-suffixed names are legal
    #     double-precision variables (e.g. A#), and a type suffix is never
    #     followed by a digit.
    for _i, _tok in enumerate(toks):
        if _tok[0] != 'name':
            continue
        if _i > 0:
            _prev = toks[_i - 1]
            _at_stmt_start = (
                (_prev[0] == 'op' and _prev[1] == ':') or
                (_prev[0] == 'name' and _prev[1].upper() in
                 ('THEN', 'ELSE', 'LINE')))
        else:
            _at_stmt_start = True
        if not _at_stmt_start:
            continue
        _t, word, _s, _e = _tok
        _k = word.rfind('#')
        if (_k > 0 and word[:_k].upper() in
                ('PRINT', 'INPUT', 'WRITE', 'OPEN', 'CLOSE',
                 'GET', 'PUT', 'SEEK')):
            raise BasicError("Expected a space before '#' (e.g. PRINT #1)")
    # (b) A standalone '#' must be written directly before the file number:
    #     no space is allowed between '#' and the number ('PRINT #1' is
    #     legal, 'PRINT # 1' is not).  The file number may be a literal or
    #     a variable, so the next source character must be a digit or a
    #     letter (or '_', the legal name-initializer).
    for _t, _v, _s, _e in toks:
        if _t == 'op' and _v == '#':
            if (_e >= len(line)
                    or not (line[_e].isdigit() or line[_e].isalpha()
                            or line[_e] == '_')):
                raise BasicError("Expected file number after '#'")
    return [(t[0], t[1]) for t in toks]


def format_tokens(tokens):
    """Render a token list in a readable single-line form (TOKEN command)."""
    parts = []
    for ttype, value in tokens:
        if ttype == 'string':
            value = '"%s"' % value
        parts.append("%s %s" % (ttype, value))
    if not parts:
        return "(no tokens)"
    return " | ".join(parts)


# --------------------------------------------------------------------------- #
#  RENUM helpers
# --------------------------------------------------------------------------- #
def _renum_stmt(stmt, line_map):
    """Return a copy of an AST statement with line references remapped.

    `line_map` maps old line numbers to new ones.  A reference to a line
    that is not in the map (e.g. a line outside the renumbered range, or a
    dangling GOTO) is left unchanged.  Statements that carry no line
    references are returned as-is.
    """
    tag = stmt[0]
    if tag in ('goto', 'gosub'):
        return (tag, line_map.get(stmt[1], stmt[1]))
    if tag == 'if':
        cond = stmt[1]
        then_actions = stmt[2]
        else_actions = stmt[3]
        new_then = _renum_actions(then_actions, line_map)
        new_else = (_renum_actions(else_actions, line_map)
                    if else_actions is not None else None)
        return ('if', cond, new_then, new_else)
    if tag == 'else':
        action = stmt[1]
        if action is None:
            return stmt
        if action[0] == 'goto':
            return ('else', ('goto', line_map.get(action[1], action[1])))
        if action[0] == 'stmt':
            return ('else', ('stmt', _renum_stmt(action[1], line_map)))
        return stmt
    if tag in ('on_goto', 'on_gosub'):
        return (tag, stmt[1], [line_map.get(x, x) for x in stmt[2]])
    if tag in ('restore', 'resume'):
        # RESTORE n / RESUME n line references (manual RENUM).
        if stmt[1] is None:
            return stmt
        return (tag, line_map.get(stmt[1], stmt[1]))
    if tag == 'on_error':
        if stmt[1] is None:
            return stmt
        return ('on_error', line_map.get(stmt[1], stmt[1]))
    if tag == 'on_key':
        target = stmt[2]
        if isinstance(target, tuple):
            return ('on_key', stmt[1],
                    (target[0], line_map.get(target[1], target[1])))
        return stmt
    if tag == 'on_timer':
        if isinstance(stmt[2], int):
            return (tag, stmt[1], line_map.get(stmt[2], stmt[2]))
        return stmt
    return stmt


def _renum_actions(actions, line_map):
    """Remap the line references in an IF...THEN/ELSE action list."""
    new = []
    for a in actions:
        if a[0] == 'goto':
            new.append(('goto', line_map.get(a[1], a[1])))
        elif a[0] == 'stmt':
            new.append(('stmt', _renum_stmt(a[1], line_map)))
        else:
            new.append(a)  # ('fall',)
    return new


def _renum_source(text, line_map):
    """Rewrite line-number references in a source line's text.

    Only numbers that are line references are changed; numbers in
    expressions, DATA items, file numbers, and inside string literals or
    REM/' comments are left untouched.  The original formatting of every
    other character is preserved.

    A number is a line reference when it immediately follows a GOTO,
    GOSUB, RESTORE, or RESUME keyword (all such numbers up to the next ':'
    or end of line, which covers GOTO n, GOSUB n, ON ... GOTO n1,n2,...,
    ON ERROR/KEY/TIMER GOTO n, RESTORE n, RESUME n) or when it is the
    single number immediately after THEN or ELSE (IF ... THEN n / ELSE n /
    ELSE GOTO n).
    """
    try:
        tokens = _tokenize_positions(text)
    except BasicError:
        return text
    edits = []
    i = 0
    n = len(tokens)
    while i < n:
        ttype, value, start, end = tokens[i]
        if ttype == 'name':
            kw = value.upper()
            if kw in ('GOTO', 'GOSUB', 'RESTORE', 'RESUME'):
                j = i + 1
                while j < n:
                    tt, vv, ss, ee = tokens[j]
                    if tt == 'op' and vv == ':':
                        break
                    if tt == 'number':
                        edit = _line_ref_edit(vv, ss, ee, line_map)
                        if edit is not None:
                            edits.append(edit)
                    j += 1
                i = j
                continue
            if kw in ('THEN', 'ELSE'):
                if i + 1 < n and tokens[i + 1][0] == 'number':
                    tt, vv, ss, ee = tokens[i + 1]
                    edit = _line_ref_edit(vv, ss, ee, line_map)
                    if edit is not None:
                        edits.append(edit)
                i += 1
                continue
        i += 1
    if not edits:
        return text
    # Apply right-to-left so earlier offsets remain valid.
    result = text
    for ss, ee, newtext in sorted(edits, key=lambda e: e[0], reverse=True):
        result = result[:ss] + newtext + result[ee:]
    return result


def _line_ref_edit(numtext, start, end, line_map):
    """Build a (start, end, newtext) edit for a line-reference number, or None."""
    try:
        val = int(numtext)
    except ValueError:
        return None
    newval = line_map.get(val)
    if newval is None or newval == val:
        return None
    return (start, end, str(newval))


def _parse_renum_args(argstr):
    """Parse the arguments of a RENUM command.

    Syntax (per the GW-BASIC manual): RENUM [new number],[old number][,increment]
      new number - first line number of the new sequence (default 10)
      old number - the line where renumbering begins (default: first line)
      increment  - increment of the new sequence (default 10)
    Fields may be left empty, e.g. RENUM 300,,50.  Returns (new, old, inc)
    where old is None when the whole program is renumbered.
    """
    argstr = argstr.strip()
    if not argstr:
        return 10, None, 10
    parts = argstr.split(',')
    if len(parts) > 3:
        raise ValueError("Too many arguments")
    while len(parts) < 3:
        parts.append('')
    new_s, old_s, inc_s = (p.strip() for p in parts)
    if new_s and not new_s.isdigit():
        raise ValueError("Invalid new number '%s'" % new_s)
    if old_s and not old_s.isdigit():
        raise ValueError("Invalid old number '%s'" % old_s)
    if inc_s and not inc_s.isdigit():
        raise ValueError("Invalid increment '%s'" % inc_s)
    new = int(new_s) if new_s else 10
    old = int(old_s) if old_s else None
    inc = int(inc_s) if inc_s else 10
    return new, old, inc


# --------------------------------------------------------------------------- #
#  PLAY music macro language (manual PLAY)
# --------------------------------------------------------------------------- #
class PlayMusic:
    """GW-BASIC PLAY music macro language (manual PLAY).

    Parses a PLAY string into (frequency, milliseconds) segments and
    hands them to the System's background speaker in order, so the notes
    play one after another and the statement never blocks the program
    (the same design this interpreter uses for SOUND).  A rest is a
    segment with the silence frequency (32767, the manual's "silence"
    frequency).  Note n (0..84) sounds at 440 * 2^((n-45)/12) Hz: there
    are 7 octaves of 12 notes, C first in each octave, middle C is the
    first note of octave 3 (note 36) and A4 = note 45.
    """

    # Chromatic position of each letter within an octave (C first; the
    # black keys occupy positions 1, 3, 6, 8, and 10).
    NOTE_POS = {'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11}
    # Black-key positions within an octave: C#, D#, F#, G#, A#.
    BLACK_KEYS = {1, 3, 6, 8, 10}
    SILENCE = 32767  # manual SOUND: the "silence" frequency

    def __init__(self, system, interp):
        self.system = system
        self.interp = interp

    def play(self, s, depth=0):
        """Parse and queue the music in string s.  Returns True when at
        least one note (or rest) was queued."""
        if depth > 16:
            raise BasicError("Nested Too Deep")
        # Manual PLAY defaults: octave 4, length L4, tempo 120, normal
        # (MN) style, music foreground.
        state = {'oct': 4, 'len': 4, 'tempo': 120, 'style': 7.0 / 8.0,
                 'bg': False}
        segs = []
        self._parse(str(s), state, segs, depth)
        if state['bg'] and len(segs) > 32:
            # MB: the background buffer holds 32 notes (or rests); anything
            # beyond the buffer is dropped (manual PLAY).
            segs = segs[:32]
        if not segs:
            return False
        self.system.stop_speaker()  # cancel any active (or infinite) tone
        for freq, ms in segs:
            self.system._play_tone(freq, max(1, int(round(ms))))
        return True

    # -- timing --------------------------------------------------------------- #
    def _note_ms(self, state):
        # L4 (quarter note) duration from the tempo, scaled by the current
        # note length and style (MN 7/8, ML 1, MS 3/4).
        return 60000.0 / state['tempo'] * 4.0 / state['len'] * state['style']

    def _rest_ms(self, n, state):
        # Rests and pauses take the full L-scaled time, unstyled.
        return 60000.0 / state['tempo'] * 4.0 / state['len'] * n

    def _freq(self, note):
        freq = 440.0 * 2.0 ** ((note - 45) / 12.0)
        # Clamp to the Windows sound driver range (37..32767 Hz).
        return int(max(37, min(32767, round(freq))))

    # -- macro string parser ---------------------------------------------------- #
    def _parse(self, s, state, segs, depth):
        i, n = 0, len(s)
        while i < n:
            c = s[i]
            if c in ' \t;':
                i += 1
                continue
            up = c.upper()
            if up in self.NOTE_POS:
                # A note: optional sharp/flat, optional length, dots.
                i += 1
                acc = 0
                if i < n and s[i] in '#+-':
                    acc = 1 if s[i] in '#+' else -1
                    i += 1
                    # Manual PLAY: # / + / - must land on a black key.
                    if (self.NOTE_POS[up] + acc) % 12 not in self.BLACK_KEYS:
                        raise BasicError("Illegal function call")
                note = state['oct'] * 12 + self.NOTE_POS[up] + acc
                if note < 0 or note > 84:
                    raise BasicError("Illegal function call")
                # A length following the note is equivalent to L<len>.
                j = i
                while j < n and s[j].isdigit():
                    j += 1
                if j > i:
                    state['len'] = self._check_len(int(s[i:j]))
                    i = j
                ms = self._note_ms(state)
                i, f = self._dots(s, i)
                segs.append((self._freq(note), ms * f))
                continue
            if up == 'L':
                v, i = self._num_at(s, i + 1)
                state['len'] = self._check_len(v)
                continue
            if up == 'T':
                v, i = self._num_at(s, i + 1)
                if v < 32 or v > 255:
                    raise BasicError("Illegal function call")
                state['tempo'] = v
                continue
            if up == 'O':
                v, i = self._num_at(s, i + 1)
                if v < 0 or v > 6:
                    raise BasicError("Illegal function call")
                state['oct'] = v
                continue
            if up == 'N':
                v, i = self._num_at(s, i + 1)
                if v < 0 or v > 84:
                    raise BasicError("Illegal function call")
                if v == 0:
                    # A rest (full L-scaled time, dots extend it).
                    i, f = self._dots(s, i)
                    segs.append((self.SILENCE, self._rest_ms(1, state) * f))
                else:
                    ms = self._note_ms(state)
                    i, f = self._dots(s, i)
                    segs.append((self._freq(v), ms * f))
                continue
            if up == 'P':
                v, i = self._num_at(s, i + 1)
                # Manual PLAY: P may range from 1-64, so P0 is invalid.
                if v < 1 or v > 64:
                    raise BasicError("Illegal function call")
                i, f = self._dots(s, i)
                segs.append((self.SILENCE, self._rest_ms(v, state) * f))
                continue
            if up == 'M':
                i += 1
                if i >= n or s[i].upper() not in 'FBLSN':
                    raise BasicError("Illegal function call")
                m = s[i].upper()
                i += 1
                if m == 'F':
                    state['bg'] = False  # MF: music foreground
                elif m == 'B':
                    state['bg'] = True   # MB: music background
                elif m == 'N':
                    state['style'] = 7.0 / 8.0  # MN: normal
                elif m == 'L':
                    state['style'] = 1.0        # ML: legato
                else:
                    state['style'] = 3.0 / 4.0  # MS: staccato
                continue
            if up == 'X':
                # X string; : execute a substring variable (manual PLAY).
                j = i + 1
                while j < n and (s[j].isalnum() or s[j] in '$%#!'):
                    j += 1
                name = s[i + 1:j]
                if not name:
                    raise BasicError("Illegal function call")
                k = j
                while k < n and s[k] in ' \t':
                    k += 1
                if k >= n or s[k] != ';':
                    raise BasicError("Illegal function call")
                i = k + 1
                v = self.interp.get_var(name)
                if isinstance(v, str):
                    self._parse(v, state, segs, depth + 1)
                else:
                    raise BasicError("Type Mismatch")
                continue
            if c in '<>':
                # Octave shift: the note must follow directly.
                i += 1
                while i < n and s[i] in ' \t':
                    i += 1
                if i >= n or s[i].upper() not in self.NOTE_POS:
                    raise BasicError("Illegal function call")
                state['oct'] += 1 if c == '>' else -1
                if state['oct'] < 0 or state['oct'] > 6:
                    raise BasicError("Illegal function call")
                continue  # the next loop pass plays the note
            raise BasicError("Illegal function call")

    @staticmethod
    def _check_len(v):
        if v < 1 or v > 64:
            raise BasicError("Illegal function call")
        return v

    @staticmethod
    def _dots(s, i):
        # Manual PLAY: each period multiplies the playing time by 3/2
        # (A. = 3/2, A.. = 9/4, A... = 27/8 of the ascribed value).
        f = 1.0
        n = len(s)
        while i < n and s[i] == '.':
            f *= 1.5
            i += 1
        return i, f

    def _num_at(self, s, i):
        """Parse the numeric argument at s[i]: a constant, or a variable
        with = in front of it (=variable), where a semicolon is required
        after the variable (manual PLAY).  Returns (value, new_index)."""
        n = len(s)
        if i < n and s[i] == '=':
            i += 1
            j = i
            while j < n and (s[j].isalnum() or s[j] in '$%#!'):
                j += 1
            name = s[i:j]
            if not name:
                raise BasicError("Illegal function call")
            k = j
            while k < n and s[k] in ' \t':
                k += 1
            if k < n and s[k] == ';':
                k += 1
            v = self.interp.get_var(name)
            if isinstance(v, str):
                raise BasicError("Type Mismatch")
            return int(v), k
        j = i
        while j < n and s[j].isdigit():
            j += 1
        txt = s[i:j]
        if not txt:
            raise BasicError("Illegal function call")
        k = j
        if k < n and s[k] == ';':
            k += 1  # a semicolon after a constant is allowed too
        return int(txt), k


# --------------------------------------------------------------------------- #
#  Parser
# --------------------------------------------------------------------------- #
STATEMENT_KEYWORDS = {
    'PRINT', 'INPUT', 'LET', 'IF', 'FOR', 'NEXT', 'WHILE', 'WEND',
    'GOTO', 'GOSUB', 'RETURN', 'RESUME', 'ON', 'REM', 'DATA', 'READ', 'RESTORE',
    'END', 'STOP', 'DIM', 'ERASE', 'SWAP', 'DEF', 'CLS', 'BEEP', 'SLEEP', 'SOUND',
    'SETFPS', 'MOUSE',
    'RANDOMIZE', 'LOCATE', 'ELSE', 'ENDIF',
    'OPEN', 'CLOSE', 'GET', 'PUT', 'SEEK',
    'KILL',
    'LINE', 'CIRCLE', 'PSET', 'PRESET', 'PAINT', 'DRAW', 'PALETTE', 'COLOR',
    # TEXTRotate matches case-insensitively: the parser uppercases every
    # name token, so the all-caps form is what gets looked up here.
    'INK', 'SCREEN', 'SCREENSIZE', 'TEXTSIZE', 'TEXTRotate'.upper(),
    # TEXTFONT (extension): choose the face/weight of the monitor text
    # (see parse_textfont / Screen.textfont).
    'TEXTFONT',
    # PAUSE (extension): stop until SPACE or ENTER is pressed (see do_pause).
    'WCLOSE', 'PAUSE', 'CURSOR', 'VIEW',
    'WINDOW',
    'BLOAD', 'BSAVE', 'OUT', 'POKE', 'PLAY',
    'MUSICFILE', 'PLAYMUSIC', 'STOPMUSIC', 'MUSICVOLUME',
    'TRAP',
    'KEY', 'ENVIRON',
    'DO', 'LOOP',
    'OPTION',
    'TYPE', 'FIELD', 'REDIM',
    'ERROR',
    'RUN', 'SYSTEM', 'EDIT',
    'WRITE',
    'WAIT',
    'LSET', 'RSET', 'LPRINT', 'COMMON', 'NEW',
    'DEFINT', 'DEFDBL', 'DEFSNG', 'DEFSTR',
}

# Functions that can be referenced without parentheses.
NOARG_FUNCTIONS = {
    'SCREEN', 'TIMER', 'CSRLIN', 'INKEY$', 'DATE$', 'TIME$',
    'DAY', 'MONTH', 'YEAR', 'HOUR', 'MINUTE', 'SECOND', 'FRE', 'RND',
    'POS',
}

BUILTIN_FUNCTIONS = {
    'LEN', 'LEFT$', 'RIGHT$', 'MID$', 'CHR$', 'ASC', 'STR$', 'VAL', 'INSTR',
    'UCASE$', 'LCASE$', 'SPACE$', 'TRIM$',
    'ABS', 'INT', 'SQR', 'SIN', 'COS', 'TAN', 'LOG', 'EXP', 'RND', 'SGN',
    'FIX', 'ROUND', 'ATN', 'ASIN', 'ACOS',
    'CDBL', 'CSNG', 'CVI', 'CVS', 'CVD', 'MKI$', 'MKS$', 'MKD$',
    'EOF', 'LOC', 'LOF', 'DIR$', 'INKEY$', 'INPUT$', 'VARPTR',
    'VARPTR$', 'PEEK', 'PEER', 'POINT', 'RGB',
    'TIMER', 'FRE', 'CSRLIN', 'POS', 'CINT', 'ROUNDDOWN', 'ROUNDUP', 'ROUNDFRAC',
    'HEX$', 'OCT$', 'BIN$', 'STRING$', 'DAY', 'MONTH', 'YEAR', 'HOUR', 'MINUTE',
    'SECOND', 'SCREEN', 'INK', 'ENVIRON', 'ENVIRON$',
    'XSZ', 'YSZ', 'XSIZE', 'YSIZE',
}


class Parser:
    def __init__(self, tokens, source=None):
        self.tokens = tokens
        self.pos = 0
        self.source = source

    # -- token stream helpers ------------------------------------------------ #
    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def advance(self):
        tok = self.peek()
        self.pos += 1
        return tok

    def at_end(self):
        return self.pos >= len(self.tokens)

    def at_stmt_end(self):
        """True at the end of the current statement: end of line, a ':'
        separator (statements inside an IF ... THEN/ELSE clause are
        separated by ':' rather than end of line), or an ELSE keyword -
        a statement inside an IF ... THEN clause ends where the ELSE
        clause begins (IF a THEN PLAYMUSIC w ELSE PLAYMUSIC w1)."""
        if self.at_end():
            return True
        tok = self.peek()
        if tok is None:
            return True
        if tok[0] == 'op' and tok[1] == ':':
            return True
        return tok[0] == 'name' and tok[1].upper() == 'ELSE'


    def stmt_tokens(self):
        """Tokens from the current position to the end of the current
        statement (a ':' separator or end of line), not including the
        separator."""
        toks = []
        for i in range(self.pos, len(self.tokens)):
            t = self.tokens[i]
            if t[0] == 'op' and t[1] == ':':
                break
            toks.append(t)
        return toks

    def match_op(self, *ops):
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] in ops:
            self.pos += 1
            return True
        return False

    def match_keyword(self, *keywords):
        tok = self.peek()
        if tok and tok[0] == 'name' and tok[1].upper() in keywords:
            self.pos += 1
            return True
        return False

    def expect_op(self, op):
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] == op:
            self.pos += 1
            return
        raise BasicError("Expected '%s'" % op)

    # -- statements ---------------------------------------------------------- #
    def parse_statement(self):
        tok = self.peek()
        if tok is None:
            return None
        if tok[0] == 'rem':
            self.advance()
            return ('rem',)
        if tok[0] == 'op' and tok[1] == '?':
            self.advance()
            return self.parse_print_items()
        if tok[0] == 'name':
            keyword = tok[1].upper()
            if keyword in STATEMENT_KEYWORDS:
                self.advance()
                return self.parse_keyword(keyword)
            return self.parse_let()
        raise BasicError("Unexpected token %s" % (tok,))

    def parse_keyword(self, keyword):
        if keyword == 'PRINT':
            return self.parse_print_items()
        if keyword == 'INPUT':
            return self.parse_input()
        if keyword == 'LET':
            return self.parse_let()
        if keyword == 'IF':
            return self.parse_if()
        if keyword == 'FOR':
            return self.parse_for()
        if keyword == 'NEXT':
            return self.parse_next()
        if keyword == 'WHILE':
            return self.parse_while()
        if keyword == 'WEND':
            return ('wend',)
        if keyword == 'ENDIF':
            return ('endif',)
        if keyword == 'GOTO':
            return ('goto', self.parse_line_number())
        if keyword == 'GOSUB':
            return ('gosub', self.parse_line_number())
        if keyword == 'RETURN':
            if self.peek() and self.peek()[0] == 'number':
                return ('return', self.parse_line_number())
            return ('return', None)
        if keyword == 'RESUME':
            if self.match_keyword('NEXT'):
                return ('resume_next',)
            if self.peek() and self.peek()[0] == 'number':
                return ('resume', self.parse_line_number())
            return ('resume', None)
        if keyword == 'ON':
            return self.parse_on()
        if keyword == 'REM':
            return ('rem',)
        if keyword == 'DATA':
            return self.parse_data()
        if keyword == 'READ':
            return self.parse_read()
        if keyword == 'RESTORE':
            if self.peek() and self.peek()[0] == 'number':
                return ('restore', self.parse_line_number())
            return ('restore', None)
        if keyword == 'END':
            # END takes no argument (manual END): a leftover on the line,
            # e.g. the "IF" of a two-word "END IF" misspelling, is a syntax
            # error rather than a silently-executed END.  A trailing REM
            # still terminates the statement normally.
            tok = self.peek()
            if tok is not None and not (tok[0] == 'rem' or
                                        (tok[0] == 'op' and tok[1] == ':')):
                raise BasicError("END takes no arguments")
            return ('end',)
        if keyword == 'STOP':
            return ('stop',)
        if keyword == 'DIM':
            return self.parse_dim()
        if keyword == 'ERASE':
            return self.parse_erase()
        if keyword == 'SWAP':
            return self.parse_swap()
        if keyword == 'TRAP':
            return self.parse_trap()
        if keyword == 'DEF':
            if self.peek() and self.peek()[0] == 'name' and self.peek()[1].upper() == 'SEG':
                self.advance()  # consume SEG
                # DEF SEG [=address] (manual DEFSEG): the '=' is optional.
                self.match_op('=')
                n = None
                if not self.at_stmt_end():
                    n = self.parse_expression()
                return ('def_seg', n)
            return self.parse_def_fn()
        if keyword == 'DEFINT':
            return self.parse_def_type('integer')
        if keyword == 'DEFDBL':
            return self.parse_def_type('double')
        if keyword == 'DEFSNG':
            return self.parse_def_type('single')
        if keyword == 'DEFSTR':
            return self.parse_def_type('string')
        if keyword == 'CLS':
            n = None
            if not self.at_stmt_end():
                n = self.parse_expression()
            return ('cls', n)
        if keyword == 'BEEP':
            return ('beep',)
        if keyword == 'SOUND':
            # SOUND freq,duration (manual SOUND)
            freq = self.parse_expression()
            self.expect_op(',')
            duration = self.parse_expression()
            return ('sound', freq, duration)
        if keyword == 'SLEEP':
            return ('sleep', self.parse_expression())
        if keyword == 'SETFPS':
            return ('setfps', self.parse_expression())
        if keyword == 'MOUSE':
            return self.parse_mouse()
        if keyword == 'RANDOMIZE':
            return self.parse_randomize()
        if keyword == 'LOCATE':
            return self.parse_locate()
        if keyword == 'ELSE':
            return self.parse_else()
        if keyword == 'OPEN':
            return self.parse_open()
        if keyword == 'CLOSE':
            return self.parse_close()
        if keyword == 'GET':
            return self.parse_get()
        if keyword == 'PUT':
            return self.parse_put()
        if keyword == 'SEEK':
            return self.parse_seek()
        if keyword == 'KILL':
            return ('kill', self.parse_kill_filename())
        if keyword == 'LINE':
            return self.parse_line()
        if keyword == 'CIRCLE':
            return self.parse_circle()
        if keyword == 'PAINT':
            return self.parse_paint()
        if keyword == 'POKE':
            return self.parse_poke()
        if keyword == 'PLAY':
            return ('play', self.parse_expression())
        if keyword == 'MUSICFILE':
            return self.parse_musicfile()
        if keyword == 'PLAYMUSIC':
            return self.parse_playmusic()
        if keyword == 'STOPMUSIC':
            return self.parse_stopmusic()
        if keyword == 'MUSICVOLUME':
            return self.parse_musicvolume()
        if keyword == 'PSET':
            return self.parse_pset()
        if keyword == 'PRESET':
            return self.parse_preset()
        if keyword == 'DRAW':
            return ('draw', self.parse_expression())
        if keyword == 'PALETTE':
            return self.parse_palette()
        if keyword == 'COLOR':
            return self.parse_color()
        if keyword == 'INK':
            return self.parse_ink()
        if keyword == 'SCREEN':
            return self.parse_screen()
        if keyword == 'SCREENSIZE':
            return self.parse_screensize()
        if keyword == 'TEXTSIZE':
            return self.parse_textsize()
        if keyword == 'TEXTRotate'.upper():
            return self.parse_textrotate()
        if keyword == 'TEXTFONT':
            return self.parse_textfont()
        if keyword == 'WCLOSE':
            # WCLOSE (extension): close the graphics window, like the
            # window's own ESC / Ctrl+C.  It takes no arguments.
            if not self.at_stmt_end():
                raise BasicError("Expected end of statement")
            return ('wclose',)
        if keyword == 'PAUSE':
            # PAUSE (extension): stop the program until the user presses the
            # SPACE or ENTER key; any other key is ignored.  No arguments.
            if not self.at_stmt_end():
                raise BasicError("Expected end of statement")
            return ('pause',)
        if keyword == 'WINDOW':
            return self.parse_window()
        if keyword == 'CURSOR':
            return ('cursor', self.parse_expression())
        if keyword == 'VIEW':
            return self.parse_view()
        if keyword == 'BLOAD':
            return self.parse_bload()
        if keyword == 'BSAVE':
            return self.parse_bsave()
        if keyword == 'OUT':
            return self.parse_out()
        if keyword == 'KEY':
            return self.parse_key()
        if keyword == 'ENVIRON':
            return ('environ', self.parse_optional_expr())
        if keyword == 'DO':
            return self.parse_do()
        if keyword == 'LOOP':
            return self.parse_loop()
        if keyword == 'OPTION':
            return self.parse_option()
        if keyword == 'TYPE':
            return self.parse_type()
        if keyword == 'FIELD':
            return self.parse_field()
        if keyword == 'REDIM':
            return self.parse_redim()
        if keyword == 'ERROR':
            return ('error', self.parse_expression())
        if keyword == 'RUN':
            return ('run', self.parse_optional_expr())
        if keyword == 'SYSTEM':
            return ('system',)
        if keyword == 'EDIT':
            return ('edit', self.parse_optional_expr())
        if keyword == 'WRITE':
            return self.parse_write()
        if keyword == 'WAIT':
            args = [self.parse_expression()]
            if self.match_op(','):
                args.append(self.parse_expression())
                if self.match_op(','):
                    args.append(self.parse_expression())
            return ('wait', args)
        if keyword == 'LSET':
            return self._parse_lset_rset('lset')
        if keyword == 'RSET':
            return self._parse_lset_rset('rset')
        if keyword == 'LPRINT':
            if self.match_keyword('USING'):
                fmt = self.parse_expression()
                self.match_op(';')
                self.match_op(',')
                args = []
                while not self.at_end():
                    if self.peek()[0] == 'op' and self.peek()[1] == ':':
                        break  # statement separator ends the item list
                    args.append(self.parse_expression())
                    if self.match_op(';') or self.match_op(','):
                        continue
                    break
                return ('lprint_using', fmt, args)
            items = self._parse_print_item_list()
            return ('lprint', items)
        if keyword == 'COMMON':
            names = []
            while not self.at_stmt_end():
                tok = self.peek()
                if tok is None or tok[0] != 'name':
                    raise BasicError("Expected variable in COMMON")
                names.append(tok[1])
                self.advance()
                if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
                    self.advance()
                    # Empty parentheses mark an array with no bounds given
                    # (manual COMMON: "Place parentheses after the variable
                    # name to indicate array variables"; example
                    # `COMMON A, B, C, D(),G$`).
                    if not (self.peek() and self.peek()[0] == 'op'
                            and self.peek()[1] == ')'):
                        while True:
                            self.parse_expression()
                            if not self.match_op(','):
                                break
                    self.expect_op(')')
                if not self.match_op(','):
                    break
            return ('common', names)
        if keyword == 'NEW':
            return ('new',)
        raise BasicError("Unknown statement '%s'" % keyword)

    def _parse_lset_rset(self, tag):
        # LSET/RSET string variable = string expression (manual LSET/RSET).
        target = self.parse_var_or_arr()
        self.expect_op('=')
        value = self.parse_expression()
        return (tag, target, value)

    def parse_print_items(self):
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '#':
            self.advance()
            filenum = self.parse_expression()
            init_sep = None
            if self.match_op(','):
                init_sep = ','
            elif self.match_op(';'):
                init_sep = ';'
            items = self._parse_print_item_list()
            return ('print_file', filenum, init_sep, items)
        items = self._parse_print_item_list()
        return ('print', items)

    def _parse_print_item_list(self):
        items = []
        if self.at_end():
            return items
        # PRINT USING "fmt", a, b, ...  The manual's examples separate the
        # format and the argument list with ; or , (either is accepted).
        if self.peek() and self.peek()[0] == 'name' and self.peek()[1].upper() == 'USING':
            self.advance()
            fmt = self.parse_expression()
            args = []
            if self.match_op(';') or self.match_op(','):
                while not self.at_end():
                    if self.peek()[0] == 'op' and self.peek()[1] == ':':
                        break  # statement separator ends the item list
                    args.append(self.parse_expression())
                    if self.match_op(';') or self.match_op(','):
                        continue
                    break
            items.append(('using', fmt, args))
            return items
        while True:
            tok = self.peek()
            if tok is not None and tok[0] == 'op' and tok[1] == ':':
                break  # statement separator: the PRINT item list ends here
            if (tok and tok[0] == 'name' and tok[1].upper() in ('TAB', 'SPC')
                    and self.pos + 1 < len(self.tokens)
                    and self.tokens[self.pos + 1] == ('op', '(')):
                # TAB(n) / SPC(n): a marker immediately followed by the item
                # it positions (no separator required between them).
                kind = tok[1].upper()
                self.advance()  # consume TAB/SPC
                self.expect_op('(')
                n = self.parse_expression()
                self.expect_op(')')
                # Optional separator after TAB/SPC
                if (self.peek() and self.peek()[0] == 'op'
                        and self.peek()[1] in (';', ',')):
                    self.advance()
                # A trailing TAB/SPC (no item after it) is legal: it has an
                # implied semicolon (manual TAB/SPC).  expr is None in that
                # case and the marker only affects position / newline.
                # The positioned item may be any expression, including a
                # string literal ("PRINT "A" TAB(12) "B";").
                expr = None
                nxt = self.peek()
                if (nxt is not None and nxt[0] in ('name', 'number', 'op', 'string')
                        and nxt[1] not in (';', ',', ':')):
                    expr = self.parse_expression()
                sep = None
                if self.match_op(';'):
                    sep = ';'
                elif self.match_op(','):
                    sep = ','
                marker = '__tab__' if kind == 'TAB' else '__spc__'
                items.append(((marker, n, expr), sep))
                if sep is None:
                    break
                if self.at_end():
                    break
                continue
            if tok and tok[0] == 'op' and tok[1] in (';', ','):
                # Empty item: a bare separator (e.g. "PRINT ; ;" or
                # "PRINT 1; ; 2") contributes no text of its own.
                sep = tok[1]
                self.advance()
                items.append((('str', ''), sep))
                if self.at_end():
                    break  # trailing separator suppresses newline
                continue
            expr = self.parse_expression()
            sep = None
            if self.match_op(';'):
                sep = ';'
            elif self.match_op(','):
                sep = ','
            items.append((expr, sep))
            if sep is None:
                # A space-separated item follows only when the next token is
                # a value token (name/number) that is not a keyword or a
                # TAB/SPC marker handled above.  Otherwise the list ends.
                nxt = self.peek()
                if (nxt is not None and nxt[0] in ('name', 'number')
                        and not self._is_keyword(nxt[1])):
                    sep = ' '
                    items[-1] = (expr, sep)
                    continue
                break
            if self.at_end():
                break  # trailing separator (e.g. PRINT I;) suppresses newline
        return items

    def _is_keyword(self, word):
        return word.upper() in STATEMENT_KEYWORDS

    def parse_input(self):
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '#':
            self.advance()
            filenum = self.parse_expression()
            if not self.match_op(','):
                self.match_op(';')  # optional separator
            var_names = []
            while True:
                tok = self.peek()
                if tok and tok[0] == 'name':
                    var_names.append(tok[1])
                    self.advance()
                    if self.match_op(','):
                        continue
                    break
                break
            return ('input_file', filenum, var_names)
        prompt = None
        suppress_qmark = False
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] == ';':
            # A leading semicolon suppresses the RETURN key (data is read on
            # the same line).  It does NOT suppress the question mark.
            self.advance()
            tok = self.peek()
        if tok and tok[0] == 'string':
            prompt = self.parse_expression()
            # A comma after the prompt suppresses the question mark; a
            # semicolon does not (manual INPUT page).
            if self.match_op(','):
                suppress_qmark = True
            self.match_op(';')
        var_names = []
        while True:
            tok = self.peek()
            if tok and tok[0] == 'name':
                var_names.append(tok[1])
                self.advance()
                if self.match_op(','):
                    continue
                break
            break
        return ('input', prompt, var_names, suppress_qmark)

    # -- MUSICFILE / PLAYMUSIC ------------------------------------------------- #
    def _parse_musicvar(self):
        # The music handle: a numeric variable or array-element reference,
        # parsed like an assignment target (('var', name) or
        # ('arr', name, indices)).
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected variable")
        name = tok[1]
        self.advance()
        if self.peek() is not None and self.peek()[0] == 'op' \
                and self.peek()[1] == '(':
            self.advance()
            indices = []
            while True:
                indices.append(self.parse_expression())
                t2 = self.peek()
                if t2 is not None and t2[0] == 'op' and t2[1] == ',':
                    self.advance()
                    continue
                break
            self.expect_op(')')
            return ('arr', name, indices)
        return ('var', name)

    def parse_musicfile(self):
        # MUSICFILE variable, file name -- bind a .wav/.mp3/.wma file to a
        # numeric variable (or array element).  The file name is a quoted
        # string (for names with spaces or drive paths), a bare name
        # without spaces (a drive path requires the quoted form, since ':'
        # is the statement separator), or a string variable / string
        # expression holding the file name (resolved at run time).
        ref = self._parse_musicvar()
        self.expect_op(',')
        tok = self.peek()
        if tok is None:
            raise BasicError("Expected file name")
        if tok[0] == 'name' and tok[1].endswith('$'):
            # File name held in a string variable (or string array
            # element), or built from a string expression starting with
            # one: resolved when the statement runs, so the value may
            # change between executions.
            path = self.parse_expression()
        elif tok[0] == 'string':
            self.advance()
            path = tok[1]
        elif tok[0] == 'name':
            parts = [tok[1]]
            self.advance()
            # Bare name: consume the rest of the statement's name tokens as
            # the file name.  The tokenizer skips a '.' that is not part of
            # a number (e.g. the extension dot in tone.wav), so two name
            # tokens that are adjacent in the stream were separated by a '.'
            # in the source - re-insert it.  A backslash (path separator)
            # survives as an op token and is kept.  Anything else ends the
            # name; a space in a file name or a drive path requires the
            # quoted form above.
            last_was_name = True
            while True:
                t2 = self.peek()
                if t2 is None:
                    break
                if t2[0] == 'name':
                    if last_was_name:
                        parts.append('.')
                    parts.append(t2[1])
                    self.advance()
                    last_was_name = True
                elif t2[0] == 'op' and t2[1] == '\\':
                    parts.append('\\')
                    self.advance()
                    last_was_name = False
                else:
                    break
            path = ''.join(parts)
        else:
            raise BasicError("Expected file name")
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('musicfile', ref, path)

    def parse_playmusic(self):
        # PLAYMUSIC variable -- play the file bound to the variable.
        ref = self._parse_musicvar()
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('playmusic', ref)

    def parse_stopmusic(self):
        # STOPMUSIC -- stop the music PLAYMUSIC started.  No arguments;
        # the MUSICFILE assignments are left in place.
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('stopmusic',)

    def parse_musicvolume(self):
        # MUSICVOLUME n -- set the music stream volume (0-100).  One
        # numeric expression; applies to the current stream when
        # music is playing, otherwise takes effect at the next
        # PLAYMUSIC.
        n = self.parse_expression()
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('musicvolume', n)

    def parse_let(self):
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected variable")
        name = tok[1]
        if name.upper() == 'MID$':
            self.advance()
            self.expect_op('(')
            args = []
            while True:
                args.append(self.parse_expression())
                if self.match_op(','):
                    continue
                break
            self.expect_op(')')
            self.expect_op('=')
            value = self.parse_expression()
            return ('mid_assign', args, value)
        self.advance()
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
            self.advance()
            indices = []
            while True:
                indices.append(self.parse_expression())
                if self.match_op(','):
                    continue
                break
            self.expect_op(')')
            target = ('arr', name, indices)
        else:
            target = ('var', name)
        self.expect_op('=')
        value = self.parse_expression()
        return ('let', target, value)

    def parse_if(self):
        cond = self.parse_expression()
        # A colon (or comma) may separate the expression from the clause
        # keyword: "IF A = 4 : THEN ..." / "IF A > 3 , THEN ...".
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] in (',', ':'):
            self.advance()
        if self.match_keyword('GOTO'):
            # IF expression GOTO line number [, ELSE ...] -- the comma between
            # the line number and ELSE is optional (manual IF).
            self.match_op(',')  # a comma is also allowed after GOTO
            line = self.parse_line_number()
            then_action = [('goto', line)]
            else_action = None
            self.match_op(',')  # a comma is allowed between the line number and ELSE
            if self.match_keyword('ELSE'):
                self.match_op(',')  # a comma is also allowed after ELSE
                else_action = self.parse_then_else_part()
            return ('if', cond, then_action, else_action)
        if not self.match_keyword('THEN'):
            raise BasicError("Expected THEN")
        self.match_op(',')  # a comma is also allowed after THEN
        then_action = self.parse_then_else_part()
        else_action = None
        self.match_op(',')  # a comma is also allowed before ELSE
        if self.match_keyword('ELSE'):
            self.match_op(',')  # a comma is also allowed after ELSE
            else_action = self.parse_then_else_part()
        return ('if', cond, then_action, else_action)

    def parse_then_else_part(self):
        # The THEN/ELSE clause is the rest of the line: either a line
        # number (implicit GOTO) or one or more colon-separated
        # statements. All of them are conditional on the IF.
        self.match_op(',')  # tolerate a comma right after the clause keyword
        tok = self.peek()
        if tok is None:
            return [('fall',)]
        if tok[0] == 'number':
            # IF...THEN line-number
            self.advance()
            return [('goto', int(tok[1]))]
        actions = []
        while not self.at_end():
            stmt = self.parse_statement()
            if stmt is None:
                break
            actions.append(('stmt', stmt))
            if not self.match_op(':'):
                break
        if not actions:
            return [('fall',)]
        return actions

    def parse_else(self):
        self.match_op(',')  # tolerate a comma right after ELSE
        tok = self.peek()
        if tok is None:
            return ('else', None)
        if tok[0] == 'number':
            return ('else', ('goto', int(self.advance()[1])))
        if tok[0] == 'name' and tok[1].upper() == 'GOTO':
            self.advance()
            return ('else', ('goto', self.parse_line_number()))
        stmt = self.parse_statement()
        return ('else', ('stmt', stmt))

    def parse_for(self):
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected variable in FOR")
        var = tok[1]
        self.advance()
        self.expect_op('=')
        start = self.parse_expression()
        if not self.match_keyword('TO'):
            raise BasicError("Expected TO")
        end = self.parse_expression()
        step = ('num', 1)
        if self.match_keyword('STEP'):
            step = self.parse_expression()
        return ('for', var, start, end, step)

    def parse_next(self):
        # NEXT [variable][,variable...]
        vars = []
        while True:
            tok = self.peek()
            if tok and tok[0] == 'name':
                vars.append(tok[1])
                self.advance()
                if not self.match_op(','):
                    break
            else:
                break
        if len(vars) == 0:
            return ('next', None)
        if len(vars) == 1:
            return ('next', vars[0])
        return ('next_multi', vars)

    def parse_while(self):
        return ('while', self.parse_expression())

    def parse_on(self):
        tok = self.peek()
        if tok and tok[0] == 'name' and tok[1].upper() == 'ERROR':
            self.advance()
            if self.match_keyword('OFF'):
                return ('on_error', None)
            if not self.match_keyword('GOTO'):
                raise BasicError("Expected GOTO or OFF after ON ERROR")
            return ('on_error', self.parse_line_number())
        if tok and tok[0] == 'name' and tok[1].upper() == 'KEY':
            self.advance()  # KEY
            n = None
            if self.peek() and self.peek()[0] == 'op' \
                    and self.peek()[1] == '(':
                # ON KEY(n) ...: the key number is in parentheses.
                self.advance()
                if not (self.peek() and self.peek()[0] == 'number'):
                    raise BasicError("Expected key number in ON KEY(n)")
                n = int(self.advance()[1])
                self.expect_op(')')
            elif self.peek() and self.peek()[0] == 'number':
                n = int(self.advance()[1])
            if self.match_keyword('OFF'):
                return ('on_key', n, None)
            if self.match_keyword('GOTO'):
                return ('on_key', n, ('goto', self.parse_line_number()))
            if self.match_keyword('GOSUB'):
                return ('on_key', n, ('gosub', self.parse_line_number()))
            raise BasicError("Expected GOSUB, GOTO, or OFF after ON KEY")
        if tok and tok[0] == 'name' and tok[1].upper() == 'TIMER':
            self.advance()  # TIMER
            n = None
            if self.peek() and self.peek()[0] == 'op' \
                    and self.peek()[1] == '(':
                # ON TIMER(n) ...: the interval is in parentheses.
                self.advance()
                if not (self.peek() and self.peek()[0] == 'number'):
                    raise BasicError("Expected number in ON TIMER(n)")
                n = int(self.advance()[1])
                self.expect_op(')')
            elif self.peek() and self.peek()[0] == 'number':
                n = int(self.advance()[1])
            if self.match_keyword('OFF'):
                return ('on_timer', n, None)
            if not self.match_keyword('GOTO'):
                raise BasicError("Expected GOTO or OFF after ON TIMER")
            return ('on_timer', n, self.parse_line_number())
        expr = self.parse_expression()
        if self.match_keyword('GOTO'):
            return ('on_goto', expr, self.parse_line_list())
        if self.match_keyword('GOSUB'):
            return ('on_gosub', expr, self.parse_line_list())
        raise BasicError("Expected GOTO or GOSUB after ON")

    def parse_line_list(self):
        lines = []
        while True:
            lines.append(self.parse_line_number())
            if self.match_op(','):
                continue
            break
        return lines

    def parse_line_number(self):
        tok = self.peek()
        if tok and tok[0] == 'number':
            return int(self.advance()[1])
        raise BasicError("Expected line number")

    def parse_data(self):
        items = []
        while not self.at_stmt_end():
            tok = self.peek()
            if tok[0] == 'string':
                self.advance()
                items.append((True, tok[1]))
            elif tok[0] == 'number':
                self.advance()
                items.append((False, parse_number(tok[1])))
            elif tok[0] == 'rem':
                # REM inside DATA is treated as legal (unquoted string) data:
                # "it will be considered to be legal data."
                self.advance()
                items.append((True, tok[1].strip()))
            elif tok[0] == 'name':
                # An unquoted string constant (a bare word).  Quotation marks
                # are only required when the value contains commas/colons or
                # significant leading/trailing spaces.
                self.advance()
                items.append((True, tok[1]))
            elif tok[0] == 'op' and tok[1] == '-':
                self.advance()
                nxt = self.peek()
                if nxt and nxt[0] == 'number':
                    self.advance()
                    items.append((False, -parse_number(nxt[1])))
                else:
                    raise BasicError("Expected number after '-'")
            else:
                raise BasicError("DATA items must be numbers or strings")
            if self.match_op(','):
                continue
            break
        return ('data', items)

    def parse_read(self):
        targets = []
        while True:
            tok = self.peek()
            if tok is None or tok[0] != 'name':
                break
            name = tok[1]
            self.advance()
            if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
                self.advance()
                indices = []
                while True:
                    indices.append(self.parse_expression())
                    if self.match_op(','):
                        continue
                    break
                self.expect_op(')')
                targets.append(('arr', name, indices))
            else:
                targets.append(('var', name))
            if self.match_op(','):
                continue
            break
        return ('read', targets)

    def parse_dim(self):
        # DIM variable(subscripts)[,variable(subscripts)]...
        arrays = []
        while True:
            tok = self.peek()
            if tok is None or tok[0] != 'name':
                raise BasicError("Expected array name in DIM")
            name = tok[1]
            self.advance()
            self.expect_op('(')
            dims = []
            while True:
                dims.append(self.parse_expression())
                if self.match_op(','):
                    continue
                break
            self.expect_op(')')
            arrays.append((name, dims))
            if not self.match_op(','):
                break
        return ('dim', arrays)

    def parse_erase(self):
        # ERASE list of array variables
        names = []
        while True:
            tok = self.peek()
            if tok is None or tok[0] != 'name':
                raise BasicError("Expected array name in ERASE")
            names.append(tok[1])
            self.advance()
            if not self.match_op(','):
                break
        return ('erase', names)

    def parse_swap(self):
        a = self.parse_var_or_arr()
        self.expect_op(',')
        b = self.parse_var_or_arr()
        return ('swap', a, b)

    def parse_trap(self):
        # TRAP ON|OFF (extension): arm or bypass the runtime safety checks
        # (overflow guard + ON KEY/COM trap polling).  Default is ON.
        # (The TRAP keyword token was already consumed by the caller.)
        tok = self.peek()
        if tok is None or tok[0] != 'name' or tok[1].upper() not in ('ON', 'OFF'):
            raise BasicError("Syntax error")
        self.advance()
        return ('trap', tok[1].upper() == 'ON')

    def parse_var_or_arr(self):
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected variable")
        name = tok[1]
        self.advance()
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
            self.advance()
            indices = []
            while True:
                indices.append(self.parse_expression())
                if self.match_op(','):
                    continue
                break
            self.expect_op(')')
            return ('arr', name, indices)
        return ('var', name)

    def parse_def_fn(self):
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected function name after DEF")
        name = tok[1]
        self.advance()
        self.expect_op('(')
        params = []
        while True:
            ptok = self.peek()
            if ptok is None or ptok[0] != 'name':
                break
            params.append(ptok[1])
            self.advance()
            if self.match_op(','):
                continue
            break
        self.expect_op(')')
        self.expect_op('=')
        body = self.parse_expression()
        return ('def_fn', name, params, body)

    def parse_def_type(self, type_name):
        """Parse the name spec of DEFINT/DEFDBL/DEFSNG/DEFSTR.

        The listed names are the EXACT variable names to be typed
        (comma-separated).  A range of two single letters (A-Z) expands
        to the single-letter variable names in between.
        """
        names = set()
        while not self.at_end():
            tok = self.peek()
            if tok is None or tok[0] != 'name':
                break
            word = tok[1].upper()
            self.advance()
            if not word.isalpha():
                continue
            if len(word) == 1:
                # A single letter may form a range: A-Z -> names A..Z.
                end = word
                if (self.peek() and self.peek()[0] == 'op'
                        and self.peek()[1] == '-'):
                    self.advance()  # consume '-'
                    tok2 = self.peek()
                    if (tok2 and tok2[0] == 'name' and tok2[1].isalpha()
                            and len(tok2[1]) == 1):
                        end = tok2[1].upper()
                        self.advance()
                for c in range(ord(word), ord(end) + 1):
                    names.add(chr(c))
            else:
                # Exact multi-letter variable name; a '-' after it is not
                # a range — swallow a trailing name so the stream stays sane.
                names.add(word)
                if (self.peek() and self.peek()[0] == 'op'
                        and self.peek()[1] == '-'):
                    self.advance()  # consume '-'
                    tok2 = self.peek()
                    if tok2 and tok2[0] == 'name' and tok2[1].isalpha():
                        names.add(tok2[1].upper())
                        self.advance()
            if not self.match_op(','):
                break
        return ('def_type', type_name, sorted(names))

    def parse_randomize(self):
        if self.at_stmt_end():
            return ('randomize', None)
        return ('randomize', self.parse_expression())

    def parse_locate(self):
        # LOCATE [row][,[col][,[cursor][,[start][,stop]]]]
        # Omitted parameters are skipped with empty commas (e.g. LOCATE ,,1).
        params = []
        if self.at_stmt_end() or (self.peek() and self.peek()[0] == 'op'
                                  and self.peek()[1] == ','):
            params.append(None)  # row omitted
        else:
            params.append(self.parse_expression())
        for _ in range(4):
            if not self.match_op(','):
                break
            if self.at_stmt_end() or (self.peek() and self.peek()[0] == 'op'
                                      and self.peek()[1] == ','):
                params.append(None)  # skipped parameter
            else:
                params.append(self.parse_expression())
        return ('locate', params)

    # -- file I/O ------------------------------------------------------------ #
    def parse_open(self):
        # First syntax:  OPEN mode, [#]filenum, "filename" [, reclen]
        # Second syntax: OPEN filename [FOR mode] AS [#]filenum [LEN=reclen]
        tok = self.peek()
        if tok and tok[0] == 'string':
            save = self.pos
            self.advance()  # consume the string
            if (self.peek() and self.peek()[0] == 'name'
                    and self.peek()[1].upper() == 'FOR'):
                filename = tok[1]
                self.advance()  # FOR
                return self._parse_open_second(filename)
            self.pos = save
        return self._parse_open_first()

    def _parse_open_first(self):
        # The mode of the first OPEN syntax is either a mode word
        # (INPUT/OUTPUT/APPEND/RANDOM/BINARY) or an expression: a string
        # constant ("I", "O", "R", "A", "B" or a full word) or a numeric
        # expression (0-4; do_open holds both mode tables).  A bare mode
        # word must NOT be parsed as a variable expression - an undeclared
        # variable evaluates to 0 and 0 maps to INPUT, which would silently
        # open every mode as INPUT.  The word is captured as a plain string,
        # exactly like the FOR clause of the second syntax.
        tok = self.peek()
        if (tok is not None and tok[0] == 'name'
                and tok[1].upper() in ('INPUT', 'OUTPUT', 'APPEND',
                                       'RANDOM', 'BINARY')):
            mode = tok[1].upper()
            self.advance()
        else:
            mode = self.parse_expression()
        self.expect_op(',')
        self.match_op('#')
        filenum = self.parse_expression()
        self.expect_op(',')
        filename = self.parse_expression()
        record_len = None
        if self.match_op(','):
            record_len = self.parse_expression()
        return ('open', mode, filenum, filename, record_len)

    def _parse_open_second(self, filename):
        # The FOR keyword has already been consumed by parse_open; the mode
        # word (INPUT/OUTPUT/APPEND/RANDOM/BINARY or I/O/R/A/B) follows.
        tok = self.peek()
        if tok and tok[0] == 'name':
            mode = tok[1].upper()
            self.advance()
        else:
            mode = self.parse_expression()
        if not self.match_keyword('AS'):
            raise BasicError("Expected AS in OPEN")
        self.match_op('#')
        filenum = self.parse_expression()
        record_len = None
        if self.match_keyword('LEN'):
            self.expect_op('=')
            record_len = self.parse_expression()
        return ('open', mode, filenum, filename, record_len)

    def parse_close(self):
        # CLOSE [[#]filenumber[,[#]filenumber]...]
        if self.at_stmt_end():
            return ('close', None)
        nums = []
        while True:
            self.match_op('#')
            nums.append(self.parse_expression())
            if not self.match_op(','):
                break
        return ('close', nums)

    def _graphics_form_of(self, keyword):
        """True when a GET/PUT keyword is used in its graphics form.

        Graphics (manual GET/PUT): GET (x1,y1)-(x2,y2),arr$ / PUT (x,y),arr$ [,[color][,XOR|OR|AND].
        The first argument is a '(' that opens a point or a point range, so a
        peek of '(' after the keyword unambiguously selects the graphics form
        (file GET/PUT always begins with a file number, never '(').
        """
        return (self.peek() is not None and self.peek()[0] == 'op'
                and self.peek()[1] == '(')

    def _point_expr(self):
        """Parse '(x,y)': a parenthesized two-number point (GET/PUT/PSET
        graphics coordinates).  A range expression like (a, b, c, d) is not a
        point and parses as a regular parenthesized expression."""
        self.expect_op('(')
        x = self.parse_expression()
        self.expect_op(',')
        y = self.parse_expression()
        self.expect_op(')')
        return (x, y)

    def parse_get(self):
        if self._graphics_form_of('GET'):
            # GET (x1,y1)-(x2,y2),arr$ (manual GET, graphics)
            x1, y1 = self._point_expr()
            self.expect_op('-')
            x2, y2 = self._point_expr()
            self.expect_op(',')
            var = self.parse_var_or_arr()
            return ('get_graphics', x1, y1, x2, y2, var)
        # GET [#]file number[,record number] - the # is optional.
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '#':
            self.advance()
            filenum = self.parse_expression()
        else:
            tok = self.peek()
            if tok and tok[0] == 'number':
                filenum = self.parse_expression()
            else:
                # Keyboard GET: GET var$
                var = self.parse_var_or_arr()
                return ('get_key', var)
        if self.at_stmt_end():
            # GET #n alone: read the next record into FIELD variables.
            return ('get', filenum, None, None)
        self.expect_op(',')
        remaining = self.stmt_tokens()
        commas = sum(1 for t in remaining if t == ('op', ','))
        if commas >= 1:
            recnum = self.parse_expression()
            self.expect_op(',')
            var = self.parse_var_or_arr()
        else:
            tok = self.peek()
            if tok and tok[0] == 'number':
                # GET #n, recnum  -> read record into FIELD variables
                recnum = self.parse_expression()
                var = None
            else:
                recnum = None
                var = self.parse_var_or_arr()
        return ('get', filenum, recnum, var)

    def parse_put(self):
        if self._graphics_form_of('PUT'):
            # PUT (x,y),arr$ [,[color][,XOR|OR|AND]] (manual PUT, graphics)
            x, y = self._point_expr()
            self.expect_op(',')
            var = self.parse_var_or_arr()
            color = None
            mode = None
            if self.match_op(','):
                color = self.parse_expression()
                if self.match_op(','):
                    tok = self.peek()
                    if tok and tok[0] == 'name' and tok[1].upper() in ('XOR', 'OR', 'AND'):
                        mode = tok[1].upper()
                        self.advance()
                    else:
                        raise BasicError("Expected XOR, OR, or AND in PUT")
            return ('put_graphics', x, y, var, color, mode)
        # PUT [#]file number[,record number] - # and record number optional.
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '#':
            self.advance()
        filenum = self.parse_expression()
        if self.at_stmt_end():
            return ('put', filenum, None, None)
        self.expect_op(',')
        remaining = self.stmt_tokens()
        commas = sum(1 for t in remaining if t == ('op', ','))
        if commas >= 1:
            recnum = self.parse_expression()
            self.expect_op(',')
            data = self.parse_expression()  # var, array, or literal
        else:
            tok = self.peek()
            if tok and tok[0] == 'number':
                # PUT #n, recnum  -> write FIELD variables to record
                recnum = self.parse_expression()
                data = None
            else:
                recnum = None
                data = self.parse_expression()
        return ('put', filenum, recnum, data)

    def parse_seek(self):
        self.expect_op('#')
        filenum = self.parse_expression()
        self.expect_op(',')
        var = self.parse_var_or_arr()
        return ('seek', filenum, var)

    def parse_file_num(self):
        self.match_op('#')
        return self.parse_expression()

    def parse_kill_filename(self):
        # KILL accepts an unquoted filename (e.g. KILL DATA1.BAS) the way
        # LOAD does.  The '.' of an extension is not a token, so a name
        # followed by another name is a dotted filename, and a name
        # followed by '\' is a path.  Anything else is a string
        # expression, as before (KILL "DATA1.BAS", KILL F$).
        tok = self.peek()
        nxt = self.tokens[self.pos + 1] if self.pos + 1 < len(self.tokens) else None
        if not (tok is not None and tok[0] == 'name' and nxt is not None
                and (nxt[0] == 'name'
                     or (nxt[0] == 'op' and nxt[1] == '\\'))):
            return self.parse_expression()
        parts = []
        while not self.at_end():
            t = self.peek()
            if not (t[0] == 'name'
                    or (t[0] == 'op' and t[1] == '\\')):
                break  # end of the filename (e.g. ':' or end of line)
            self.advance()
            if t[0] == 'op':  # '\' path separator
                parts.append('\\')
            else:
                parts.append(t[1])
                if not self.at_end() and self.peek()[0] == 'name':
                    parts.append('.')
        return ('str', ''.join(parts))

    # -- graphics ------------------------------------------------------------ #
    def parse_line(self):
        if self.peek() and self.peek()[0] == 'name' and self.peek()[1].upper() == 'INPUT':
            self.advance()
            if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '#':
                # File LINE INPUT
                self.expect_op('#')
                filenum = self.parse_expression()
                self.expect_op(',')
                var = self.parse_var_or_arr()
                return ('line_input', filenum, var)
            else:
                # Keyboard LINE INPUT [;][prompt string;]string variable
                prompt = None
                if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == ';':
                    self.advance()
                if self.peek() and self.peek()[0] == 'string':
                    prompt = self.parse_expression()
                    self.match_op(';')
                var = self.parse_var_or_arr()
                return ('line_input_key', var, prompt)
        # LINE [(x1,y1)]-(x2,y2) [,[attribute][,B[F]][,style]]
        x1 = None
        y1 = None
        if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
            self.advance()
            x1 = self.parse_expression()
            self.expect_op(',')
            y1 = self.parse_expression()
            self.expect_op(')')
        self.expect_op('-')
        self.expect_op('(')
        x2 = self.parse_expression()
        self.expect_op(',')
        y2 = self.parse_expression()
        self.expect_op(')')
        color = None
        bf = ''
        style = None
        if self.match_op(','):
            # attribute (may be omitted with an empty comma)
            if not (self.at_stmt_end() or (self.peek() and self.peek()[0] == 'op'
                                           and self.peek()[1] == ',')):
                tok = self.peek()
                # Manual LINE: a bare B/BF right after one comma is a syntax
                # error; the attribute must be omitted with a second comma
                # (LINE (x1,y1)-(x2,y2),,B).
                if tok and tok[0] == 'name' and tok[1].upper() in ('B', 'BF'):
                    raise BasicError("Expected ','")
                color = self.parse_expression()
            if self.match_op(','):
                tok = self.peek()
                if tok and tok[0] == 'name':
                    bf = self.advance()[1]
                if self.match_op(','):
                    style = self.parse_expression()
        return ('line', x1, y1, x2, y2, color, bf, style)

    def parse_mouse(self):
        # MOUSE x [, y [, button]] (extension): wait for a mouse click on the
        # graphics window and store its location (and button) in variables.
        var_names = []
        while True:
            tok = self.peek()
            if tok and tok[0] == 'name':
                var_names.append(tok[1])
                self.advance()
                if len(var_names) == 3:
                    break
                if self.match_op(','):
                    continue
                break
            break
        if not var_names:
            raise BasicError("Syntax error")
        return ('mouse', var_names)

    def parse_circle(self):
        # CIRCLE (x,y),r [,[color][,[start][,end][,aspect]]]
        # Empty arguments are allowed (manual example: CIRCLE (160,100),R,,,,5/18).
        self.expect_op('(')
        x = self.parse_expression()
        self.expect_op(',')
        y = self.parse_expression()
        self.expect_op(')')
        self.expect_op(',')
        r = self.parse_expression()
        color = None
        start = None
        end = None
        aspect = None
        if self.match_op(','):
            if not self._empty_param():
                color = self.parse_expression()
            if self.match_op(','):
                if not self._empty_param():
                    start = self.parse_expression()
                if self.match_op(','):
                    if not self._empty_param():
                        end = self.parse_expression()
                    if self.match_op(','):
                        if not self._empty_param():
                            aspect = self.parse_expression()
        return ('circle', x, y, r, color, start, end, aspect)

    def _empty_param(self):
        if self.at_end():
            return True
        tok = self.peek()
        return tok is not None and tok[0] == 'op' and tok[1] in (',', ':')

    def parse_pset(self):
        return self._parse_point_stmt('pset')

    def parse_preset(self):
        return self._parse_point_stmt('preset')

    def _parse_point_stmt(self, tag):
        # (x,y), x,y, or STEP(x,y) - relative to the last referenced point.
        step = False
        tok = self.peek()
        if tok and tok[0] == 'name' and tok[1].upper() == 'STEP':
            self.advance()  # STEP
            self.expect_op('(')
            x = self.parse_expression()
            self.expect_op(',')
            y = self.parse_expression()
            self.expect_op(')')
            step = True
        elif self.match_op('('):
            x = self.parse_expression()
            self.expect_op(',')
            y = self.parse_expression()
            self.expect_op(')')
        else:
            x = self.parse_expression()
            self.expect_op(',')
            y = self.parse_expression()
        color = None
        if self.match_op(','):
            color = self.parse_expression()
        return (tag, x, y, color, step)

    def parse_paint(self):
        # PAINT (x,y) | x,y [,[color][,border]] (manual PAINT).  Empty
        # paint/border arguments are allowed and default (foreground /
        # paint color).
        if self.match_op('('):
            x = self.parse_expression()
            self.expect_op(',')
            y = self.parse_expression()
            self.expect_op(')')
        else:
            x = self.parse_expression()
            self.expect_op(',')
            y = self.parse_expression()
        color = None
        border = None
        bckgrnd = None
        if self.match_op(','):
            if not self._empty_param():
                color = self.parse_expression()
            if self.match_op(','):
                if not self._empty_param():
                    border = self.parse_expression()
            if self.match_op(','):
                if not self._empty_param():
                    bckgrnd = self.parse_expression()
        return ('paint', x, y, color, border, bckgrnd)

    def parse_palette(self):
        # PALETTE [attribute,color] | PALETTE first,last,color | PALETTE
        # USING arrayname, index (manual PALETTE).  No arguments resets the
        # palette to its initial setting.
        if self.match_keyword('USING'):
            tok = self.peek()
            if tok is None or tok[0] != 'name':
                raise BasicError("Expected array name in PALETTE USING")
            arr = tok[1]
            self.advance()
            self.expect_op(',')
            index = self.parse_expression()
            return ('palette_using', arr, index)
        if self.at_stmt_end():
            return ('palette', None)
        first = self.parse_expression()
        if not self.match_op(','):
            return ('palette', (first,))
        second = self.parse_expression()
        if self.match_op(','):
            third = self.parse_expression()
            return ('palette', (first, second, third))
        return ('palette', (first, second))

    def parse_color(self):
        # COLOR [foreground][,[background][,border]] - "COLOR ,n" selects
        # the palette in SCREEN 1 (empty foreground).
        if self.at_stmt_end():
            return ('color', None, None, None)
        fg = None
        if not (self.peek() and self.peek()[0] == 'op' and self.peek()[1] == ','):
            fg = self.parse_expression()
        bg = None
        if self.match_op(','):
            if not (self.at_stmt_end() or (self.peek() and self.peek()[0] == 'op'
                                           and self.peek()[1] == ',')):
                bg = self.parse_expression()
        border = None
        if self.match_op(','):
            if not self.at_stmt_end():
                border = self.parse_expression()
        return ('color', fg, bg, border)

    def parse_ink(self):
        n = self.parse_expression()
        color = None
        if self.match_op(','):
            color = self.parse_expression()
        return ('ink', n, color)

    def parse_screen(self):
        # SCREEN [mode] [,[colorswitch]][,[apage]][,[vpage]]
        mode = self.parse_expression()
        color = None
        apage = None
        vpage = None
        if self.match_op(','):
            if not self._empty_param():
                color = self.parse_expression()
            if self.match_op(','):
                if not self._empty_param():
                    apage = self.parse_expression()
                if self.match_op(','):
                    if not self._empty_param():
                        vpage = self.parse_expression()
        return ('screen', mode, color, apage, vpage)

    def parse_screensize(self):
        # SCREENSIZE [x [, y]] | SCREENSIZE FULLSCREEN.
        #
        # SCREENSIZE x [, y] opens a custom-size graphics window x pixels
        # wide and y pixels tall (a single argument gives a square window).
        # Unlike SCREEN (which selects a fixed hardware mode), SCREENSIZE
        # lets the caller choose any size, so no screen-mode numbers need
        # remembering.  The size is optional so that a plain "SCREENSIZE"
        # (e.g. a direct replacement for "SCREEN 7") still opens a window
        # instead of being a syntax error: with no arguments it defaults to
        # the classic 320x200 graphics size.
        #
        # SCREENSIZE FULLSCREEN opens the window maximized to fill the
        # screen; the interpreter determines the actual size (the screen
        # size) rather than the caller, and XSZ()/YSZ() report it.
        if self.at_stmt_end():
            return ('screensize', None, None, False)
        if self.match_keyword('FULLSCREEN'):
            if not self.at_stmt_end():
                raise BasicError("Expected end of statement")
            return ('screensize', None, None, True)
        width = self.parse_expression()
        if self.match_op(','):
            height = self.parse_expression()
        else:
            height = width  # one argument -> square window
        return ('screensize', width, height, False)

    def parse_textsize(self):
        # TEXTSIZE x - the size, in pixels, of a text character cell on the
        # monitor (the window).  x is a positive integer expression; the
        # fixed 8x8 glyph is scaled to an x-by-x pixel cell, so larger x
        # gives bigger, more readable text.  A bare TEXTSIZE (no argument)
        # is a no-op that just resets to the authentic 8-pixel cell.
        if self.at_stmt_end():
            return ('textsize', None)
        size = self.parse_expression()
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('textsize', size)

    def parse_textrotate(self):
        # TEXTRotate x - rotate the lines of text drawn from now on by x
        # degrees (an integer 0-359) clockwise, each line as a rigid whole
        # about its pivot (the cursor at the line's start).  A bare
        # TEXTRotate (no argument) resets to upright (0).  The range is
        # validated at execution (Screen.textrotate).
        if self.at_stmt_end():
            return ('textrotate', None)
        degrees = self.parse_expression()
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('textrotate', degrees)

    def parse_textfont(self):
        # TEXTFONT [font][, [bold][, [italic]]] - choose the face the
        # monitor text is drawn in.  All three arguments are optional and
        # positional; each omitted argument takes its per-slot default
        # (Arial, not bold, not italic), so e.g. TEXTFONT ,,I is Arial
        # regular italic and TEXTFONT ,B is Arial bold.  The arguments are
        # raw WORD names (not expressions); validation of the face and the
        # weight flags happens at execution in Screen.textfont, which
        # raises "Illegal function call" for anything it does not
        # recognise.
        if self.at_stmt_end():
            return ('textfont', None, None, None)
        def _arg():
            tok = self.peek()
            if tok is None or (tok[0] == 'op' and tok[1] in (',', ':')):
                return None
            if tok[0] != 'name':
                raise BasicError("Expected a font or weight name")
            self.advance()
            return tok[1]
        font = _arg()
        bold = None
        italic = None
        if self.match_op(','):
            bold = _arg()
            if self.match_op(','):
                italic = _arg()
        if not self.at_stmt_end():
            raise BasicError("Expected end of statement")
        return ('textfont', font, bold, italic)

    def parse_view(self):
        # VIEW [[SCREEN][(x1,y1)-(x2,y2)]] - bare VIEW disables the viewport.
        # The SCREEN flag means absolute plotting (manual VIEW).
        if self.at_stmt_end():
            return ('view', None, None, None, None, False)
        screen_abs = False
        if self.peek() and self.peek()[0] == 'name' and self.peek()[1].upper() == 'SCREEN':
            self.advance()
            screen_abs = True
        self.expect_op('(')
        x1 = self.parse_expression()
        self.expect_op(',')
        y1 = self.parse_expression()
        self.expect_op(')')
        self.expect_op('-')
        self.expect_op('(')
        x2 = self.parse_expression()
        self.expect_op(',')
        y2 = self.parse_expression()
        self.expect_op(')')
        return ('view', x1, y1, x2, y2, screen_abs)

    def parse_window(self):
        # WINDOW [[SCREEN](x1,y1)-(x2,y2)] (manual WINDOW).  With no arguments
        # it disables any previous world-coordinate mapping (returns the screen
        # to normal physical coordinates).  With arguments it defines a world
        # coordinate space: without SCREEN the y-axis is inverted (Cartesian,
        # lower-left origin); with SCREEN it is not inverted (upper-left
        # origin).  Coordinates are sorted into ascending order.
        if self.at_stmt_end():
            return ('window', None, None, None, None, False)
        screen_abs = False
        if self.peek() and self.peek()[0] == 'name' and self.peek()[1].upper() == 'SCREEN':
            self.advance()
            screen_abs = True
        self.expect_op('(')
        x1 = self.parse_expression()
        self.expect_op(',')
        y1 = self.parse_expression()
        self.expect_op(')')
        self.expect_op('-')
        self.expect_op('(')
        x2 = self.parse_expression()
        self.expect_op(',')
        y2 = self.parse_expression()
        self.expect_op(')')
        return ('window', x1, y1, x2, y2, screen_abs)

    # -- memory / system ----------------------------------------------------- #
    def parse_bload(self):
        # BLOAD filename[,offset] (manual) or filename, mode, offset (ext).
        filename = self.parse_expression()
        mode = None
        start = None
        if self.match_op(','):
            first = self.parse_expression()
            if self.match_op(','):
                mode = first
                start = self.parse_expression()
            else:
                start = first
        return ('bload', filename, mode, start)

    def parse_bsave(self):
        # BSAVE filename,offset,length - offset and length are required.
        filename = self.parse_expression()
        self.expect_op(',')
        start = self.parse_expression()
        self.expect_op(',')
        length = self.parse_expression()
        return ('bsave', filename, start, length)

    def parse_out(self):
        port = self.parse_expression()
        self.expect_op(',')
        val = self.parse_expression()
        return ('out', port, val)

    def parse_poke(self):
        # POKE a,b [,c,d ...] (manual POKE): one or more address,value
        # pairs.
        pairs = []
        while True:
            addr = self.parse_expression()
            self.expect_op(',')
            val = self.parse_expression()
            pairs.append((addr, val))
            if not self.match_op(','):
                break
        return ('poke', pairs)

    def parse_key(self):
        # KEY n, "string" | KEY(n), "string" | KEY(n) ON|OFF|STOP
        # | KEY ON | KEY OFF | KEY LIST
        tok = self.peek()
        if tok and tok[0] == 'name':
            kw = tok[1].upper()
            if kw == 'ON':
                self.advance()
                return ('key_on',)
            if kw == 'OFF':
                self.advance()
                return ('key_off',)
            if kw == 'LIST':
                self.advance()
                return ('key_list',)
        if tok and tok[0] == 'op' and tok[1] == '(':
            # KEY(n) ON | OFF | STOP: control the trap for key n (manual
            # ON KEY(n) / KEY(n)).
            self.advance()
            n = self.parse_expression()
            self.expect_op(')')
            if self.match_op(','):
                # KEY(n), expr: parenthesized definition form (manual KEY:
                # KEY(n),CHR$[hex code]+CHR$[scan code] defines keys 15-20).
                s = self.parse_expression()
                return ('key', n, s)
            tok = self.peek()
            if tok and tok[0] == 'name':
                kw = tok[1].upper()
                if kw == 'ON':
                    self.advance()
                    return ('key_state', n, 'on')
                if kw == 'OFF':
                    self.advance()
                    return ('key_state', n, 'off')
                if kw == 'STOP':
                    self.advance()
                    return ('key_state', n, 'stop')
            raise BasicError("Expected ON, OFF, or STOP after KEY(n)")
        n = self.parse_expression()
        self.expect_op(',')
        s = self.parse_expression()
        return ('key', n, s)

    def parse_optional_expr(self):
        if self.at_stmt_end():
            return None
        return self.parse_expression()

    # -- control flow / data ------------------------------------------------- #
    def parse_do(self):
        cond = None
        if not self.at_end():
            if self.match_keyword('WHILE'):
                cond = ('while', self.parse_expression())
            elif self.match_keyword('UNTIL'):
                cond = ('until', self.parse_expression())
        return ('do', cond)

    def parse_loop(self):
        cond = None
        if not self.at_end():
            if self.match_keyword('WHILE'):
                cond = ('while', self.parse_expression())
            elif self.match_keyword('UNTIL'):
                cond = ('until', self.parse_expression())
        return ('loop', cond)

    def parse_option(self):
        if not self.match_keyword('BASE'):
            raise BasicError("Expected BASE")
        base = self.parse_expression()
        return ('option', base)

    def parse_type(self):
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected type name")
        name = tok[1]
        self.advance()
        fields = []
        if self.match_op('('):
            while True:
                ftok = self.peek()
                if ftok is None or ftok[0] != 'name':
                    break
                fname = ftok[1]
                self.advance()
                ftype = 'SINGLE'
                if self.match_keyword('AS'):
                    ttok = self.peek()
                    if ttok and ttok[0] == 'name':
                        ftype = self.advance()[1]
                flen = None
                if self.peek() and self.peek()[0] == 'op' and self.peek()[1] == '(':
                    self.advance()
                    flen = self.parse_expression()
                    self.expect_op(')')
                fields.append((fname, ftype, flen))
                if self.match_op(','):
                    continue
                break
            self.expect_op(')')
        return ('type', name, fields)

    def parse_field(self):
        # FIELD [#] filenum, num AS stringvar [,num AS stringvar]...
        # (manual) - each number is a field width; fields are contiguous
        # starting at position 1.  Also accepts the legacy single-field form
        # "FIELD #n, pos, width AS var".
        self.match_op('#')
        filenum = self.parse_expression()
        self.expect_op(',')
        first_num = self.parse_expression()
        if self.match_keyword('AS'):
            fields = []
            var = self.parse_var_or_arr()
            fields.append((first_num, var))
            while self.match_op(','):
                num = self.parse_expression()
                if not self.match_keyword('AS'):
                    raise BasicError("Expected AS in FIELD")
                var = self.parse_var_or_arr()
                fields.append((num, var))
            return ('field', filenum, fields)
        # Legacy single-field form: pos, width AS var.
        self.expect_op(',')
        width = self.parse_expression()
        if not self.match_keyword('AS'):
            raise BasicError("Expected AS in FIELD")
        var = self.parse_var_or_arr()
        return ('field_old', filenum, first_num, width, var)

    def parse_redim(self):
        # GW-BASIC: REDIM [PRESERVE] name(dims)
        preserve = False
        if self.match_keyword('PRESERVE'):
            preserve = True
        tok = self.peek()
        if tok is None or tok[0] != 'name':
            raise BasicError("Expected array name in REDIM")
        name = tok[1]
        self.advance()
        self.expect_op('(')
        dims = []
        while True:
            dims.append(self.parse_expression())
            if self.match_op(','):
                continue
            break
        self.expect_op(')')
        return ('redim', name, dims, preserve)

    def parse_write(self):
        filenum = None
        if self.match_op('#'):
            filenum = self.parse_expression()
            self.expect_op(',')
        items = []
        while not self.at_stmt_end():
            items.append(self.parse_expression())
            if self.match_op(','):
                continue
            if self.match_op(';'):
                continue
            break
        return ('write', filenum, items)

    # -- expressions --------------------------------------------------------- #
    def parse_expression(self):
        return self.parse_imp()

    # Logical-operator precedence (manual Ch 6.4.3, Table 6.2 - "The
    # operators are listed in order of precedence"):  NOT > AND > OR > XOR > EQV > IMP
    # Each operator gets its own level, so e.g.
    #   1 AND 3 XOR 1 AND 2  groups as  (1 AND 3) XOR (1 AND 2)
    # and NOT binds tightest of all (parse_not is the innermost operand).
    def parse_imp(self):
        left = self.parse_eqv()
        while self.match_keyword('IMP'):
            right = self.parse_eqv()
            left = ('binop', 'IMP', left, right)
        return left

    def parse_eqv(self):
        left = self.parse_xor()
        while self.match_keyword('EQV'):
            right = self.parse_xor()
            left = ('binop', 'EQV', left, right)
        return left

    def parse_xor(self):
        left = self.parse_or()
        while self.match_keyword('XOR'):
            right = self.parse_or()
            left = ('binop', 'XOR', left, right)
        return left

    def parse_or(self):
        left = self.parse_and()
        while self.match_keyword('OR'):
            right = self.parse_and()
            left = ('binop', 'OR', left, right)
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.match_keyword('AND'):
            right = self.parse_not()
            left = ('binop', 'AND', left, right)
        return left

    def parse_not(self):
        if self.match_keyword('NOT'):
            return ('unop', 'NOT', self.parse_not())
        return self.parse_relational()

    def parse_relational(self):
        left = self.parse_additive()
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] in ('=', '<', '>', '<=', '>=', '<>'):
            op = self.advance()[1]
            right = self.parse_additive()
            return ('binop', op, left, right)
        return left

    def parse_additive(self):
        left = self.parse_term()
        while True:
            tok = self.peek()
            if tok and tok[0] == 'op' and tok[1] in ('+', '-', '&'):
                op = self.advance()[1]
                right = self.parse_term()
                left = ('binop', op, left, right)
            else:
                break
        return left

    def parse_term(self):
        left = self.parse_intdiv()
        while True:
            tok = self.peek()
            if tok and tok[0] == 'op' and tok[1] in ('*', '/'):
                op = self.advance()[1]
                right = self.parse_intdiv()
                left = ('binop', op, left, right)
            else:
                break
        return left

    def parse_intdiv(self):
        left = self.parse_unary()
        while True:
            tok = self.peek()
            if tok and tok[0] == 'op' and tok[1] == '\\':
                self.advance()
                right = self.parse_unary()
                left = ('binop', '\\', left, right)
            elif self.match_keyword('MOD'):
                right = self.parse_unary()
                left = ('binop', 'MOD', left, right)
            else:
                break
        return left

    def parse_unary(self):
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] in ('-', '+'):
            op = self.advance()[1]
            return ('unop', op, self.parse_unary())
        return self.parse_power()

    def parse_power(self):
        # '^' is right-associative in GW-BASIC: 2^3^2 == 2^(3^2) == 512,
        # not (2^3)^2 == 64 (manual Ch. 6: X^(Y^Z) - a power tower is read
        # right-to-left). The exponent is parsed recursively so any further
        # '^' binds to its own exponent.
        base = self.parse_primary()
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] == '^':
            self.advance()
            exponent = self.parse_exponent_operand()
            base = ('binop', '^', base, exponent)
        return base

    def parse_exponent_operand(self):
        # The right-hand side of '^' accepts a single primary, with an
        # optional leading unary sign (GW-BASIC allows X^-2 even though
        # negation has lower precedence than '^' - manual 6.4.1). If the
        # (signed) primary is itself followed by '^', the chain continues
        # right-associatively: X^Y^Z parses as X^(Y^Z).
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] in ('-', '+'):
            op = self.advance()[1]
            base = ('unop', op, self.parse_primary())
        else:
            base = self.parse_primary()
        tok = self.peek()
        if tok and tok[0] == 'op' and tok[1] == '^':
            self.advance()
            base = ('binop', '^', base, self.parse_exponent_operand())
        return base

    def parse_primary(self):
        tok = self.peek()
        if tok is None:
            raise BasicError("Unexpected end of expression")
        if tok[0] == 'number':
            self.advance()
            return ('num', parse_number(tok[1]), classify_number(tok[1]))
        if tok[0] == 'string':
            self.advance()
            return ('str', tok[1])
        if tok[0] == 'name':
            name = tok[1]
            if name.upper() == 'IF':
                # IF condition THEN expression ELSE expression - the
                # conditional expression.  IF is reserved, so an IF here
                # can never be a variable; treating it as one silently
                # evaluates the whole expression to 0 (and drops the rest
                # of the line).  ELSE is mandatory in the expression form;
                # a missing THEN/ELSE is a syntax error, not a silent 0.
                self.advance()  # IF
                cond = self.parse_expression()
                if not self.match_keyword('THEN'):
                    raise BasicError("Expected THEN in IF expression")
                then_expr = self.parse_expression()
                if not self.match_keyword('ELSE'):
                    raise BasicError("Expected ELSE in IF expression")
                else_expr = self.parse_expression()
                return ('ifexp', cond, then_expr, else_expr)
            nxt = self.tokens[self.pos + 1] if self.pos + 1 < len(self.tokens) else None
            if nxt and nxt[0] == 'op' and nxt[1] == '(' and name.upper() in ('INPUT$', 'VARPTR', 'VARPTR$'):
                # INPUT$(n[, [#]f]), VARPTR(var | #f) and VARPTR$(var | #f):
                # the '#' file-number form is not a normal expression, so it
                # is captured here (VARPTR$ only allows the variable form;
                # the #f form is rejected at evaluation time).
                self.advance()  # name
                self.advance()  # (
                args = self._parse_special_call_args(name.upper())
                self.expect_op(')')
                return ('call', name, args)
            if nxt and nxt[0] == 'op' and nxt[1] == '(': 
                # Function call OR array reference (disambiguated at runtime).
                self.advance()  # name
                self.advance()  # (
                args = []
                if not (self.peek() and self.peek()[0] == 'op' and self.peek()[1] == ')'):
                    while True:
                        args.append(self.parse_expression())
                        if self.match_op(','):
                            continue
                        break
                self.expect_op(')')
                return ('call', name, args)
            self.advance()
            return ('var', name)
        if tok[0] == 'op' and tok[1] == '(':
            self.advance()
            expr = self.parse_expression()
            self.expect_op(')')
            return expr
        raise BasicError("Unexpected token in expression: %s" % (tok,))

    def _parse_special_call_args(self, uname):
        """Parse arguments for INPUT$(n[, [#]f]) and VARPTR(var | #f).

        The '#' file-number form is not a normal expression, so it is
        captured here: INPUT$ takes the file number as a plain value, while
        VARPTR(#f) is represented as an ('fnum', expr) node.
        """
        if uname == 'INPUT$':
            args = [self.parse_expression()]
            if self.match_op(','):
                self.match_op('#')  # optional # before the file number
                args.append(self.parse_expression())
            return args
        # VARPTR / VARPTR$: a variable/array, or #file number (FCB address
        # for VARPTR; VARPTR$ rejects it when evaluated).
        if self.match_op('#'):
            return [('fnum', self.parse_expression())]
        return [self.parse_expression()]


def _split_top_level_stmts(tokens):
    """Split a token list into per-statement groups, honouring IF.

    An IF statement consumes the rest of the (concatenated) token stream:
    its THEN/ELSE clause may contain colons that do NOT separate top-level
    statements (e.g. "IF X=1 THEN A=2: B=3" is one IF, not two).  The caller
    must therefore pass a token list where every statement after the first
    IF on the line is already logically part of that IF.
    """
    statements = []
    current = []
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        if tok[0] == 'name' and tok[1].upper() == 'IF' and not current:
            current.extend(tokens[i:])
            break
        if tok == ('op', ':'):
            if current:
                statements.append(current)
            current = []
            i += 1
            continue
        current.append(tok)
        i += 1
    if current:
        statements.append(current)
    return statements


def parse_statement_group(tokens):
    """Parse one top-level statement (plus any colon-separated tail on the
    same line) from a token list.  Returns a list of statement AST nodes.

    This is the shared workhorse used both by parse_program_line (single
    line) and by the multi-line IF/THEN/ELSE continuation loader.  It is
    deliberately line-agnostic: the caller is responsible for deciding how
    many source lines' worth of tokens to pass in.
    """
    parsed = []
    for stmt_tokens in _split_top_level_stmts(tokens):
        if not stmt_tokens:
            continue
        parser = Parser(stmt_tokens, None)
        stmt = parser.parse_statement()
        if stmt is not None:
            parsed.append(stmt)
        # A single-line IF whose THEN/ELSE clause is a line number ends at
        # that line number; any colon-separated statements after it on the
        # same line are separate, unconditional statements (the common
        # idiom "IF A THEN 20: GOTO 30").
        if stmt is not None and stmt[0] == 'if' and not parser.at_end():
            while not parser.at_end():
                if parser.peek() == ('op', ':'):
                    parser.advance()
                    continue
                rest = parser.parse_statement()
                if rest is not None:
                    parsed.append(rest)
    return parsed


def parse_statement_with_continuation(first_text, follow_texts):
    """Parse a possibly-multi-line IF statement that starts on `first_text`
    and continues onto the lines in `follow_texts` (in source order).

    Returns (stmts, num_consumed, needs_more):
      stmts        -- list of statement AST nodes for the completed IF (the
                      IF plus any trailing colon-separated statements on its
                      final line).  Empty when the statement is incomplete.
      num_consumed -- how many lines of follow_texts were absorbed into the
                      IF (0 when it completed on the first line).
      needs_more   -- True when the IF is not yet complete (it ended on a
                      line with no THEN/ELSE yet) and more input is needed;
                      the caller supplies additional lines and calls again.

    A non-IF first line is parsed normally and reported as complete with
    zero lines consumed.
    """
    first_tokens = tokenize(first_text)
    # Locate the first IF token; anything before it is a separate statement
    # (e.g. "A=1 : IF A" — though that is unusual, handle it generally).
    if_start = None
    for i, tok in enumerate(first_tokens):
        if tok[0] == 'name' and tok[1].upper() == 'IF':
            if_start = i
            break
    if if_start is None:
        return (parse_statement_group(first_tokens), 0, False)

    pre = first_tokens[:if_start]
    lead = parse_statement_group(pre) if pre else []
    base = list(first_tokens[if_start:])  # IF + rest of its line

    def attempt(toks):
        """Parse the IF from `toks`.  Returns (stmt, tail, error) where tail
        is the list of tokens left over after the IF (its trailing
        colon-separated statements) and error is a BasicError if the IF could
        not be parsed at all (incomplete or malformed)."""
        parser = Parser(toks, None)
        try:
            stmt = parser.parse_statement()
        except BasicError as e:
            return (None, None, e)
        tail = []
        if stmt is not None and not parser.at_end():
            if parser.peek() == ('op', ':'):
                tail = toks[parser.pos:]
            # A non-colon leftover means the IF is not actually complete
            # (e.g. "IF A" then a stray token): treat as incomplete.
            elif not parser.at_end():
                return (None, None, BasicError("incomplete IF"))
        return (stmt, tail, None)

    consumed = 0
    while True:
        toks = base if consumed == 0 else base + _flatten_follow(follow_texts, consumed)
        stmt, tail, err = attempt(toks)
        if err is None and stmt is not None:
            out = list(lead)
            out.append(stmt)
            if tail:
                # Trailing colon-separated statements on the IF's final line
                # (the "IF A THEN 20: GOTO 30" idiom).
                out.extend(parse_statement_group(tail))
            return (out, consumed, False)
        # Incomplete or error: need the next line.
        if consumed < len(follow_texts):
            consumed += 1
            continue
        return ([], consumed, True)


def _flatten_follow(follow_texts, n):
    """Concatenate the tokens of follow_texts[:n]."""
    toks = []
    for t in follow_texts[:n]:
        toks.extend(tokenize(t))
    return toks


_CLAUSE_KEYWORDS = {'THEN', 'ELSE', 'GOTO', 'GOSUB', 'IF'}


def _is_bare_if_expression(text):
    """True when `text` is a standalone, incomplete IF: it begins with an IF
    keyword followed by an expression, and contains no THEN/ELSE/GOTO clause
    keyword or statement separator on the line.  Such a line is the first
    line of a multi-line IF whose THEN/ELSE sit on later lines.

    This is deliberately conservative: any line that already carries a clause
    keyword, a colon, or that does not start with IF is left to the normal
    single-line parser, so existing behaviour is preserved.
    """
    try:
        toks = tokenize(text)
    except BasicError:
        # Malformed (e.g. an unterminated string): not a bare IF line.
        # The caller's own guarded parse reports the real syntax error.
        return False
    if not toks or toks[0] != ('name', 'IF'):
        return False
    for tok in toks[1:]:
        ttype, val = tok[0], tok[1]
        if ttype == 'op' and val == ':':
            return False
        if ttype == 'name' and val.upper() in _CLAUSE_KEYWORDS:
            return False
    return True


def _is_bare_if_comma(text):
    """True when `text` is an incomplete IF that ends with the optional comma
    before THEN (e.g. "IF A > 3 ,"): it starts with IF, has no clause keyword
    or colon, and its final token is a comma.  The THEN/ELSE then sit on the
    following line(s)."""
    try:
        toks = tokenize(text)
    except BasicError:
        # Malformed (e.g. an unterminated string): not a bare IF line.
        # The caller's own guarded parse reports the real syntax error.
        return False
    if not toks or toks[0] != ('name', 'IF') or toks[-1] != ('op', ','):
        return False
    for tok in toks[1:-1]:
        ttype, val = tok[0], tok[1]
        if ttype == 'op' and val == ':':
            return False
        if ttype == 'name' and val.upper() in _CLAUSE_KEYWORDS:
            return False
    return True


def parse_program_line(line):
    """Parse one BASIC source line into a list of statement AST nodes."""
    return parse_statement_group(tokenize(line))


def _iter_logical_lines(filename):
    """Yield (line_number, text) pairs for a saved .BAS program file.

    A line too long for one physical line is saved by GW-BASIC (manual
    SAVE) with its line number repeated on the following physical
    line(s); consecutive fragments with the same line number are
    concatenated with no separator (the file stores the original line
    text split at a character boundary), so the caller sees the complete
    logical line.  Physical lines without a leading line number are not
    program lines and are skipped.
    """
    with open(filename, 'r') as f:
        cur = None
        for raw in f:
            raw = raw.strip()
            if not raw:
                continue
            parts = raw.split(None, 1)
            if not parts or not parts[0].isdigit():
                if cur is not None:
                    yield cur
                    cur = None
                continue
            ln = int(parts[0])
            rest = parts[1] if len(parts) > 1 else ''
            if cur is not None and ln == cur[0]:
                # Continuation fragment of the previous physical line.
                cur = (ln, cur[1] + rest)
            else:
                if cur is not None:
                    yield cur
                cur = (ln, rest)
        if cur is not None:
            yield cur


# --------------------------------------------------------------------------- #
#  Interpreter
# --------------------------------------------------------------------------- #
class CaseInsensitiveDict(dict):
    """A dict with case-insensitive string keys.

    GW-BASIC variable and array names are case-insensitive (X, x and X$ all
    refer to the same variable). Keys are stored in canonical upper-case form
    so that lookups, membership tests, get/pop and iteration all compare
    case-insensitively.
    """

    @staticmethod
    def _key(key):
        # Fast path: an all-caps name is unchanged by upper() (the common
        # case), so avoid the allocation.
        if isinstance(key, str):
            return key if key.isupper() else key.upper()
        return key

    def __setitem__(self, key, value):
        super().__setitem__(self._key(key), value)

    def __getitem__(self, key):
        return super().__getitem__(self._key(key))

    def __delitem__(self, key):
        super().__delitem__(self._key(key))

    def __contains__(self, key):
        return super().__contains__(self._key(key))

    def get(self, key, default=None):
        return super().get(self._key(key), default)

    def pop(self, key, *args):
        return super().pop(self._key(key), *args)

    def setdefault(self, key, default=None):
        return super().setdefault(self._key(key), default)

    def __repr__(self):
        return '%s(%r)' % (type(self).__name__, dict(self))


# Default F1-F10 key assignments (manual KEY: "Initially, the function keys
# are assigned the following special functions").  Redefine with
# KEY n, "string"; the null string disables the key (INKEY$ then reports
# CHR$(0)+CHR$(scan code)).
DEFAULT_KEY_DEFS = {
    1: 'LIST', 2: 'RUN' + chr(13), 3: 'LOAD"', 4: 'SAVE"',
    5: 'CONT' + chr(13), 6: '",LPT1:"', 7: 'TRON' + chr(13),
    8: 'TROFF' + chr(13), 9: 'KEY', 10: 'SCREEN 000' + chr(13),
}


class Interpreter:
    def __init__(self, program, output_func=None, input_func=None, gui=False):
        self.program = program
        self.source = {}  # line number -> source text (set by the REPL for TRACE display)
        self.lines = sorted(program.keys())
        self.next_line_map = self._build_next_line_map()
        self.output_func = output_func if output_func is not None else sys.stdout.write
        self.input_func = input_func if input_func is not None else input

        self.vars = CaseInsensitiveDict()
        self.arrays = CaseInsensitiveDict()
        self.array_dims = CaseInsensitiveDict()
        # MUSICFILE/PLAYMUSIC: the music table, (NAME, index tuple) -> .wav
        # path.  Lives as long as the interpreter does: cleared by NEW
        # (a fresh Interpreter), kept across RUNs (a program re-binds its
        # own handles at start; immediate-mode bindings survive for the
        # convenience of testing at the Ok prompt).
        self.music = {}
        self.data = []
        self.data_ptr = 0
        self.gosub_stack = []
        # (steps, line, stmt_idx) of an IF action continuation a RETURN is
        # about to resume; consumed at the top of _step_line.
        self._resume_actions = None
        self.for_stack = []
        self.while_stack = []
        self.def_fns = {}
        self._def_fn_active = set()
        self.error_handler = None
        self.error_line = None
        self._in_error_handler = False
        self._resume_suppress = False
        self._trapped_error = None
        self.skip_else_stack = []
        self.pc = None
        self.trace = False      # TRACE ON: display executed lines at a rate
        self.trace_rate = None  # seconds between trace displays (1 / lines per second)
        self.trace_lps = None   # TRACE ON <rate>: lines per second (int) - the PAUSE batch size
        self.trace_pause = False  # TRACE ON <rate> PAUSE: hold after every <rate> traced lines
        self._trace_pause_count = 0  # traced lines left until the next PAUSE
        self._stopped = False   # True while halted by STOP/break/trace
        self._running = False   # True while _run_loop is executing
        self.random = random.Random()
        self._last_rnd = 0
        # The screen always starts virtual (headless); the graphics window is
        # created lazily the moment the program executes a graphics SCREEN
        # command (see Screen.set_mode -> _ensure_gui -> render).  echo=True
        # mirrors text output to the console so a program's PRINT output is
        # visible next to the graphics window too.  gui=False (--nogui) keeps
        # it headless even when the program selects a graphics mode.
        self.screen = Screen(virtual=True, echo=True, gui_allowed=gui)
        self.files = FileIO()
        self.system = System()
        self.system._screen = self.screen  # the window's keyboard feeds the
        # system key queue too (see System.pump_key_events / get)
        self._io = None  # the I/O middle layer (IoDevice); see the io
                         # property.  The REPL replaces it with one it owns
                         # so interpreter messages route the same way.
        self.option_base = 0
        self.def_types = {}
        self.types = {}
        self.do_stack = []
        self.fields = {}
        self.last_point = None  # last point referenced by LINE (manual LINE)
        self.date_str = time.strftime('%m-%d-%Y')
        self.time_str = time.strftime('%H:%M:%S')
        # Manual KEY / ON KEY: per-run key definitions (F1-F10 expansion
        # strings; keys 15-20 as (hex mask, scan code) pairs) and event
        # traps.
        self.key_defs = dict(DEFAULT_KEY_DEFS)
        self.key_traps = {}
        # TRAP ON|OFF (extension): when False the runtime value-safety
        # checks are bypassed for speed (overflow guard + ON KEY/COM trap
        # polling).  Default True = full checking (cbasic.py behavior).
        self._trap = True
        # True while run_immediate() is executing (direct mode: no event
        # trapping, manual ON COM/KEY).
        self._immediate_mode = False
        self.build_data_pool()

    # -- setup --------------------------------------------------------------- #
    def _build_next_line_map(self):
        m = {}
        for i, line in enumerate(self.lines):
            m[line] = self.lines[i + 1] if i + 1 < len(self.lines) else None
        return m

    def build_data_pool(self):
        self.data = []
        self.data_line_map = {}
        for line in self.lines:
            for stmt in self.program[line]:
                if stmt[0] == 'data':
                    if line not in self.data_line_map:
                        self.data_line_map[line] = len(self.data)
                    self.data.extend(stmt[1])
        self.data_ptr = 0

    def reset_state(self):
        """Re-initialize all state before a RUN.

        Every RUN starts from a clean slate, like a freshly started
        interpreter: scalar variables and array elements read as 0/""
        again, DIM bounds are dropped (the program's DIM statements
        re-establish them), and DEF FN / DEFxxx / OPTION BASE / TYPE
        declarations plus the ON ERROR GOTO handler and the execution
        stacks are cleared (the program re-executes them if present).
        """
        self.vars = CaseInsensitiveDict()
        self.arrays = CaseInsensitiveDict()
        self.array_dims = CaseInsensitiveDict()
        self.data_ptr = 0
        self.def_fns = {}
        self.def_types = {}
        self.types = {}
        self.fields = {}
        self.option_base = 0
        self._def_fn_active = set()
        self.error_handler = None
        self.error_line = None
        self._in_error_handler = False
        self._resume_suppress = False
        self._trapped_error = None
        self.gosub_stack = []
        self._resume_actions = None
        self.for_stack = []
        self.while_stack = []
        self.do_stack = []
        self.skip_else_stack = []
        # Manual KEY / ON KEY: key definitions and event traps are per-run.
        self.key_defs = dict(DEFAULT_KEY_DEFS)
        self.key_traps = {}
        # TRAP state is per-run (a fresh RUN starts fully checking).
        self._trap = True
        self.last_point = None
        # Manual DRAW: the current graphics position defaults to the center
        # of the screen when a program is run, so a previous run's last
        # PSET/LINE point must not leak into the new run.
        self.screen.last_point = None
        self.screen._draw_scale = 1.0
        self.screen._draw_color = self.screen.fg
        self.screen._draw_angle = 0
        self.screen._draw_turn = 0.0
        self.screen._interp = self
        self.screen._stop_requested = False
        self.screen._close_requested = False
        self.screen._close_pending = False
        self.screen._interrupt = False
        self.screen._paint_due = False
        # Each RUN starts with a fixed-size window; a previous run's
        # SCREENSIZE FULLSCREEN must not carry over.
        self.screen._fullscreen = False
        # Manual WINDOW: RUN, SCREEN, and WINDOW with no arguments disable
        # any WINDOW definition (the screen returns to physical
        # coordinates), so a previous run's world mapping must not
        # carry over.
        self.screen.window_rect = None
        self.screen.window_screen = False
        # Start each run with a clean SETFPS pacing burst (the cap itself is
        # preserved - it is a screen-level setting, not per-run state).
        self.screen._fps_base = None
        self.screen._fps_count = 0
        # A fresh program starts with the default monitor text settings:
        # TEXTSIZE TEXTSIZE_DEFAULT, upright text (TEXTRotate 0) and the
        # default TEXTFONT face (Arial, not bold, not italic).  The fields
        # are set directly rather than through textsize()/textrotate()/
        # textfont(), whose repaint and pivot side effects are unwanted
        # mid-reset.
        self.screen.cell = TEXTSIZE_DEFAULT
        self.screen.text_rotate = 0
        self.screen.text_font = TEXTFONT_DEFAULT
        # The face and cell may have changed: drop every font and glyph
        # cached from the previous run so the new run renders from the
        # defaults (the glyph caches are keyed by (cell, char, angle) and
        # do not include the face).
        self.screen._font = None
        self.screen._use_font = False
        self.screen._font_cache = {}
        self.screen._mask_cache.clear()
        self.screen._cov_cache.clear()
        self.screen._rot_pivot = None
        self.screen._ensure_font()
        # Manual RUN: the dynamic RGB() color table is program state, like
        # the variables - a fresh run numbers colors from index 16 again
        # (see _reset_dynamic_rgb).  CONT deliberately does not reset it:
        # a stopped program's variables (holding its color indexes) survive.
        _reset_dynamic_rgb()
        # MUSICVOLUME is program state, like the variables: every RUN
        # starts at full volume (100).  A volume set by a previous run
        # (or in immediate mode) must not leak into the new one; CONT
        # deliberately does not reset it, matching the other per-run
        # state above.
        self.system.music_volume = 100
        self.pc = None
        self._stopped = False
        self._trace_last = None
        self.pc_stmt = 0
        self.cur_line = []
        self.cur_stmt_idx = 0
        self.date_str = time.strftime('%m-%d-%Y')
        self.time_str = time.strftime('%H:%M:%S')

    @property
    def io(self):
        """The I/O middle layer (see IoDevice): routes every print and key
        read of the program to the graphics window while it is open and to
        the console once it is closed.  Created on first use for a
        standalone interpreter; the REPL installs its own instance so that
        program and interpreter messages share one router."""
        if self._io is None:
            self._io = IoDevice(self.screen, self.output_func,
                                self.input_func, _read_key)
        return self._io

    def write(self, text, newline=True):
        # All program output goes through the I/O middle layer: the window
        # (the monitor) while it is open, the console once it is closed.
        self.io.write(text, newline)

    # -- value helpers ------------------------------------------------------- #
    def format_number(self, value):
        return self.format_number_kind(value, 'single')

    def format_value(self, value):
        return self.format_value_kind(value, 'single')

    def format_number_kind(self, value, kind='single'):
        """Format a number for display at its precision (manual 6.1.1):
        single-precision values print with seven or fewer digits;
        double-precision values with as many as 16."""
        if kind == 'double':
            return self._fmt_double(value)
        if kind == 'int':
            return str(value) if isinstance(value, int) else str(int(value))
        return self._fmt_single(value)

    def format_value_kind(self, value, kind='single'):
        if isinstance(value, str):
            return value
        s = self.format_number_kind(value, kind)
        if not s.startswith('-'):
            s = ' ' + s  # reserve sign column, like GW-BASIC
        return s

    def _fmt_single(self, value):
        if isinstance(value, int):
            return str(value)
        if not math.isfinite(value):
            return str(value)
        # Single-precision display: up to seven significant digits in a
        # fixed-point or integer format, and no leading zero for |x| < 1
        # (manual PRINT: "seven or fewer digits"; SIN(1.5) prints .9974951,
        # 1/3 prints .3333333).  Trailing zeros are dropped.  Values outside
        # the seven-digit fixed range print in exponential form.
        if value == int(value) and abs(value) < 1e7:
            return str(int(value))
        if abs(value) >= 1e7 or (value != 0 and abs(value) < 1e-5):
            return "%.5E" % value
        av = abs(value)
        # li: 10**li <= av < 10**(li+1); keep six digits after the leading
        # one (seven significant digits total).
        li = int(math.floor(math.log10(av)))
        decimals = max(0, 6 - li)
        s = '%.*f' % (decimals, av)
        if '.' in s:
            s = s.rstrip('0').rstrip('.')
        if s.startswith('0.'):
            s = '.' + s[2:]
        return ('-' if value < 0 else '') + s

    def _fmt_double(self, value):
        """Double-precision display (manual 6.1.1: "printed with as many as
        16 digits").

        The value is shown with its shortest round-tripping decimal
        (975.3421222# prints 975.3421222; 123456.789 prints 123456.789);
        when that needs more than sixteen significant digits, it is rounded
        to sixteen (2.04 widened to double prints 2.039999961853027, the
        manual's worked example).  No leading zero for |x| < 1, trailing
        zeros dropped, exponential form outside the sixteen-digit fixed
        range, with the same cutoffs the single-precision display uses.
        """
        if isinstance(value, int):
            return str(value)
        if not math.isfinite(value):
            return str(value)
        if value == int(value) and abs(value) < 1e15:
            return str(int(value))
        sign = ''
        r = repr(value)
        if r.startswith('-'):
            sign = '-'
            r = r[1:]
        if 'e' in r:
            r = r.upper()
        body = r.split('E')[0]
        if body.startswith('0.'):
            body = body[2:]
        if sum(c.isdigit() for c in body) > 16:
            # More than sixteen significant digits would be needed to
            # reproduce the value exactly; the manual allows "as many as
            # sixteen", so round to sixteen.
            r = '%.15E' % value
            if r.startswith('-'):
                r = r[1:]
        if 'E' in r:
            mant, exp = r.split('E')
            expi = int(exp)
            if mant.startswith('-'):
                mant = mant[1:]
            if abs(value) >= 1e16 or (value != 0 and abs(value) < 1e-5):
                return sign + mant + 'E%+03d' % expi
            digs = mant.replace('.', '')
            point = (mant.index('.') if '.' in mant else len(mant)) + expi
            if point <= 0:
                s = '0.' + '0' * (-point) + digs
            elif point >= len(digs):
                s = digs + '0' * (point - len(digs))
            else:
                s = digs[:point] + '.' + digs[point:]
            if '.' in s:
                s = s.rstrip('0').rstrip('.')
            if s.startswith('0.'):
                s = '.' + s[2:]
            return sign + s
        # Plain fixed-point repr: already the shortest form with no
        # trailing zeros (except the ".0" of a whole value >= 1e15).
        if r.startswith('0.'):
            r = '.' + r[2:]
        if r.endswith('.0'):
            r = r[:-2]
        return sign + r

    def _value_kind(self, value, vtype):
        """Display precision of a stored value (manual 6.1.1/6.2.2)."""
        if isinstance(value, str):
            return 'string'
        if vtype == 'integer':
            return 'int'
        if vtype == 'double':
            return 'double'
        return 'single'

    def var_type(self, name):
        """Effective type of a variable name.

        A type declaration suffix ($, %, !, #) always wins; otherwise the
        type declared for that exact variable name by DEFINT/DEFDBL/
        DEFSNG/DEFSTR applies; otherwise the variable is untyped (numeric,
        stored as given).
        """
        n = name
        if n and n[-1] in '$%!#':
            return {'$': 'string', '%': 'integer',
                    '!': 'single', '#': 'double'}[n[-1]]
        if not n:
            return 'default'
        if n.upper() in self.def_types:
            return self.def_types[n.upper()]
        return 'default'

    def _to_float(self, value):
        if isinstance(value, (int, float)):
            return float(value)
        return parse_val(str(value))

    def _single(self, value):
        """Round a value through IEEE-754 single precision.

        Integer fast path: an int holds its value exactly and is
        representable as a single, so no pack/unpack is needed - the int
        is kept as-is.  Only non-integer values (and out-of-range ints)
        go through the IEEE-754 single rounding."""
        if isinstance(value, bool):
            return int(value)
        if isinstance(value, int):
            # Every integer with magnitude below 2**23 is exactly
            # representable as an IEEE-754 single, so keep it as-is.  At
            # and beyond that bound the spacing of single-precision
            # values exceeds 1, so round through single precision.
            if -8388607 <= value <= 8388607:
                return value
            return round_single(value)
        return round_single(self._to_float(value))

    # -- single-precision math (1986 software-library emulation) ------------- #
    def _sin_single(self, x):
        """SIN in single precision (manual SIN: "SIN(x) is calculated in
        single-precision").

        Emulates the 16-bit software library of the original interpreter:
        a single-precision Taylor series, with terms added while they are
        >= 1e-8.  Unlike a correctly rounded single-precision sine, the
        library's result for the manual's example is one single-precision
        ULP higher, so SIN(1.5) prints .9974951 as documented.
        """
        x = self._single(x)
        if not math.isfinite(x):
            return math.sin(x)
        tau = self._single(2 * math.pi)
        pi = self._single(math.pi)
        r = self._single(x % tau)
        if r > pi:
            r = self._single(r - tau)
        x2 = self._single(r * r)
        t = s = self._single(r)
        n = 1
        while n < 40:
            t = self._single(self._single(-t * x2)
                             / self._single(self._single(2 * n) * (2 * n + 1)))
            if abs(t) < 1e-8:
                break
            s = self._single(s + t)
            n += 1
        return s

    def _log_single(self, x):
        """LOG (natural log) in single precision (manual LOG).

        Emulates the 16-bit software library: single-precision range
        reduction to [1, 2) plus a 2*atanh series (terms added while
        >= 1e-8), with the ln(2) constant given to seven significant
        digits -- the library's own display precision -- so LOG(2) =
        .6931471 as documented in the manual.
        """
        x = self._single(x)
        if not math.isfinite(x):
            return math.log(x)
        k = 0
        while x >= 2.0:
            x = self._single(x / 2.0)
            k += 1
        while x < 1.0:
            x = self._single(x * 2.0)
            k -= 1
        z = self._single(self._single(x - 1.0) / self._single(x + 1.0))
        z2 = self._single(z * z)
        t = s = self._single(z)
        n = 0
        while abs(t) >= 1e-8 and n < 100:
            t = self._single(t * z2)
            if abs(t) < 1e-8:
                break
            n += 1
            s = self._single(s + self._single(t / self._single(2.0 * n + 1.0)))
        s = self._single(2.0 * s)
        if k == 0:
            return s
        return self._single(s + self._single(self._single(0.6931471) * k))

    def _unpack_str(self, s, size, fmt):
        """Unpack the first `size` bytes of a string as a little-endian value."""
        data = str(s).encode('latin-1', errors='replace')[:size]
        if len(data) < size:
            data = data + b'\x00' * (size - len(data))
        return struct.unpack(fmt, data)[0]

    def _pack_str(self, value, fmt):
        """MKI$/MKS$/MKD$ (manual MKIS): pack a numeric value into the
        little-endian binary string that CVI/CVS/CVD unpack.  The result
        is a (possibly non-printable) string of the packed width."""
        if isinstance(value, str):
            raise BasicError("Type Mismatch")
        if fmt == '<h':
            # MKI$: the value must fit in a 16-bit integer.
            n = int(math.trunc(float(value)))
            if n < -32768 or n > 32767:
                raise BasicError("Overflow")
            return struct.pack('<h', n).decode('latin-1')
        try:
            return struct.pack(fmt, float(value)).decode('latin-1')
        except (OverflowError, ValueError):
            raise BasicError("Overflow")

    def coerce(self, name, value):
        """Coerce a value to the declared type of the variable."""
        t = self.var_type(name)
        if t == 'string':
            # A string variable/array element must hold a string.  (A numeric
            # value reaching coerce() here is a "Type mismatch" that the
            # caller's _check_let_type() rejects; this branch is a defensive
            # fallback only.)
            return value if isinstance(value, str) else self.format_value(value)
        if t == 'integer':
            v = self._to_float(value)
            # GW-BASIC rounds half away from zero.
            n = int(math.floor(v + 0.5)) if v >= 0 else int(math.ceil(v - 0.5))
            # Integer variables hold 16-bit signed values (-32768..32767);
            # an out-of-range assignment is "Overflow" (ERR 6), the same as
            # CINT and the logical operators (manual CINT / 6.4.3).
            if n < -32768 or n > 32767:
                raise BasicError("Overflow")
            return n
        if t == 'single':
            return self._single(value)
        if t == 'double':
            return self._to_float(value)
        # Untyped numeric variables are single precision by default
        # (manual 6.2.2); an untyped variable may also hold a string.
        if isinstance(value, str):
            return value
        if isinstance(value, int):
            # Integer fast path: an int is exact and representable as a
            # single, so it is stored as-is (no pack/unpack).  Only a
            # non-representable int actually needs single-precision
            # rounding.
            if -8388607 <= value <= 8388607:
                return value
            return self._single(value)
        return self._single(value)

    def assign(self, name, value):
        name = name if name.isupper() else name.upper()
        if name in ('ERR', 'ERL'):
            # ERR and ERL are read-only (set by the error handler).
            raise BasicError("Illegal function call")
        if name == 'DATE$':
            self._set_special_var('DATE$', value)
            return
        if name == 'TIME$':
            self._set_special_var('TIME$', value)
            return
        self.vars[name] = self.coerce(name, value)

    def _set_special_var(self, name, value):
        """Validate and store a DATE$ or TIME$ assignment (manual DATES/TIMES)."""
        if not isinstance(value, str):
            raise BasicError("Type mismatch")
        if name == 'DATE$':
            m = re.match(r'^(\d{1,2})[-/](\d{1,2})[-/](\d{2,4})$', value.strip())
            if not m:
                raise BasicError("Illegal function call")
            mo, d, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
            if y < 100:
                y += 1900
            if not (1980 <= y <= 2099) or not (1 <= mo <= 12) or not (1 <= d <= 31):
                raise BasicError("Illegal function call")
            self.date_str = '%02d-%02d-%04d' % (mo, d, y)
        else:  # TIME$
            m = re.match(r'^(\d{1,2})(?::(\d{1,2})(?::(\d{1,2}))?)?$', value.strip())
            if not m:
                raise BasicError("Illegal function call")
            h = int(m.group(1))
            mi = int(m.group(2)) if m.group(2) is not None else 0
            s = int(m.group(3)) if m.group(3) is not None else 0
            if h > 23 or mi > 59 or s > 59:
                raise BasicError("Illegal function call")
            self.time_str = '%02d:%02d:%02d' % (h, mi, s)

    def get_var(self, name):
        name = name if name.isupper() else name.upper()
        if name == 'TIME$':
            return self.time_str
        if name == 'DATE$':
            return self.date_str
        # Single lookup: the stored keys are canonical upper-case, so a
        # failed getitem is the membership test (one _key() + one dict
        # probe instead of two).
        try:
            return self.vars[name]
        except KeyError:
            return "" if self.var_type(name) == 'string' else 0

    def get_arr(self, name, idx):
        self._check_bounds(name, idx)
        arr = self.arrays.get(name, {})
        if idx in arr:
            return arr[idx]
        return "" if self.var_type(name) == 'string' else 0

    def _check_bounds(self, name, idx):
        """Validate an array index against the array's bounds.

        Implicit (non-DIM'd) arrays get their bounds on first use: the base
        is the current OPTION BASE and each upper bound starts at the index
        first used in that dimension. Implicit arrays grow to accommodate
        larger indices; DIM'd/REDIM'd arrays have fixed bounds. An index
        below the base, or out of range for a fixed array, raises
        "Subscript out of range" (GW-BASIC error 9).
        """
        if name not in self.array_dims:
            base = self.option_base
            # An array used without a DIM statement has subscripts 0..10
            # (or base..10 with OPTION BASE 1).  Anything beyond 10 is an
            # error; the array does not grow to fit larger indices.
            for i in idx:
                i = int(i)
                if i < base or i > 10:
                    raise BasicError("Subscript out of range")
            self.array_dims[name] = (base, [10] * len(idx), False)  # False = implicit
            return
        base, uppers, explicit = self.array_dims[name]
        if len(idx) != len(uppers):
            raise BasicError("Subscript out of range")
        changed = False
        for d, (i, u) in enumerate(zip(idx, uppers)):
            if i < base:
                raise BasicError("Subscript out of range")
            if i > u:
                if explicit:
                    raise BasicError("Subscript out of range")
                uppers[d] = i  # implicit arrays grow
                changed = True
        if changed:
            self.array_dims[name] = (base, uppers, explicit)

    def eval_target(self, target):
        if target[0] == 'var':
            return self.get_var(target[1])
        name = target[1]
        idx = tuple(int(self.eval(e)) for e in target[2])
        return self.get_arr(name, idx)

    def assign_target(self, target, value):
        if target[0] == 'var':
            self.assign(target[1], value)
            return
        name = target[1]
        idx = tuple(int(self.eval(e)) for e in target[2])
        self._check_bounds(name, idx)
        if name not in self.arrays:
            self.arrays[name] = {}
        self.arrays[name][idx] = self.coerce(name, value)

    # -- expression evaluation ---------------------------------------------- #
    def eval(self, node):
        return self.eval_with_kind(node)[0]

    def eval_with_kind(self, node):
        """Evaluate an expression, returning (value, kind).

        kind is 'int', 'single', 'double', or 'string' (manual 6.1.1/6.2.2/
        6.3): the precision at which the value is held, which governs its
        display (seven or up to sixteen digits) and the rounding of the
        arithmetic built from it.
        """
        tag = node[0]
        if tag == 'num':
            v = node[1]
            if len(node) > 2:
                return (v, node[2])
            # Two-tuple pseudo-numbers (FOR default step, INPUT# file
            # number): classify from the value itself.
            return (v, 'int' if isinstance(v, int) else 'single')
        if tag == 'str':
            return (node[1], 'string')
        if tag == 'var':
            name = node[1]
            upper = name.upper()
            if upper in NOARG_FUNCTIONS:
                return self.call_noarg_k(upper)
            v = self.get_var(name)
            return (v, self._value_kind(v, self.var_type(name)))
        if tag == 'arr':
            name = node[1]
            idx = tuple(int(self.eval(e)) for e in node[2])
            v = self.get_arr(name, idx)
            return (v, self._value_kind(v, self.var_type(name)))
        if tag == 'unop':
            op = node[1]
            v, k = self.eval_with_kind(node[2])
            if op == '-':
                return (-v, k)
            if op == '+':
                return (v, k)
            if op == 'NOT':
                # GW-BASIC NOT is a bitwise complement: NOT X = -(X+1) (manual
                # Chapter 6.4.3), so NOT 5 = -6, NOT 0 = -1, NOT -1 = 0.
                return (-self._to_int16(v) - 1, 'int')
            raise BasicError("Unknown unary op %s" % op)
        if tag == 'binop':
            op = node[1]
            a, ka = self.eval_with_kind(node[2])
            b, kb = self.eval_with_kind(node[3])
            return self.eval_binop_k(op, a, ka, b, kb)
        if tag == 'ifexp':
            # IF cond THEN a ELSE b - the conditional expression: only the
            # selected branch is evaluated, so e.g.
            # IF X=0 THEN 1 ELSE 10/X raises no divide-by-zero when X=0.
            if self.eval(node[1]):
                return self.eval_with_kind(node[2])
            return self.eval_with_kind(node[3])
        if tag == 'call':
            name = node[1]
            upper = name.upper()
            if upper == 'VARPTR':
                return (self._varptr(node[2]), 'int')
            if upper == 'VARPTR$':
                return (self._varptr_str(node[2]), 'string')
            args_k = [self.eval_with_kind(a) for a in node[2]]
            args = [a for a, _ in args_k]
            if upper in BUILTIN_FUNCTIONS:
                return self.call_builtin_k(upper, args_k)
            if name in self.def_fns or upper in self.def_fns:
                return self.call_def_fn_k(name, args_k)
            # Otherwise the name may only be an array reference.  If it is
            # not a known array (DIM'd, in implicit use, or ERASE'd), the
            # call is to a user function that was never DEF'd ->
            # "Undefined User Function" (manual DEFFN), instead of silently
            # creating an implicit array that reads back 0.
            if name not in self.arrays and name not in self.array_dims:
                raise BasicError("Undefined User Function")
            # Known array: treat as an array reference; non-numeric
            # subscripts are still an undefined-function reference.
            try:
                idx = tuple(int(a) for a in args)
            except (TypeError, ValueError):
                raise BasicError("Undefined function")
            v = self.get_arr(name, idx)
            return (v, self._value_kind(v, self.var_type(name)))
        raise BasicError("Unknown expression node %s" % tag)

    def _to_int32(self, v):
        """Convert a value to a 32-bit signed integer (GW-BASIC semantics)."""
        n = int(v)
        n &= 0xFFFFFFFF
        if n >= 0x80000000:
            n -= 0x100000000
        return n

    def _to_int16(self, v):
        """Convert a value to a 16-bit signed integer (GW-BASIC logical ops).

        Manual Chapter 6.4.3: "Logical operators convert their operands to
        16-bit, signed, two's complement integers within the range of -32768
        to +32767 (if the operands are not within this range, an error
        results)."  Out-of-range operands therefore raise "Overflow" (ERR 6).
        A string operand is a "Type mismatch" (ERR 13): logical operators
        take numeric operands and there is no implicit string conversion.
        """
        if isinstance(v, str):
            raise BasicError("Type mismatch")
        n = int(v)
        if n < -0x8000 or n > 0x7FFF:
            raise BasicError("Overflow", 6)
        return n

    def _bitwise16(self, a, b, op):
        """16-bit two's-complement bitwise AND/OR/XOR/EQV/IMP (GW-BASIC).

        Manual Chapter 6.4.3: operands are converted to 16-bit signed
        two's-complement integers (range -32768..32767, else "Overflow"), and
        the operation is performed bit-wise, each result bit set from the
        corresponding operand bits.  Used for AND / OR / XOR, whose manual
        worked examples are raw bitwise results (63 AND 16 = 16, -1 AND 8 = 8,
        4 OR 2 = 6).  EQV / IMP are NOT handled here: the manual's Table 6.2
        requires a Boolean 0/-1 result, so they are dispatched to
        _logical_bool() instead (see the operator dispatch below).
        """
        x = self._to_int16(a)
        y = self._to_int16(b)
        if op == 'and':
            r = x & y
        elif op == 'or':
            r = x | y
        elif op == 'xor':
            r = x ^ y
        else:
            raise BasicError("Unknown operator %s" % op)
        # Reinterpret the 16-bit pattern as a signed value.
        r &= 0xFFFF
        if r >= 0x8000:
            r -= 0x10000
        return r

    def _logical_bool(self, x, y, op):
        """Table 6.2 logical operator: EQV / IMP.

        Manual Chapter 6.4.3 is explicit that "The logical operator returns a
        bit-wise result which is either true (not zero) or false (zero)" and
        "If both operands are supplied as 0 or -1, logical operators return 0
        or -1".  The result therefore must be a Boolean 0 or -1, not a raw bit
        pattern.  The operands are first reduced to their truth value (nonzero
        = true) and Table 6.2 is applied:

            EQV: T T -> T    T F -> F    F T -> F    F F -> T
            IMP: T T -> T    T F -> F    F T -> T    F F -> T

        This is the classic GW-BASIC behavior: every multi-bit operand is
        normalized to 0/-1, so ``1 EQV 0`` and ``1 IMP 0`` are both 0 (false),
        not the raw bitwise pattern (which would be -2).  A string operand
        is a "Type mismatch" (ERR 13), like every other logical operator.
        """
        if isinstance(x, str) or isinstance(y, str):
            raise BasicError("Type mismatch")
        tx = -1 if x else 0
        ty = -1 if y else 0
        if op == 'eqv':
            return -1 if (tx == 0) == (ty == 0) else 0
        if op == 'imp':
            return 0 if (tx != 0 and ty == 0) else -1
        raise BasicError("Unknown operator %s" % op)

    def _compare(self, op, a, b):
        """Relational comparison with GW-BASIC mixed-type rules.

        A number always sorts before a string.
        """
        a_str = isinstance(a, str)
        b_str = isinstance(b, str)
        if a_str != b_str:
            a_is_num = not a_str
            if op == '<':
                return -1 if a_is_num else 0
            if op == '>':
                return -1 if not a_is_num else 0
            if op == '<=':
                return -1 if a_is_num else 0
            if op == '>=':
                return -1 if not a_is_num else 0
            if op == '=':
                return 0
            if op == '<>':
                return -1
        if op == '=':
            return -1 if a == b else 0
        if op == '<>':
            return -1 if a != b else 0
        if op == '<':
            return -1 if a < b else 0
        if op == '>':
            return -1 if a > b else 0
        if op == '<=':
            return -1 if a <= b else 0
        if op == '>=':
            return -1 if a >= b else 0
        raise BasicError("Unknown operator %s" % op)

    # Approximate GW-BASIC's largest representable magnitude (manual 6.1:
    # floating-point constants run up to ~1.7x10^38).
    _MACHINE_MAX = 1.701411834604692e+38

    def _runtime_warning(self, message):
        """Print a non-fatal GW-BASIC warning and continue.

        Manual 6.4.1.2: division by zero and exponentiation overflow (0 to
        a negative power) print their message and substitute machine
        infinity as the result, but do NOT halt the program and are
        explicitly "not trapped by the error trapping function" - i.e.
        ON ERROR GOTO must never see these, unlike a normal BasicError.
        """
        self.write(message, newline=True)

    def _machine_infinity(self, sign_source):
        """Signed machine-infinity placeholder (manual 6.4.1.2)."""
        try:
            negative = sign_source < 0
        except TypeError:
            negative = False
        return -self._MACHINE_MAX if negative else self._MACHINE_MAX

    def _round_int_operand(self, v):
        """Round a numeric operand to the nearest integer, half away from
        zero (manual 6.4.1.1: '\\' and MOD operands "are rounded to
        integers ... before the division is performed").  The manual adds
        that the operands "must be within the range of -32768 to 32767";
        this interpreter widens that limit so \\ and MOD operate on values up
        to the full 64-bit range (roughly +/-2^63).  A rounded operand that
        still does not fit in a signed 64-bit integer raises "Overflow" (ERR
        6).  This only affects \\ and MOD: CINT, integer variables, the
        logical operators and MKI$ still use the original 16-bit range."""
        if isinstance(v, str):
            raise BasicError("Type mismatch")
        n = int(math.floor(v + 0.5)) if v >= 0 else int(math.ceil(v - 0.5))
        if n < -(1 << 63) or n > (1 << 63) - 1:
            raise BasicError("Overflow")
        return n

    def _check_overflow(self, result):
        """Clamp an arithmetic result to GW-BASIC's overflow behavior
        (manual 6.4.1.2): print "Overflow" and substitute signed machine
        infinity instead of returning an out-of-range value; non-fatal
        and not trappable, same as division by zero."""
        if isinstance(result, (int, float)):
            try:
                too_big = abs(result) > self._MACHINE_MAX
            except (OverflowError, ValueError):
                too_big = True
            if too_big:
                self._runtime_warning("Overflow")
                return self._machine_infinity(result)
        return result

    def eval_binop(self, op, a, b):
        return self.eval_binop_k(op, a, 'single', b, 'single')[0]

    def _arith_kind(self, ka, kb):
        """Manual 6.3: all operands of an arithmetic operation are converted
        to the precision of the most precise operand, and the result is
        returned at that precision (a double operand wins; everything else
        is single)."""
        if ka == 'double' or kb == 'double':
            return 'double'
        return 'single'

    def _arith(self, r, ka, kb):
        r = self._check_overflow(r)
        k = self._arith_kind(ka, kb)
        if k == 'single':
            r = self._single(r)
        return (r, k)

    def eval_binop_k(self, op, a, ka, b, kb):
        if op == '&':
            # '&' is string concatenation, coercing numbers via STR$-style
            # formatting (at each operand's own precision).
            s = self.format_value_kind(a, ka) + self.format_value_kind(b, kb)
            return (s, 'string')
        if op == '+':
            a_str, b_str = isinstance(a, str), isinstance(b, str)
            if a_str or b_str:
                if not (a_str and b_str):
                    # Manual 6.3: mixing a string and a numeric operand is
                    # a "Type Mismatch", not an implicit conversion.
                    raise BasicError("Type mismatch")
                return (a + b, 'string')
            return self._arith(a + b, ka, kb)
        if op == '-':
            if isinstance(a, str) or isinstance(b, str):
                raise BasicError("Type mismatch")
            return self._arith(a - b, ka, kb)
        if op == '*':
            if isinstance(a, str) or isinstance(b, str):
                raise BasicError("Type mismatch")
            return self._arith(a * b, ka, kb)
        if op == '/':
            if isinstance(a, str) or isinstance(b, str):
                raise BasicError("Type mismatch")
            if b == 0:
                # Manual 6.4.1.2: non-fatal, not trappable, continues with
                # machine infinity signed like the numerator.
                self._runtime_warning("Division by zero")
                return (self._machine_infinity(a), 'single')
            return self._arith(a / b, ka, kb)
        if op == '\\':
            ai = self._round_int_operand(a)
            bi = self._round_int_operand(b)
            if bi == 0:
                self._runtime_warning("Division by zero")
                return (self._machine_infinity(ai), 'single')
            return (int(ai / bi), 'int')  # truncate toward zero
        if op == 'MOD':
            ai = self._round_int_operand(a)
            bi = self._round_int_operand(b)
            if bi == 0:
                self._runtime_warning("Division by zero")
                return (self._machine_infinity(ai), 'single')
            return (ai - int(ai / bi) * bi, 'int')
        if op == '^':
            if isinstance(a, str) or isinstance(b, str):
                raise BasicError("Type mismatch")
            if a == 0 and b < 0:
                # Manual 6.4.1.2: non-fatal, not trappable, continues with
                # positive machine infinity.
                self._runtime_warning("Division by zero")
                return (self._machine_infinity(1), 'single')
            if a < 0 and b != int(b):
                raise BasicError("Illegal function call")
            # On overflow, a ** b raises OverflowError (Python floats do not
            # silently saturate), so guard it and substitute signed machine
            # infinity instead of letting the exception escape (manual 6.4.1.2).
            try:
                return self._arith(a ** b, ka, kb)
            except OverflowError:
                self._runtime_warning("Overflow")
                return (self._machine_infinity(a), 'single')
        if op in ('=', '<>', '<', '>', '<=', '>='):
            return (self._compare(op, a, b), 'int')
        if op == 'AND':
            return (self._bitwise16(a, b, 'and'), 'int')
        if op == 'OR':
            return (self._bitwise16(a, b, 'or'), 'int')
        if op == 'XOR':
            return (self._bitwise16(a, b, 'xor'), 'int')
        # EQV / IMP: the manual (Ch 6.4.3, Table 6.2) mandates a Boolean result
        # (0 or -1) -- the operands are reduced to true/false and the truth
        # table applied, so multi-bit operands normalize (1 EQV 0 = 0, not -2).
        if op == 'EQV':
            return (self._logical_bool(a, b, 'eqv'), 'int')
        if op == 'IMP':
            return (self._logical_bool(a, b, 'imp'), 'int')
        raise BasicError("Unknown operator %s" % op)

    # -- built-in functions -------------------------------------------------- #
    def call_builtin_k(self, name, args_k):
        """call_builtin with precision tracking (manual 6.3): returns
        (value, kind) where kind is 'int', 'single', 'double', or 'string'.

        STR$, ABS and VAL need the argument's own precision (STR$ formats the
        number at that precision; VAL re-parses its text as a numeric
        constant).  Every other function goes through call_builtin unchanged;
        the result is classified: string results are 'string', integer
        results 'int', CDBL/CVD (which convert to double precision) 'double',
        and everything else 'single' - the manual's math functions are all
        "calculated in single-precision" unless the /d switch is used.
        """
        args = [a for a, _ in args_k]
        if name == 'STR$':
            v, k = args_k[0]
            s = self.format_number_kind(v, k)
            if not s.startswith('-'):
                s = ' ' + s
            return (s, 'string')
        if name == 'ABS':
            v, k = args_k[0]
            return (abs(v), k)
        if name == 'VAL':
            # Appendix A, error 13: VAL expects a string argument; a numeric
            # one is "Type mismatch" (no coercion).
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            s = args[0]
            m = _VAL_RE.match(s)
            v = parse_val(s)
            kind = classify_number(m.group(0)) if m else 'int'
            return (v, kind)
        v = self.call_builtin(name, args)
        if isinstance(v, str):
            return (v, 'string')
        if isinstance(v, int):
            return (v, 'int')
        if name in ('CDBL', 'CVD'):
            return (v, 'double')
        return (v, 'single')

    def call_builtin(self, name, args):
        # Appendix A, error 13: a function that expects a numeric argument is
        # given a string argument, or vice versa, is a "Type mismatch".  The
        # string functions below therefore reject a numeric x$ argument, and
        # LEFT$/RIGHT$/MID$ reject a string n/m argument, instead of the
        # implicit str()/int() coercion.
        if name == 'LEN':
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            return len(args[0])
        if name == 'LEFT$':
            # Manual LEFT$: x$ is a string expression; n is a numeric
            # expression within 0..255, else "Illegal function call".
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            if isinstance(args[1], str):
                raise BasicError("Type mismatch")
            n = int(args[1])
            if n < 0 or n > 255:
                raise BasicError("Illegal function call")
            return args[0][:n]
        if name == 'RIGHT$':
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            if isinstance(args[1], str):
                raise BasicError("Type mismatch")
            n = int(args[1])
            if n < 0 or n > 255:
                raise BasicError("Illegal function call")
            s = args[0]
            return s[-n:] if n > 0 else ''
        if name == 'MID$':
            # Manual MID$: x$ is a string expression; n is a numeric
            # expression within 1..255, optional m within 0..255, otherwise
            # "Illegal function call".
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            if isinstance(args[1], str):
                raise BasicError("Type mismatch")
            s = args[0]
            start = int(args[1])
            has_len = len(args) >= 3
            if has_len and isinstance(args[2], str):
                raise BasicError("Type mismatch")
            length = int(args[2]) if has_len else len(s)
            # Manual MID$ function: n within 1..255, m within 0..255,
            # otherwise "Illegal function call".
            if start < 1 or start > 255:
                raise BasicError("Illegal function call")
            if has_len and (length < 0 or length > 255):
                raise BasicError("Illegal function call")
            if has_len:
                return s[start - 1:start - 1 + length]
            return s[start - 1:]
        if name == 'CHR$':
            n = int(args[0])
            if n < 0 or n > 255:
                raise BasicError("Illegal function call")
            return chr(n)
        if name == 'ASC':
            # Manual ASC: x$ is a string expression; a null string is an
            # "Illegal function call".
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            s = args[0]
            if not s:
                raise BasicError("Illegal function call")
            return ord(s[0])
        if name == 'STR$':
            s = self.format_number(args[0])
            if not s.startswith('-'):
                s = ' ' + s
            return s
        if name == 'VAL':
            # Manual VAL: the argument is a string expression (Appendix A,
            # error 13).
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            return parse_val(args[0])
        if name == 'INSTR':
            # INSTR always returns a number (the 1-based position, or 0 when
            # not found), never a string -- per the manual it returns a
            # position, so the result is coerced to int in every path.
            if len(args) == 2:
                return int(find_instr(str(args[0]), str(args[1])))
            start = int(args[0])
            if start == 0:
                raise BasicError("Illegal argument in line number")
            if start < 1 or start > 255:
                raise BasicError("Illegal function call")
            haystack = str(args[1])
            needle = str(args[2])
            if start > len(haystack):
                return 0
            idx = haystack.find(needle, start - 1)
            return int(idx + 1) if idx != -1 else 0
        if name == 'UCASE$':
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            return args[0].upper()
        if name == 'LCASE$':
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            return args[0].lower()
        if name == 'SPACE$':
            # Manual SPACE$: x is rounded to an integer and must be within
            # the range of 0 to 255; out of range is "Illegal function call".
            n = int(args[0])
            if n < 0 or n > 255:
                raise BasicError("Illegal function call")
            return ' ' * n
        if name == 'TRIM$':
            if not isinstance(args[0], str):
                raise BasicError("Type mismatch")
            return args[0].strip()
        if name == 'ABS':
            return abs(args[0])
        if name == 'INT':
            return math.floor(args[0])
        if name == 'SQR':
            if args[0] < 0:
                raise BasicError("Illegal function call")
            # Manual SQR: calculated in single-precision.
            return self._single(math.sqrt(args[0]))
        if name == 'SIN':
            # Manual SIN: calculated in single-precision; the manual's
            # example SIN(1.5) = .9974951 pins the 1986 library's result.
            return self._sin_single(args[0])
        if name == 'COS':
            # Manual COS: calculated in single-precision.
            return self._single(math.cos(args[0]))
        if name == 'TAN':
            # Manual TAN: calculated in single-precision.
            return self._single(math.tan(args[0]))
        if name == 'LOG':
            if args[0] <= 0:
                raise BasicError("Illegal function call")
            # Manual LOG: calculated in single-precision; the manual's
            # example LOG(2) = .6931471 pins the 1986 library's result.
            return self._log_single(args[0])
        if name == 'EXP':
            # GW-BASIC numbers are single precision; EXP overflows above
            # the single-precision limit (~88.02969).
            if args[0] > 88.02969:
                raise BasicError("Overflow")
            # Manual EXP: calculated in single-precision.
            return self._single(math.exp(args[0]))
        if name == 'RND':
            # GW-BASIC: RND(0) returns the last value; RND(-1) re-seeds with
            # the system timer; RND(x>0) returns the next random number.
            x = args[0] if args else 1
            if x == 0:
                return self._last_rnd
            if x < 0:
                self.random.seed()
            self._last_rnd = self.random.random()
            return self._last_rnd
        if name == 'SGN':
            return (args[0] > 0) - (args[0] < 0)
        if name == 'FIX':
            return math.trunc(args[0])
        if name == 'ROUND':
            # Extension with the same half-away-from-zero rule as CINT
            # (2.5 -> 3, -2.5 -> -3); no 16-bit range check, like the
            # sibling ROUNDDOWN/ROUNDUP extensions.
            v = args[0]
            return int(math.floor(v + 0.5)) if v >= 0 else int(math.ceil(v - 0.5))
        if name == 'ATN':
            # Manual ATN: calculated in single-precision.
            return self._single(math.atan(args[0]))
        if name == 'ASIN':
            if args[0] < -1 or args[0] > 1:
                raise BasicError("Illegal function call")
            # Manual ASIN: calculated in single-precision.
            return self._single(math.asin(args[0]))
        if name == 'ACOS':
            if args[0] < -1 or args[0] > 1:
                raise BasicError("Illegal function call")
            # Manual ACOS: calculated in single-precision.
            return self._single(math.acos(args[0]))
        if name == 'CDBL':
            return self._to_float(args[0])
        if name == 'CSNG':
            return self._single(args[0])
        if name == 'CVI':
            return self._unpack_str(args[0], 2, '<h')
        if name == 'CVS':
            return self._unpack_str(args[0], 4, '<f')
        if name == 'CVD':
            return self._unpack_str(args[0], 8, '<d')
        if name == 'MKI$':
            return self._pack_str(args[0], '<h')
        if name == 'MKS$':
            return self._pack_str(args[0], '<f')
        if name == 'MKD$':
            return self._pack_str(args[0], '<d')
        if name == 'EOF':
            return self.files.eof(int(args[0]))
        if name == 'LOC':
            return self.files.loc(int(args[0]))
        if name == 'LOF':
            return self.files.lof(int(args[0]))
        if name == 'DIR$':
            return self.files.dir(args[0] if args else '')
        if name == 'INKEY$':
            return self.system.inkey()
        if name == 'INPUT$':
            n = int(args[0])
            if len(args) >= 2:
                # File form: INPUT$(n, [#]filenum).
                return self.files.input_chars(int(args[1]), n)
            s = ''
            for _ in range(max(0, n)):
                c = self.system.get()
                if not c:
                    break
                s += c
            return s
        if name == 'PEEK':
            return self.system.peer(int(args[0]))
        if name == 'PEER':
            # PEER is the word-sized sibling of PEEK: a signed 16-bit
            # little-endian read, not a byte alias.
            return self.system.peer_word(int(args[0]))
        if name == 'POINT':
            if len(args) == 1:
                # POINT (function): the current graphics coordinates.
                n = int(args[0])
                if n < 0 or n > 3:
                    raise BasicError("Illegal function call")
                return self.screen.point_coord(n)
            return self.screen.point(int(args[0]), int(args[1]))
        if name == 'RGB':
            # RGB(r,g,b): the full-precision color constructor.  Allocates
            # (or reuses) a dynamic palette slot for the exact color and
            # returns its index (>= 16); every drawing command accepts the
            # result as a color expression, e.g.
            #   LINE (0,0)-(99,99),RGB(255,0,0) BF
            #   PSET (10,10),RGB(200,16,24)
            if len(args) != 3:
                raise BasicError("Illegal function call")
            for a in args:
                if isinstance(a, str):
                    raise BasicError("Type mismatch")
            return _rgb_alloc(*args)
        if name == 'TIMER':
            return self.system.timer()
        if name == 'FRE':
            return self.system.fre(args[0] if args else None)
        if name == 'CSRLIN':
            return self.screen.csrlin()
        if name == 'POS':
            # Manual POS: POS(c) returns the current cursor column; c is a
            # dummy argument and the leftmost position is 1.
            return self.screen.cursor_col + 1
        if name in ('XSZ', 'XSIZE'):
            return self.screen.xsize()
        if name in ('YSZ', 'YSIZE'):
            return self.screen.ysize()
        if name == 'CINT':
            v = args[0]
            # GW-BASIC rounds half away from zero.
            r = int(math.floor(v + 0.5)) if v >= 0 else int(math.ceil(v - 0.5))
            if r < -32768 or r > 32767:
                raise BasicError("Overflow")
            return r
        if name == 'ROUNDDOWN':
            return math.floor(args[0])
        if name == 'ROUNDUP':
            return math.ceil(args[0])
        if name == 'ROUNDFRAC':
            return math.trunc(args[0])
        if name == 'HEX$':
            return self._hex_oct(args[0], 16)
        if name == 'OCT$':
            return self._hex_oct(args[0], 8)
        if name == 'BIN$':
            return self._hex_oct(args[0], 2)
        if name == 'STRING$':
            # Manual STRING$: n and j are 0..255; STRING$(n, x$) repeats
            # the FIRST character of x$ (null x$ -> "Illegal function call").
            n = int(args[0])
            if n < 0 or n > 255:
                raise BasicError("Illegal function call")
            if isinstance(args[1], str):
                s = args[1]
                if not s:
                    raise BasicError("Illegal function call")
                return s[0] * n
            j = int(args[1])
            if j < 0 or j > 255:
                raise BasicError("Illegal function call")
            return chr(j) * n
        if name == 'DAY':
            return self.system.now()['DAY']
        if name == 'MONTH':
            return self.system.now()['MONTH']
        if name == 'YEAR':
            return self.system.now()['YEAR']
        if name == 'HOUR':
            return self.system.now()['HOUR']
        if name == 'MINUTE':
            return self.system.now()['MINUTE']
        if name == 'SECOND':
            return self.system.now()['SECOND']
        if name == 'SCREEN':
            if not args:
                # SCREEN with no arguments returns the current mode.
                return self.screen.mode
            if len(args) == 1:
                # SCREEN(n) function: the current color of pen n.
                return self.screen.ink(int(args[0]))
            # SCREEN(row, col[, z]) function (manual SCREENF).
            row = int(args[0])
            col = int(args[1])
            z = bool(args[2]) if len(args) > 2 else False
            return self.screen.screen_at(row, col, z)
        if name == 'INK':
            return self.screen.ink(int(args[0]))
        if name in ('ENVIRON', 'ENVIRON$'):
            if not args:
                return ''
            return self.system.environ_get(args[0])
        raise BasicError("Unknown function %s" % name)

    def _hex_oct(self, v, base):
        """HEX$/OCT$/BIN$: round half away from zero, then two's complement.

        Manual (HEXS.html): HEX$ converts values in the range -32768..+65535
        into a hex string 0..FFFF, and "if x is negative, 2's (binary)
        complement form is used" -- i.e. a 16-bit representation.
        """
        n = int(math.floor(v + 0.5)) if v >= 0 else int(math.ceil(v - 0.5))
        if n < -0x8000 or n > 0xFFFF:
            raise BasicError("Overflow", 6)
        if n < 0:
            n += 0x10000
        if base == 16:
            return format(n, 'X')
        if base == 2:
            return format(n, 'b')
        return format(n, 'o')

    def call_noarg_k(self, name):
        v = self.call_noarg(name)
        if isinstance(v, str):
            return (v, 'string')
        if isinstance(v, int):
            return (v, 'int')
        return (v, 'single')

    def call_noarg(self, name):
        """Functions usable without parentheses: SCREEN, TIMER, CSRLIN, INKEY$, DATE$, TIME$."""
        if name == 'SCREEN':
            return self.screen.mode
        if name == 'TIMER':
            return self.system.timer()
        if name == 'CSRLIN':
            return self.screen.csrlin()
        if name == 'INKEY$':
            return self.system.inkey()
        if name == 'DATE$':
            return self.date_str
        if name == 'TIME$':
            return self.time_str
        if name == 'FRE':
            return self.system.fre()
        if name == 'POS':
            return self.screen.cursor_col + 1
        if name == 'RND':
            # Bare RND (no parentheses) is "the next random number"
            # (manual RND: RND[(x)], x omitted -> next in the sequence).
            self._last_rnd = self.random.random()
            return self._last_rnd
        if name in ('DAY', 'MONTH', 'YEAR', 'HOUR', 'MINUTE', 'SECOND'):
            return self.system.now()[name]
        raise BasicError("Unknown function %s" % name)

    def _varptr(self, arg_nodes):
        """VARPTR: needs the variable's identity, not just its value.

        A value must have been assigned to the variable before VARPTR runs,
        otherwise "Illegal function call" (manual VARPTR).  VARPTR(#n) returns
        the FCB address of file n.
        """
        if not arg_nodes:
            raise BasicError("VARPTR requires an argument")
        arg = arg_nodes[0]
        if arg[0] == 'fnum':
            filenum = int(self.eval(arg[1]))
            if filenum not in self.files.files:
                raise BasicError("Bad file number (52)")
            return self.system.fcb_addr(filenum)
        if arg[0] == 'var':
            varname = arg[1]
            if varname.upper() not in self.vars:
                raise BasicError("Illegal function call")
            value = self.get_var(varname)
            addr = self.system.varptr(varname, value)
            self.system.store_value(addr, value)
            return addr
        if arg[0] == 'arr':
            varname = arg[1]
            idx = tuple(int(self.eval(e)) for e in arg[2])
            arr = self.arrays.get(varname, {})
            if idx not in arr:
                raise BasicError("Illegal function call")
            value = self.get_arr(varname, idx)
            key = '%s[%s]' % (varname, ','.join(str(i) for i in idx))
            addr = self.system.varptr(key, value)
            self.system.store_value(addr, value)
            return addr
        value = self.eval(arg)
        addr = self.system.varptr('expr', value)
        self.system.store_value(addr, value)
        return addr

    def _varptr_str(self, arg_nodes):
        """VARPTR$: the three-byte string form of VARPTR (manual VARPTR$).

        Returns a three-byte string: byte 0 is the variable type (2 integer,
        3 string, 4 single-precision, 8 double precision); bytes 1-2 are the
        address in 8086 format, least significant byte first.  As with
        VARPTR, a value must have been assigned to the variable (or array
        element) before VARPTR$ runs, otherwise "Illegal function call".
        The manual defines VARPTR$ only for a variable, so any other form
        (an expression or #file number) is an illegal call.
        """
        if not arg_nodes:
            raise BasicError("VARPTR$ requires an argument")
        arg = arg_nodes[0]
        if arg[0] == 'var':
            varname = arg[1]
            if varname.upper() not in self.vars:
                raise BasicError("Illegal function call")
            value = self.get_var(varname)
            addr = self.system.varptr(varname, value)
            self.system.store_value(addr, value)
        else:
            # An array element: an 'arr' node (assignment/READ context), or
            # a 'call' node naming a known array (expression context, where
            # "A(i)" is parsed as a function call and disambiguated here).
            name = None
            idx_nodes = None
            if arg[0] == 'arr':
                name, idx_nodes = arg[1], arg[2]
            elif arg[0] == 'call' and (
                    arg[1] in self.arrays or arg[1].upper() in self.arrays
                    or arg[1] in self.array_dims
                    or arg[1].upper() in self.array_dims):
                name, idx_nodes = arg[1], arg[2]
            if name is None:
                # The manual defines VARPTR$ only for a variable; any other
                # form (an expression or #file number) is an illegal call.
                raise BasicError("Illegal function call")
            varname = name
            idx = tuple(int(self.eval(e)) for e in idx_nodes)
            arr = self.arrays.get(varname, self.arrays.get(varname.upper(), {}))
            if idx not in arr:
                raise BasicError("Illegal function call")
            value = self.get_arr(varname, idx)
            key = '%s[%s]' % (varname, ','.join(str(i) for i in idx))
            addr = self.system.varptr(key, value)
            self.system.store_value(addr, value)
        # GW-BASIC's default (untyped) numeric storage is single precision.
        type_bytes = {'integer': 2, 'string': 3, 'single': 4, 'double': 8}
        t = type_bytes.get(self.var_type(varname), 4)
        addr &= 0xFFFF
        return chr(t) + chr(addr & 0xFF) + chr((addr >> 8) & 0xFF)

    def call_def_fn(self, name, args):
        key = name if name in self.def_fns else name.upper()
        if key not in self.def_fns:
            raise BasicError("Undefined User Function")
        params, body = self.def_fns[key]
        if len(args) != len(params):
            raise BasicError("Wrong number of args for %s" % name)
        # Recursive DEF FN is not supported.
        if key in self._def_fn_active:
            raise BasicError("Illegal function call")
        # Argument type must agree with the parameter's declared type.
        for p, a in zip(params, args):
            pt = self.var_type(p)
            if pt == 'default':
                continue
            is_str = isinstance(a, str)
            if pt == 'string' and not is_str:
                raise BasicError("Type Mismatch")
            if pt in ('integer', 'single', 'double') and is_str:
                raise BasicError("Type Mismatch")
        old = {}
        for p in params:
            old[p] = self.vars.get(p)
        for p, a in zip(params, args):
            self.assign(p, a)
        self._def_fn_active.add(key)
        try:
            value = self.eval(body)
        finally:
            self._def_fn_active.discard(key)
            for p in params:
                if old[p] is None:
                    self.vars.pop(p, None)
                else:
                    self.vars[p] = old[p]
        # A typed function name forces the return value to that type.
        if key and key[-1] == '$':
            return value if isinstance(value, str) else str(value)
        if key and key[-1] in '%!#':
            return self._to_float(value)
        return value

    def call_def_fn_k(self, name, args_k):
        """DEF FN evaluation with precision tracking: the body is evaluated
        via eval_with_kind so the result carries its natural precision, and
        a typed function name (%, !, #) forces the documented return type
        (manual DEFFN)."""
        key = name if name in self.def_fns else name.upper()
        if key not in self.def_fns:
            raise BasicError("Undefined User Function")
        params, body = self.def_fns[key]
        args = [a for a, _ in args_k]
        if len(args) != len(params):
            raise BasicError("Wrong number of args for %s" % name)
        # Recursive DEF FN is not supported.
        if key in self._def_fn_active:
            raise BasicError("Illegal function call")
        # Argument type must agree with the parameter's declared type.
        for p, a in zip(params, args):
            pt = self.var_type(p)
            if pt == 'default':
                continue
            is_str = isinstance(a, str)
            if pt == 'string' and not is_str:
                raise BasicError("Type Mismatch")
            if pt in ('integer', 'single', 'double') and is_str:
                raise BasicError("Type Mismatch")
        old = {}
        for p in params:
            old[p] = self.vars.get(p)
        for p, a in zip(params, args):
            self.assign(p, a)
        self._def_fn_active.add(key)
        try:
            value, kind = self.eval_with_kind(body)
        finally:
            self._def_fn_active.discard(key)
            for p in params:
                if old[p] is None:
                    self.vars.pop(p, None)
                else:
                    self.vars[p] = old[p]
        # A typed function name forces the return value to that type.
        if key and key[-1] == '$':
            if isinstance(value, str):
                return (value, 'string')
            # Numeric body result of a $-named function: convert with the
            # value's own display precision, so FNS$(5) is "5", not "5.0".
            return (self.format_number_kind(value, kind), 'string')
        if key and key[-1] == '%':
            return (self._to_float(value), 'int')
        if key and key[-1] == '!':
            return (self._single(value), 'single')
        if key and key[-1] == '#':
            return (self._to_float(value), 'double')
        return (value, kind)

    # -- structural searches ------------------------------------------------- #
    def find_matching_else(self, start_line, ignore=()):
        """Find the ELSE line owned by the IF at/around `start_line`.

        Scans forward over the program lines: every IF without an inline
        ELSE (fall-through or inline statement) owns the next unmatched
        ELSE line, so it opens a scope; an ELSE closes the innermost open
        scope, and an ELSE at depth 0 is the match.  `ignore` lists ELSE
        lines already claimed by in-progress (nested) multi-line IFs, so a
        nested outer IF claims the *next* ELSE line instead.
        """
        ignore = set(ignore)
        depth = 0
        for line in self.lines:
            if line <= start_line:
                continue
            for stmt in self.program[line]:
                if stmt[0] == 'if' and stmt[3] is None:
                    depth += 1
                elif stmt[0] == 'else':
                    if depth == 0:
                        if line in ignore:
                            continue
                        return (line, stmt[1] is not None)
                    depth -= 1
        return None

    def find_if_terminator(self, start_line, ignore=()):
        """Find the line that terminates the fall-through IF at/around
        `start_line`: the first unmatched ELSE or ENDIF line after it.

        Scans forward over the program lines: every IF without an inline
        ELSE (fall-through or inline statement) opens a scope; an ELSE or
        ENDIF at depth 0 is the terminator, and one at depth > 0 closes the
        innermost open scope.  `ignore` lists ELSE lines already claimed by
        in-progress (nested) multi-line IFs, so a nested outer IF claims the
        *next* ELSE line instead.

        Returns (line, kind, has_stmt) where kind is 'else' or 'endif' and
        has_stmt is True when an ELSE line carries its own statement, or
        None when no terminator exists.  For programs with no ENDIF lines
        this is exactly find_matching_else.
        """
        ignore = set(ignore)
        depth = 0
        for line in self.lines:
            if line <= start_line:
                continue
            for stmt in self.program[line]:
                if stmt[0] == 'if' and stmt[3] is None:
                    depth += 1
                elif stmt[0] == 'else':
                    if depth == 0:
                        if line in ignore:
                            continue
                        return (line, 'else', stmt[1] is not None)
                    depth -= 1
                elif stmt[0] == 'endif':
                    if depth == 0:
                        return (line, 'endif', False)
                    depth -= 1
        return None

    def find_matching_next(self, start_line):
        depth = 0
        for line in self.lines:
            if line <= start_line:
                continue
            for stmt in self.program[line]:
                if stmt[0] == 'for':
                    depth += 1
                elif stmt[0] == 'next':
                    if depth == 0:
                        return line
                    depth -= 1
        return None

    def find_matching_next_pos(self, start_line, start_idx):
        """Return (line, stmt_idx) of the NEXT matching the FOR at
        (start_line, start_idx), or None. Scans the rest of the current line
        first (a single-line FOR puts its NEXT on the FOR line), then
        subsequent lines, tracking FOR/NEXT nesting depth."""
        depth = 0
        line = self.program[start_line]
        for i in range(start_idx + 1, len(line)):
            tag = line[i][0]
            if tag == 'for':
                depth += 1
            elif tag == 'next':
                if depth == 0:
                    return (start_line, i)
                depth -= 1
        for ln in self.lines:
            if ln <= start_line:
                continue
            for i, stmt in enumerate(self.program[ln]):
                tag = stmt[0]
                if tag == 'for':
                    depth += 1
                elif tag == 'next':
                    if depth == 0:
                        return (ln, i)
                    depth -= 1
        return None

    def find_matching_wend(self, start_line):
        depth = 0
        for line in self.lines:
            if line <= start_line:
                continue
            for stmt in self.program[line]:
                if stmt[0] == 'while':
                    depth += 1
                elif stmt[0] == 'wend':
                    if depth == 0:
                        return line
                    depth -= 1
        return None

    def find_matching_wend_pos(self, start_line, start_idx):
        """Return (line, stmt_idx) of the WEND matching the WHILE at
        (start_line, start_idx), or None. Scans the rest of the current line
        first (a single-line WHILE puts its WEND on the WHILE line), then
        subsequent lines, tracking WHILE/WEND nesting depth."""
        depth = 0
        line = self.program[start_line]
        for i in range(start_idx + 1, len(line)):
            tag = line[i][0]
            if tag == 'while':
                depth += 1
            elif tag == 'wend':
                if depth == 0:
                    return (start_line, i)
                depth -= 1
        for ln in self.lines:
            if ln <= start_line:
                continue
            for i, stmt in enumerate(self.program[ln]):
                tag = stmt[0]
                if tag == 'while':
                    depth += 1
                elif tag == 'wend':
                    if depth == 0:
                        return (ln, i)
                    depth -= 1
        return None

    def find_matching_loop_pos(self, start_line, start_idx):
        """Return (line, stmt_idx) of the LOOP matching the DO at
        (start_line, start_idx), or None. Scans the rest of the current line
        first (a single-line DO puts its LOOP on the DO line), then
        subsequent lines, tracking DO/LOOP nesting depth."""
        depth = 0
        line = self.program[start_line]
        for i in range(start_idx + 1, len(line)):
            tag = line[i][0]
            if tag == 'do':
                depth += 1
            elif tag == 'loop':
                if depth == 0:
                    return (start_line, i)
                depth -= 1
        for ln in self.lines:
            if ln <= start_line:
                continue
            for i, stmt in enumerate(self.program[ln]):
                tag = stmt[0]
                if tag == 'do':
                    depth += 1
                elif tag == 'loop':
                    if depth == 0:
                        return (ln, i)
                    depth -= 1
        return None

    def for_should_continue(self, current, end, step):
        if step > 0:
            return current <= end
        if step < 0:
            return current >= end
        return True

    # -- statement execution ------------------------------------------------- #
    def execute_line(self, line, start_idx=0):
        self.cur_line = line
        for idx in range(start_idx, len(line)):
            self.cur_stmt_idx = idx
            self.execute_statement(line[idx])

    def execute_statement(self, stmt):
        # Manual ON COM/KEY: at the start of every new statement, check
        # whether a trapped key event has occurred (and expand any
        # redefined F1-F10 key so INKEY$ can read its characters).
        self._check_key_traps()
        tag = stmt[0]
        if tag == 'print':
            self.do_print(stmt[1])
        elif tag == 'input':
            self.do_input(stmt[1], stmt[2], stmt[3] if len(stmt) > 3 else False)
        elif tag == 'let':
            value = self.eval(stmt[2])
            self._check_let_type(stmt[1], value)
            self.assign_target(stmt[1], value)
        elif tag == 'if':
            self.do_if(stmt)
        elif tag == 'for':
            self.do_for(stmt)
        elif tag == 'next':
            self.do_next(stmt[1])
        elif tag == 'next_multi':
            self.do_next_multi(stmt[1])
        elif tag == 'while':
            self.do_while(stmt)
        elif tag == 'wend':
            self.do_wend()
        elif tag == 'endif':
            # ENDIF (extension) terminates a multi-line IF ... THEN block.
            # Reaching it means the block's condition was true (or the line
            # was jumped to directly); the false-skip already landed past
            # it, so just fall through.
            pass
        elif tag == 'goto':
            raise Goto(stmt[1])
        elif tag == 'gosub':
            raise Gosub(stmt[1])
        elif tag == 'return':
            raise Return(stmt[1])
        elif tag == 'resume':
            self.do_resume(stmt[1])
        elif tag == 'resume_next':
            self.do_resume_next()
        elif tag == 'on_goto':
            self.do_on_goto(stmt)
        elif tag == 'on_gosub':
            self.do_on_gosub(stmt)
        elif tag == 'rem':
            pass
        elif tag == 'data':
            pass  # data pool built at load time
        elif tag == 'read':
            self.do_read(stmt[1])
        elif tag == 'restore':
            self.do_restore(stmt[1])
        elif tag == 'end':
            self.files.close()
            raise Stop()
        elif tag == 'stop':
            raise Break(self.pc)
        elif tag == 'dim':
            self.do_dim(stmt)
        elif tag == 'erase':
            self.do_erase(stmt[1])
        elif tag == 'swap':
            self.do_swap(stmt)
        elif tag == 'def_fn':
            self.def_fns[stmt[1]] = (stmt[2], stmt[3])
        elif tag == 'def_type':
            self.do_def_type(stmt)
        elif tag == 'on_error':
            # Manual ON ERROR: ON ERROR GOTO 0 disables trapping (like
            # ON ERROR OFF); subsequent errors print a message and halt.
            if stmt[1] == 0 and self._in_error_handler:
                # Manual ON ERROR: an ON ERROR GOTO 0 inside an active
                # error handler stops and prints the message of the
                # error that caused the trap.  Checked first so the reset
                # below does not clear the flag we are about to report on.
                raise BasicError(self._trapped_error or "Error")
            self.error_handler = None if stmt[1] in (None, 0) else stmt[1]
            # Executing ON ERROR (setting or clearing the trap) leaves any
            # prior handler context: reset the in-handler flag so the next
            # error is trapped normally.  This covers the two common ways a
            # handler returns to normal code -- "ON ERROR OFF + GOTO" and the
            # chained-handler pattern (a handler GOTOs out, then ON ERROR
            # GOTO n sets up the next trap).  Without this, a handler that
            # exits via a plain GOTO leaves _in_error_handler set, and
            # "error trapping does not occur within the handler" would then
            # wrongly suppress every later trap.  Note: error_line is NOT
            # cleared here, because a following RESUME NEXT still needs it.
            self._in_error_handler = False
        elif tag == 'cls':
            if stmt[1] is not None:
                n = int(self.eval(stmt[1]))
                if n not in (0, 1, 2):
                    raise BasicError("Illegal function call")
            self.screen.cls()
            if self.screen.virtual:
                self.output_func('\033[2J\033[H')
        elif tag == 'beep':
            self.output_func('\a')
        elif tag == 'sound':
            # SOUND freq,duration (manual SOUND): non-blocking.  On Windows
            # the tone is played for real by the background speaker thread
            # (Windows sound driver / winsound); elsewhere it is simulated
            # and a starting tone is approximated with the terminal bell.
            if self.system.sound(self.eval(stmt[1]), self.eval(stmt[2])) \
                    and self.system._winsound is None:
                self.output_func('\a')
        elif tag == 'sleep':
            self._sleep_seconds(self.eval(stmt[1]))
        elif tag == 'setfps':
            self.screen.set_fps(self.eval(stmt[1]))
        elif tag == 'mouse':
            self.do_mouse(stmt)
        elif tag == 'randomize':
            if stmt[1] is not None:
                v = self.eval(stmt[1])
                if isinstance(v, str):
                    raise BasicError("Type mismatch")
                # RANDOMIZE [expression]: "expression may be any numeric
                # formula" and is not forced to an integer (manual
                # RANDOMIZE) - no range check, so RANDOMIZE TIMER
                # (0..86399 seconds) works.
                self.random.seed(v)
            else:
                # Bare RANDOMIZE: prompt for a seed (manual RANDOMIZE).
                self.write("Random number seed (-32768 to 32767)? ", newline=False)
                try:
                    line = self.io.read_line().strip()
                except EOFError:
                    line = ''
                if line == '':
                    self.random.seed()
                else:
                    try:
                        seed = int(float(line))
                    except ValueError:
                        raise BasicError("Type mismatch")
                    if seed < -32768 or seed > 32767:
                        raise BasicError("Illegal function call")
                    self.random.seed(seed)
        elif tag == 'locate':
            self.do_locate(stmt[1])
        elif tag == 'else':
            self.do_else(stmt)
        elif tag == 'open':
            self.do_open(stmt)
        elif tag == 'close':
            self.do_close(stmt[1])
        elif tag == 'get':
            self.do_get(stmt)
        elif tag == 'get_key':
            self.do_get_key(stmt[1])
        elif tag == 'get_graphics':
            self.do_get_graphics(stmt)
        elif tag == 'put':
            self.do_put(stmt)
        elif tag == 'put_graphics':
            self.do_put_graphics(stmt)
        elif tag == 'seek':
            self.do_seek(stmt)
        elif tag == 'kill':
            self.files.kill(self.eval(stmt[1]))
        elif tag == 'line':
            self.do_line(stmt)
        elif tag == 'line_input':
            self.do_line_input(stmt)
        elif tag == 'line_input_key':
            self.do_line_input_key(stmt[1], stmt[2] if len(stmt) > 2 else None)
        elif tag == 'circle':
            self.do_circle(stmt)
        elif tag == 'paint':
            self.do_paint(stmt)
        elif tag == 'poke':
            for addr, val in stmt[1]:
                self.system.poke(self.eval(addr), self.eval(val))
        elif tag == 'play':
            self.do_play(stmt[1])
        elif tag == 'musicfile':
            path = stmt[2]
            if not isinstance(path, str):
                # File name from a string variable/expression.
                path = self.eval(path)
                if not isinstance(path, str):
                    raise BasicError("Type Mismatch")
            self.do_musicfile(stmt[1], path)
        elif tag == 'playmusic':
            self.do_playmusic(stmt[1])
        elif tag == 'stopmusic':
            self.system.music_stop()
        elif tag == 'musicvolume':
            self.system.music_set_volume(self.eval(stmt[1]))
        elif tag == 'pset':
            self.do_pset_preset(stmt)
        elif tag == 'preset':
            self.do_pset_preset(stmt)
        elif tag == 'draw':
            self.screen.draw(str(self.eval(stmt[1])))
        elif tag == 'palette':
            # PALETTE: emulated as a no-op (no real hardware palette).
            pass
        elif tag == 'palette_using':
            # PALETTE USING arrayname, index: no-op remap.
            pass
        elif tag == 'color':
            self.screen.color(self.eval(stmt[1]) if stmt[1] is not None else None,
                              self.eval(stmt[2]) if stmt[2] is not None else None,
                              self.eval(stmt[3]) if stmt[3] is not None else None)
        elif tag == 'ink':
            self.screen.ink(self.eval(stmt[1]), self.eval(stmt[2]) if stmt[2] is not None else None)
        elif tag == 'screen':
            self.screen.set_mode(int(self.eval(stmt[1])))
            if stmt[3] is not None:
                self.screen.apage = int(self.eval(stmt[3]))
            if stmt[4] is not None:
                self.screen.vpage = int(self.eval(stmt[4]))
        elif tag == 'screensize':
            # Custom-size graphics window: x = width, y = height (pixels).
            # Uses the full 16-color palette (the max this interpreter
            # supports) via the custom-size screen mode.  A bare SCREENSIZE
            # (no size) defaults to the classic 320x200; SCREENSIZE w is
            # square.  SCREENSIZE FULLSCREEN maximizes the window to fill the
            # screen; the interpreter chooses the size (the screen size).
            fullscreen = stmt[3] if len(stmt) > 3 else False
            if stmt[1] is None and not fullscreen:
                w, h = 320, 200
            elif stmt[1] is None:
                w, h = None, None  # fullscreen: size chosen by the window
            else:
                w = int(self.eval(stmt[1]))
                h = int(self.eval(stmt[2]))
            size = None if w is None else (w, h)
            if not fullscreen:
                # Place the window's top-left corner at the position the
                # last LOCATE set (desktop pixels; the initial top-left
                # corner if LOCATE has not run yet).  set_mode resets the
                # cursor but not locate_pos, so the position survives it.
                # The placement is a one-shot: _init_gui applies it when the
                # window is created; the code below applies it when the
                # window already exists.
                row, col = self.screen.locate_pos
                self.screen._window_topleft = (col, row)
            self.screen.set_mode(CUSTOM_SCREEN_MODE, size=size,
                                 fullscreen=fullscreen)
            if not fullscreen and self.screen._root is not None:
                # The window already existed (set_mode just rendered it):
                # move it now with a single geometry() call.
                x, y = self.screen._window_topleft
                self.screen._window_topleft = None
                try:
                    self.screen._root.geometry("+%d+%d" % (x, y))
                except Exception:
                    pass
        elif tag == 'textsize':
            # TEXTSIZE x: size (in pixels) of a text character cell on the
            # monitor.  A bare TEXTSIZE (size None) resets to the default
            # cell (TEXTSIZE_DEFAULT, 11).
            size = None if stmt[1] is None else self.eval(stmt[1])
            self.screen.textsize(size)
        elif tag == 'textrotate':
            # TEXTRotate x: rotate the lines of text drawn from now on by x
            # degrees (0-359) clockwise, each line about its pivot (the
            # cursor at the line's start); a bare TEXTRotate (degrees None)
            # resets to upright.  The range is validated in Screen.
            # textrotate.
            self.screen.textrotate(
                None if stmt[1] is None else self.eval(stmt[1]))
        elif tag == 'textfont':
            # TEXTFONT [font][, [bold][, [italic]]]: the face and weight of
            # the monitor text drawn from now on (see Screen.textfont).
            # Omitted arguments are None and take their per-slot defaults
            # (Arial, not bold, not italic); an unknown face or flag is an
            # "Illegal function call".
            self.screen.textfont(stmt[1], stmt[2], stmt[3])
        elif tag == 'cursor':
            self.screen.cursor(self.eval(stmt[1]))
        elif tag == 'view':
            if stmt[1] is None:
                self.screen.view_rect = None
                self.screen.view_screen = False
            else:
                self.screen.view(self.eval(stmt[1]), self.eval(stmt[2]),
                                 self.eval(stmt[3]), self.eval(stmt[4]),
                                 stmt[5])
        elif tag == 'window':
            if stmt[1] is None:
                self.screen.window(None)
            else:
                self.screen.window(self.eval(stmt[1]), self.eval(stmt[2]),
                                   self.eval(stmt[3]), self.eval(stmt[4]),
                                   stmt[5])
        elif tag == 'wclose':
            # WCLOSE: destroy the graphics window and drop I/O back to the
            # console; the program keeps running (see Screen.wclose).
            self.screen.wclose()
        elif tag == 'pause':
            # PAUSE (extension): wait for SPACE/ENTER (see do_pause).
            self.do_pause()
        elif tag == 'bload':
            mode = self.eval(stmt[2]) if stmt[2] is not None else None
            start = self.eval(stmt[3]) if stmt[3] is not None else None
            self.system.bload(self.eval(stmt[1]), mode, start)
        elif tag == 'bsave':
            self.system.bsave(self.eval(stmt[1]), self.eval(stmt[2]),
                              self.eval(stmt[3]))
        elif tag == 'out':
            self.system.out(self.eval(stmt[1]), self.eval(stmt[2]))
        elif tag == 'key':
            n = int(self.eval(stmt[1]))
            # Valid key numbers are 1-10 or 15-20 (manual KEY).
            if not ((1 <= n <= 10) or (15 <= n <= 20)):
                raise BasicError("Illegal function call")
            s = str(self.eval(stmt[2]))
            if 1 <= n <= 10:
                # KEY n, "string": the key's assignment; only the first 15
                # characters are stored (manual KEY).  A null string
                # disables the key as a function key.
                self.key_defs[n] = s[:15]
            else:
                # KEY n, CHR$(hex code)+CHR$(scan code): defines the physical
                # key trapped by ON KEY(n) (modifier mask + scan code).
                if len(s) < 2:
                    raise BasicError("Illegal function call")
                self.key_defs[n] = (ord(s[0]), ord(s[1]))
        elif tag == 'key_state':
            self.do_key_state(stmt[1], stmt[2])
        elif tag == 'key_on':
            self.system.key_on()
        elif tag == 'key_off':
            self.system.key_off()
        elif tag == 'key_list':
            # Manual KEY LIST: list all key values; strings are displayed
            # padded out to their full 15 characters.
            for n in sorted(self.key_defs):
                v = self.key_defs[n]
                if isinstance(v, tuple):
                    self.write("KEY %d = CHR$(%d)+CHR$(%d)\n"
                               % (n, v[0], v[1]), newline=False)
                else:
                    self.write("KEY %d = \"%s\"\n" % (n, v.ljust(15)),
                               newline=False)
        elif tag == 'environ':
            self.system.environ(self.eval(stmt[1]) if stmt[1] is not None else None)
        elif tag == 'do':
            self.do_do(stmt)
        elif tag == 'loop':
            self.do_loop(stmt)
        elif tag == 'option':
            new_base = int(self.eval(stmt[1]))
            if new_base not in (0, 1):
                raise BasicError("Illegal function call")
            if new_base != self.option_base and self._arrays_in_use():
                raise BasicError("Illegal function call")
            self.option_base = new_base
        elif tag == 'type':
            self.types[stmt[1]] = stmt[2]
        elif tag == 'field':
            self.do_field(stmt)
        elif tag == 'field_old':
            self.do_field_old(stmt)
        elif tag == 'redim':
            self.do_redim(stmt)
        elif tag == 'error':
            self.do_error(stmt[1])
        elif tag == 'run':
            self.do_run(stmt)
        elif tag == 'system':
            # SYSTEM closes all files before returning (manual SYSTEM).
            self.files.close()
            raise Stop()
        elif tag == 'edit':
            pass
        elif tag == 'write':
            self.do_write(stmt)
        elif tag == 'wait':
            self.do_wait(stmt[1])
        elif tag == 'lset':
            self.do_lset_rset(stmt, left=True)
        elif tag == 'rset':
            self.do_lset_rset(stmt, left=False)
        elif tag == 'lprint':
            # LPRINT: same as PRINT, output goes to the line printer
            # (emulated as a no-op here; the 80-column width is assumed).
            pass
        elif tag == 'lprint_using':
            pass
        elif tag == 'common':
            # COMMON variables: recorded (manual COMMON).
            self.common_vars = getattr(self, 'common_vars', []) + list(stmt[1])
        elif tag == 'new':
            # NEW (manual NEW): delete the program in memory and clear all
            # variables, then return to command level.
            self.program.clear()
            self.reset_state()
            self.trace = False
            self.trace_rate = None
            self.trace_lps = None
            self.trace_pause = False
            self._trace_pause_count = 0
            self._new_cleared = True
            raise Stop()
        elif tag == 'def_seg':
            self.system.def_seg(self.eval(stmt[1]) if stmt[1] is not None else None)
        elif tag == 'trap':
            self._trap = stmt[1]
        elif tag == 'on_key':
            self.do_on_key(stmt[1], stmt[2])
        elif tag == 'on_timer':
            pass  # timer events are not emulated
        elif tag == 'mid_assign':
            self.do_mid_assign(stmt[1], stmt[2])
        elif tag == 'print_file':
            self.do_print_file(stmt)
        elif tag == 'input_file':
            self.do_input_file(stmt)
        else:
            raise BasicError("Unknown statement %s" % tag)

    # -- event trapping (manual ON KEY) ------------------------------------- #
    def do_on_key(self, n, target):
        """ON KEY(n) GOSUB/GOTO line | ON KEY(n) OFF | ON KEY OFF
        (manual ON KEY).  Setting a trap leaves its event
        disabled; KEY(n) ON activates trapping for that key."""
        if n is not None:
            n = int(n)
            if not (1 <= n <= 20):
                raise BasicError("Illegal function call")
        if target is None:
            # ON KEY OFF clears every trap; ON KEY(n) OFF clears key n.
            if n is None:
                self.key_traps.clear()
            else:
                self.key_traps.pop(n, None)
            return
        if n is None:
            # Bare "ON KEY GOTO/GOSUB" (undocumented): accepted for
            # compatibility, but no specific key is trapped.
            return
        kind, line = target
        self.key_traps[n] = {
            'kind': kind, 'line': line,
            'state': 'off',       # on | off | stop (manual ON KEY)
            'was_on': False,      # the event was ON when the trap fired
            'explicit': False,    # trap routine changed the state itself
            'pending': False,     # event happened while state was 'stop'
            'in_trap': False,     # inside a GOTO trap awaiting a RETURN
        }

    def do_key_state(self, n, mode):
        """KEY(n) ON | OFF | STOP: control trapping of key n (manual ON
        KEY).  ON activates trapping (firing an event that happened while
        the event was STOP immediately); OFF disables it and forgets any
        pending event; STOP disables it but remembers the next event."""
        n = int(self.eval(n))
        t = self.key_traps.get(n)
        if t is None:
            return
        t['explicit'] = True
        t['in_trap'] = False
        if mode == 'on':
            if t['pending']:
                t['pending'] = False
                self._fire_key_trap(n, t)  # raises
                return
            t['state'] = 'on'
        elif mode == 'off':
            t['state'] = 'off'
            t['pending'] = False
        else:  # 'stop'
            t['state'] = 'stop'
            t['pending'] = False

    def _fire_key_trap(self, n, t):
        """Branch to the trap for key n.  The event is automatically
        stopped for the duration of the trap (no recursive traps); the
        RETURN that ends the trap re-arms it (manual ON KEY / RETURN)."""
        t['state'] = 'off'
        t['was_on'] = True
        t['explicit'] = False
        t['pending'] = False
        line = t['line']
        if line not in self.program:
            # Same as GOTO/GOSUB to an undefined line: route through the
            # normal error-trap path (ERR/ERL, then halt if untrapped).
            self._trap_or_raise(BasicError("Undefined line number"))
            return
        if t['kind'] == 'gosub':
            raise Gosub(line, trap_key=n)
        t['in_trap'] = True
        raise Goto(line)

    def _rearm_key(self, n):
        """Re-arm key n's event after its trap returns: automatically ON
        unless an explicit KEY(n) OFF/STOP/ON was done inside the trap."""
        t = self.key_traps.get(n)
        if t is None:
            return
        if t['was_on'] and not t['explicit']:
            t['state'] = 'on'
        t['was_on'] = False

    def _check_key_traps(self):
        """Statement-start event check (manual ON COM/KEY): pump pending
        console keys, fire the trap of any trapped key that was pressed,
        and expand pressed F1-F10 keys into their KEY n assignment string.
        No trapping happens in direct mode or while an error handler is
        active (an error trap disables all trapping)."""
        if self._immediate_mode or self.error_line is not None:
            return
        if not self._trap:
            # TRAP OFF: bypass the ON KEY/COM polling entirely (the
            # program has declared it no longer needs the trap net).
            return
        traps_active = any(t['state'] in ('on', 'stop')
                           for t in self.key_traps.values())
        if not traps_active and not self.system.key_events:
            return
        self.system.pump_key_events()
        events = self.system.key_events
        i = 0
        while i < len(events):
            ev = events[i]
            n = self._key_event_number(ev)
            t = self.key_traps.get(n) if n is not None else None
            if (t is not None
                    and t['state'] in ('on', 'stop')):
                if t['state'] == 'on':
                    del events[i]  # a trapped key is consumed by the trap
                    self._fire_key_trap(n, t)  # raises
                    return
                del events[i]  # remembered; KEY(n) ON fires it
                t['pending'] = True
                continue
            self._expand_function_key(ev, i)
            i += 1

    def _key_event_number(self, ev):
        """Logical GW-BASIC key number (1-20) for a raw key event, or None.

        11-14 are the cursor keys (11 up, 12 left, 13 right, 14 down);
        1-10 are F1-F10 (scan codes 59-68, manual ON KEY); 15-20 are the
        user-defined keys from KEY(n),CHR$(hex code)+CHR$(scan code),
        matched by scan code and modifier mask."""
        token = ev.get('token')
        if token == 'up':
            return 11
        if token == 'left':
            return 12
        if token == 'right':
            return 13
        if token == 'down':
            return 14
        scan = ev.get('scan')
        if scan is None:
            return None
        if 59 <= scan <= 68:
            return scan - 58
        mask = ev.get('mask', 0)
        for n in range(15, 21):
            d = self.key_defs.get(n)
            if not isinstance(d, tuple):
                continue
            hexc, kscan = d
            if kscan != scan:
                continue
            if hexc == 0:
                return n
            if hexc & 0x03 == 0x03:
                # &H03 couples the two SHIFT keys: either one suffices.
                if ((mask & hexc & ~0x03) == (hexc & ~0x03)
                        and (mask & 0x03) != 0):
                    return n
            elif (mask & hexc) == hexc:
                return n
        return None

    def _expand_function_key(self, ev, i):
        """Expand a pressed F1-F10 key into its KEY n assignment string
        (manual KEY: "When the key is pressed, the data assigned to it
        will be input to the program"; INKEY$ then returns one character
        of the string per invocation).  A disabled key (null string) or
        one with no assignment reports CHR$(0)+CHR$(scan code)."""
        scan = ev.get('scan')
        if scan is None or not (59 <= scan <= 68):
            return
        n = scan - 58
        t = self.key_traps.get(n)
        if t is not None and t['state'] in ('on', 'stop'):
            return  # the trap consumes the key (or has remembered it)
        s = self.key_defs.get(n)
        if s is None or s == '':
            ev['ch'] = chr(0) + chr(scan)
            return
        events = self.system.key_events
        events[i:i + 1] = [{'ch': c, 'token': None, 'scan': None, 'mask': 0}
                           for c in s]

    def exec_action(self, action):
        if action == ('fall',):
            return
        if action[0] == 'goto':
            raise Goto(action[1])
        if action[0] == 'stmt':
            self.execute_statement(action[1])

    def exec_actions(self, actions):
        self._exec_actions_seq(actions, 0, len(actions))

    def _exec_actions_seq(self, actions, i, n):
        """Execute a (slice of the) IF action list, owning any same-line
        FOR/DO/WHILE loops it contains.

        A single-line IF ... THEN FOR ... : body : NEXT (or DO ... : LOOP /
        WHILE ... : WEND) is folded by the parser into one ('if', cond, actions)
        node.  The real do_for/do_do/do_while locate their body and terminating
        NEXT/LOOP/WEND from self.pc / self.cur_stmt_idx, which in this in-IF
        context are the IF's own single-statement line -- so they would treat
        the body as a *later* line and run only once.  Instead we drive those
        loops here over the flat action list, matching each NEXT/LOOP/WEND to
        its opener by nesting depth, so nested and adjacent loops work.  We use
        a local stack and never touch self.for_stack / self.do_stack, so no
        state leaks to the caller and control simply falls through to the
        statement after the NEXT/LOOP/WEND.

        A GOSUB raised by any action annotates the exception with this
        frame's continuation, a list of steps (see _exec_action_steps):
        a plain GOSUB resumes with the slice of the list following the
        action, a GOSUB entered by an ON KEY(n) trap with the slice
        starting at the interrupted action.  _step_line's Gosub handler
        pushes that continuation on the GOSUB stack so the RETURN can
        resume the action list mid-way (a GOSUB raised deeper in a nested
        loop body already carries its own continuation, innermost wins).
        """
        try:
            while i < n:
                i = self._exec_one_action(actions, i, n)
        except Gosub as g:
            if g.resume is None:
                # The GOSUB is this frame's own action: the continuation is
                # the rest of the slice (a key-trap GOSUB interrupted
                # action i, so it resumes there).
                g.resume = [('slice', actions,
                             i if g.trap_key is not None else i + 1, n)]
            raise
        except Break as b:
            # Record the STOP's action index (innermost frame wins) so a
            # CONT can resume the action list after it.
            if b.action_idx is None:
                b.action_idx = i
            raise

    def _exec_one_action(self, actions, i, n):
        """Execute action i of an IF action list (driving any same-line
        FOR/DO/WHILE loop it opens); return the index to continue with."""
        action = actions[i]
        if action[0] != 'stmt':
            self.exec_action(action)  # goto / fall
            return i + 1
        stmt = action[1]
        tag = stmt[0]
        if tag == 'for':
            # ('for', var, start, end, step)
            loop_end = self._stmt_span(actions, i, 'for', 'next', n)
            if loop_end is None:
                # No matching NEXT on this line: malformed; run once as-is.
                self.exec_action(action)
                return i + 1
            # The body is every statement after the FOR up to (not
            # including) the matching NEXT: slice [i+1, loop_end).
            body_end = loop_end
            var, start_e, end_e, step_e = stmt[1], stmt[2], stmt[3], stmt[4]
            start = self.eval(start_e)
            end = self.eval(end_e)
            step = self.eval(step_e)
            self.assign(var, start)
            if not self.for_should_continue(start, end, step):
                # Empty loop: the counter is already out of range, so the
                # body never runs (mirrors do_for's early exit).
                return loop_end + 1
            # do-while: run the body once, then keep looping while the
            # advanced counter is still in range (mirrors do_for/_advance_for
            # which test before adding the step: read live var, add step).
            while True:
                try:
                    self._exec_actions_seq(actions, i + 1, body_end)
                except Gosub as g:
                    # A GOSUB in the body resumes at: the rest of this
                    # pass (recorded by the inner frame), the loop from
                    # the counter's current value, then the actions
                    # after the NEXT (all still inside this slice).
                    g.resume = list(g.resume or []) + [
                        ('for', actions, i + 1, body_end, var, end, step),
                        ('slice', actions, loop_end + 1, n),
                    ]
                    raise
                cur = self.get_var(var)
                if not isinstance(cur, (int, float)):
                    cur = 0
                cur = cur + step
                self.assign(var, cur)
                if not self.for_should_continue(cur, end, step):
                    break
            return loop_end + 1
        elif tag == 'do':
            # ('do', cond_or_None) -- the DO line's condition (if any)
            # is pre-tested: an unsatisfied condition skips the body and
            # the matching LOOP entirely (mirrors do_do).  The LOOP's own
            # condition, if any, is post-tested after each pass (mirrors
            # do_loop); a bare LOOP repeats under the DO condition's
            # pre-test re-run (an unconditioned DO...LOOP loops forever).
            loop_end = self._stmt_span(actions, i, 'do', 'loop', n)
            if loop_end is None:
                self.exec_action(action)
                return i + 1
            # Body is every statement after the DO up to (not including)
            # the matching LOOP: slice [i+1, loop_end).
            pre_cond = stmt[1]
            if pre_cond is not None and not self._loop_condition_holds(pre_cond):
                return loop_end + 1
            body_end = loop_end
            loop_cond = actions[loop_end][1][1]
            if loop_cond is None:
                loop_cond = pre_cond  # bare LOOP: governed by the pre-test
            while True:
                try:
                    self._exec_actions_seq(actions, i + 1, body_end)
                except Gosub as g:
                    g.resume = list(g.resume or []) + [
                        ('do', actions, i + 1, body_end, loop_cond),
                        ('slice', actions, loop_end + 1, n),
                    ]
                    raise
                if not self._loop_condition_holds(loop_cond):
                    break
            return loop_end + 1
        elif tag == 'while':
            # ('while', cond) -- condition checked before each pass.
            loop_end = self._stmt_span(actions, i, 'while', 'wend', n)
            if loop_end is None:
                self.exec_action(action)
                return i + 1
            # Body is every statement after the WHILE up to (not
            # including) the matching WEND: slice [i+1, loop_end).
            # The WHILE node is ('while', expr); the condition is a plain
            # expression (true = keep looping), unlike DO/LOOP which wrap
            # their condition as ('while'/'until', expr).
            body_end = loop_end
            while bool(self.eval(stmt[1])):
                try:
                    self._exec_actions_seq(actions, i + 1, body_end)
                except Gosub as g:
                    g.resume = list(g.resume or []) + [
                        ('while', actions, i + 1, body_end, stmt[1]),
                        ('slice', actions, loop_end + 1, n),
                    ]
                    raise
            return loop_end + 1
        else:
            self.exec_action(action)
            return i + 1

    def _exec_action_steps(self, steps, if_line, line, stmt_idx):
        """Execute a GOSUB continuation (a list of slice/loop steps) left
        by a RETURN from a GOSUB inside IF actions.  A GOSUB raised by a
        step re-records the continuation from that point (its own steps
        plus the steps still pending here); a STOP rewinds the steps past
        the STOP so CONT can pick up after it."""
        i = 0
        n = len(steps)
        while i < n:
            try:
                self._exec_action_step(steps[i])
            except Gosub as g:
                if g.resume is None:
                    g.resume = []
                step_i = steps[i]
                if step_i[0] != 'slice':
                    # A GOSUB in a loop step's body re-entry: the loop
                    # itself keeps running after the pass the GOSUB left.
                    g.resume = list(g.resume) + [step_i]
                g.resume = list(g.resume) + list(steps[i + 1:])
                raise
            except Break as b:
                if b.action_idx is not None:
                    step_i = steps[i]
                    skip_to = b.action_idx + 1
                    if step_i[0] == 'slice':
                        a, s, e = step_i[1], step_i[2], step_i[3]
                        rest = ([('slice', a, skip_to, e)]
                                if skip_to < e else [])
                    else:
                        # A loop step: the rest of the current body pass,
                        # then the loop itself.
                        a, body_first, body_end = step_i[1], step_i[2], step_i[3]
                        rest = ([('slice', a, skip_to, body_end)]
                                if skip_to < body_end else []) + [step_i]
                    self._resume_actions = (rest + list(steps[i + 1:]),
                                            if_line, line, stmt_idx)
                raise
            i += 1

    def _exec_action_step(self, step):
        """Execute one continuation step: a slice of the IF action list, or
        the resumption of the same-line loop that contains the GOSUB."""
        kind = step[0]
        if kind == 'slice':
            self._exec_actions_seq(step[1], step[2], step[3])
        elif kind == 'for':
            # Advance-then-test, mirroring _exec_one_action's FOR loop from
            # the counter's current (possibly subroutine-modified) value.
            actions, body_first, body_end, var, end, step_ = step[1:7]
            while True:
                cur = self.get_var(var)
                if not isinstance(cur, (int, float)):
                    cur = 0
                cur = cur + step_
                self.assign(var, cur)
                if not self.for_should_continue(cur, end, step_):
                    break
                self._exec_actions_seq(actions, body_first, body_end)
        elif kind == 'do':
            actions, body_first, body_end, cond = step[1:5]
            while self._loop_condition_holds(cond):
                self._exec_actions_seq(actions, body_first, body_end)
        elif kind == 'while':
            actions, body_first, body_end, cond = step[1:5]
            while bool(self.eval(cond)):
                self._exec_actions_seq(actions, body_first, body_end)

    def _stmt_span(self, actions, start, open_tag, close_tag, limit):
        """Return the index of the NEXT/LOOP/WEND matching the loop that
        opens at ``actions[start]`` (tag == open_tag), scanning up to ``limit``,
        or None if not closed within the slice.  Nested openers of the same
        kind are matched by depth."""
        depth = 1
        j = start + 1
        while j < limit:
            if actions[j][0] == 'stmt':
                tag = actions[j][1][0]
                if tag == open_tag:
                    depth += 1
                elif tag == close_tag:
                    depth -= 1
                    if depth == 0:
                        return j
            j += 1
        return None

    def _loop_condition_holds(self, cond):
        """Evaluate a (kind, expr) loop condition.  ``while`` loops while true,
        ``until`` loops while false.  ``cond`` of None means unconditional."""
        if cond is None:
            return True
        kind, expr = cond
        val = bool(self.eval(expr))
        return (kind == 'while' and val) or (kind == 'until' and not val)

    def do_print(self, items):
        out = []
        col = 0
        for item in items:
            if item[0] == 'using':
                text = self.format_using(str(self.eval(item[1])),
                                         [self.eval(a) for a in item[2]])
                out.append(text)
                col += len(text)
                continue
            first = item[0]
            sep = item[1]
            if isinstance(first, tuple) and first[0] in ('__tab__', '__spc__'):
                marker, n, expr = first
                n_val = int(self.eval(n))
                if marker == '__tab__':
                    if n_val < 1 or n_val > 255:
                        raise BasicError("Illegal function call")
                    target = n_val - 1  # 1-based column -> 0-based index
                    if target > col:
                        out.append(' ' * (target - col))
                        col = target
                    else:
                        # Already beyond space n: TAB goes to that position
                        # on the NEXT LINE (manual TAB).
                        out.append('\n' + ' ' * target)
                        col = target
                else:
                    if n_val < 0 or n_val > 255:
                        raise BasicError("Illegal function call")
                    # n greater than the screen width wraps: n MOD width
                    # (manual SPC).
                    width = self.screen.cols
                    if width > 0 and n_val > width:
                        n_val = n_val % width
                    if n_val > 0:
                        out.append(' ' * n_val)
                        col += n_val
                if expr is not None:
                    # Trailing TAB/SPC (no item after it) only positions;
                    # there is no value to print (manual TAB/SPC).
                    value, k = self.eval_with_kind(expr)
                    s = self.format_value_kind(value, k)
                    out.append(s)
                    col += len(s)
                    if sep == ',':
                        next_zone = ((col // 14) + 1) * 14
                        out.append(' ' * (next_zone - col))
                        col = next_zone
                continue
            expr, sep = item
            value, k = self.eval_with_kind(expr)
            s = self.format_value_kind(value, k)
            out.append(s)
            col += len(s)
            if sep == ',':
                next_zone = ((col // 14) + 1) * 14
                out.append(' ' * (next_zone - col))
                col = next_zone
        text = ''.join(out)
        last = items[-1] if items else None
        # A trailing ';' or ',' suppresses the newline (GW-BASIC behavior).
        # A TAB/SPC is not itself a data item: it positions the item that
        # follows it, so the newline is governed by that item's own separator
        # (last[1]), not by the presence of the TAB/SPC marker (manual TAB/SPC).
        suppress = False
        if last is not None:
            if last[0] == 'using':
                suppress = False
            elif (isinstance(last[0], tuple)
                    and last[0][0] in ('__tab__', '__spc__')
                    and last[0][2] is None):
                # A TAB/SPC at the end of the list (no item after it) has an
                # implied semicolon: no line return (manual TAB/SPC).
                suppress = True
            else:
                suppress = last[1] in (';', ',')
        self.write(text, newline=not suppress)

    def do_input(self, prompt, var_names, suppress_qmark=False):
        while True:
            if prompt is not None:
                p = self.eval(prompt)
                if p:
                    if not suppress_qmark and p[-1] not in '?':
                        p = p + '? '
                    self.write(p, newline=False)
                else:
                    self.write('?', newline=False)
            else:
                self.write('?', newline=False)
            try:
                line = self.io.read_line().strip()
            except EOFError:
                raise BasicError("Input past end (62)")
            if line == '':
                continue
            if line == '?':
                self.write("Type values separated by commas.\n")
                continue
            # Commas inside a quoted string are part of the string
            # (manual INPUT); only unquoted commas separate items.
            parts = [p.strip() for p in FileIO._split_unquoted_commas(line)]
            if len(parts) != len(var_names):
                # Too few OR too many items both cause a redo.
                self.write("?Redo from start\n")
                continue
            values = []
            ok = True
            for name, part in zip(var_names, parts):
                vt = self.var_type(name)
                if vt not in ('string', 'default'):
                    # Declared numeric target (%, !, # or DEFINT/DEFSNG/
                    # DEFDBL): numeric data only.
                    try:
                        v = float(part)
                    except ValueError:
                        ok = False
                        break
                    if math.isinf(v):
                        self.write("Overflow", newline=True)
                        ok = False
                        break
                    val = int(v) if v == int(v) else v
                    if isinstance(val, float) and classify_number(part) == 'single':
                        val = round_single(val)
                    values.append(val)
                elif part.startswith('"') and part.endswith('"') and len(part) >= 2:
                    # Quoted data is a string for any remaining target.
                    values.append(part[1:-1])
                elif vt == 'string':
                    values.append(part)
                else:
                    try:
                        v = float(part)
                    except ValueError:
                        # Untyped target: string data is accepted - an
                        # untyped variable can hold a string (same rule as
                        # INPUT# and assignment).
                        values.append(part)
                    else:
                        if math.isinf(v):
                            # Out-of-range value typed at the INPUT prompt:
                            # real GW-BASIC prints "Overflow" and redoes the
                            # input (its source's CKOVER/??L030 path), so
                            # treat it as a failed parse instead of crashing
                            # on int(inf).
                            self.write("Overflow", newline=True)
                            ok = False
                            break
                        val = int(v) if v == int(v) else v
                        if isinstance(val, float) and classify_number(part) == 'single':
                            val = round_single(val)
                        values.append(val)
            if not ok:
                self.write("?Redo from start\n")
                continue
            for name, val in zip(var_names, values):
                self.assign(name, val)
            break

    def _filter_skip_else(self, target):
        """Drop stale ELSE-skip markers after a jump to `target`.

        A marker (if_line, else_line) is valid only while control stays
        between the IF line and its ELSE line; a jump past the ELSE line
        (or back to/before the IF line) invalidates it.
        """
        self.skip_else_stack = [
            m for m in self.skip_else_stack if m[0] < target <= m[1]
        ]

    def do_if(self, stmt):
        cond = self.eval(stmt[1])
        then_actions = stmt[2]
        else_actions = stmt[3]
        then_is_fall = (then_actions == [('fall',)])
        # ELSE lines already claimed by in-progress (nested) multi-line
        # IFs; a newly matched ELSE must be a line not already claimed.
        claimed = {m[1] for m in self.skip_else_stack}
        if cond:
            if then_is_fall:
                target = self.find_matching_else(self.pc, claimed)
                if target is not None:
                    self.skip_else_stack.append((self.pc, target[0]))
                # fall through to the THEN block
            else:
                self.exec_actions(then_actions)
                # A THEN statement executed on the IF line does not consume
                # the IF's matching ELSE when that ELSE sits on a later
                # (multi-line) line: mark it so do_else skips it, now that
                # the THEN branch has run.  IFs with an inline ELSE are
                # complete and own no later ELSE line.  Nested IFs inside
                # the THEN statement may have claimed ELSE lines while it
                # ran, so re-read the claimed set here.
                if else_actions is None:
                    target = self.find_matching_else(
                        self.pc, {m[1] for m in self.skip_else_stack})
                    if target is not None:
                        self.skip_else_stack.append((self.pc, target[0]))
        else:
            if else_actions is not None:
                self.exec_actions(else_actions)
            elif then_is_fall:
                # The block ends at the first unmatched ELSE or ENDIF line
                # (ENDIF support: when no ENDIF line is involved the scan
                # is identical to the original find_matching_else).
                target = self.find_if_terminator(self.pc, claimed)
                if target is not None:
                    line, kind, has_stmt = target
                    if kind == 'else':
                        if has_stmt:
                            raise Goto(line)
                        raise Goto(self.next_line_map[line])
                    # kind == 'endif': skip the whole block and continue
                    # with the line after the ENDIF.  .get: the ENDIF may
                    # be the program's last line (Goto(None) ends the run).
                    raise Goto(self.next_line_map.get(line))
                raise Goto(self.next_line_map[self.pc])
            # single-line IF with no ELSE: do nothing

    def do_else(self, stmt):
        action = stmt[1]
        # A matching marker may sit below newer markers when nested
        # multi-line IFs share one start line, so search the whole stack
        # (innermost/newest first) instead of only the top.
        for i in range(len(self.skip_else_stack) - 1, -1, -1):
            if self.skip_else_stack[i][1] == self.pc:
                del self.skip_else_stack[i]
                if action is None:
                    # ELSE block is the following line; skip it.
                    nxt = self.next_line_map[self.pc]
                    raise Goto(self.next_line_map[nxt] if nxt is not None else None)
                raise Goto(self.next_line_map[self.pc])
        if action is None:
            return  # fall into the ELSE block
        self.exec_action(action)

    def do_for(self, stmt):
        var = stmt[1]
        # Manual FORNEXT (reading (b)): "The final value for the loop
        # variable is always set before the initial value is set."
        # EXPERIMENTAL COPY (gwbasic_for_b.py) - the original gwbasic.py
        # evaluates start first and never touches the counter until the
        # final assignment.  Here the counter is assigned the final value
        # before the initial-value expression is evaluated, so a start
        # expression referencing the counter sees the final value; the
        # counter is then re-assigned the initial value.
        end = self.eval(stmt[3])
        self.assign(var, end)
        start = self.eval(stmt[2])
        step = self.eval(stmt[4])
        self.assign(var, start)
        line = self.pc
        idx = self.cur_stmt_idx
        # Body start: the statement after the FOR on the same line (a
        # single-line FOR carries its body on the FOR line), or the next
        # line (a multi-line FOR).
        if idx + 1 < len(self.cur_line):
            body_start = (line, idx + 1)
        else:
            body_start = (self.next_line_map.get(line), 0)
        if not self.for_should_continue(start, end, step):
            # Empty loop: skip to just past the matching NEXT.
            next_pos = self.find_matching_next_pos(line, idx)
            if next_pos is not None:
                nline, nidx = next_pos
                if nidx + 1 < len(self.program[nline]):
                    raise Goto(nline, nidx + 1)
                raise Goto(self.next_line_map.get(nline), 0)
            return
        # Store the counter name in canonical (upper-case) form: BASIC
        # names are case-insensitive, so NEXT matching must be too.
        self.for_stack.append((var.upper(), start, end, step, body_start))

    def do_next(self, var):
        if not self.for_stack:
            raise BasicError("NEXT without FOR")
        if var is None:
            idx = len(self.for_stack) - 1
        else:
            idx = None
            var_up = var.upper()
            for i in range(len(self.for_stack) - 1, -1, -1):
                if self.for_stack[i][0] == var_up:
                    idx = i
                    break
            if idx is None:
                raise BasicError("NEXT without matching FOR")
        self._advance_for(idx)

    def do_next_multi(self, vars):
        # NEXT I,J: close the innermost matching loop, then the next outer
        # matching loop, and so on (manual FORNEXT).  A Goto (loop continue)
        # short-circuits; otherwise continue until no matching FOR remains.
        if not self.for_stack:
            raise BasicError("NEXT without FOR")
        vars_up = [v.upper() for v in vars]
        while True:
            idx = None
            for i in range(len(self.for_stack) - 1, -1, -1):
                if self.for_stack[i][0] in vars_up:
                    idx = i
                    break
            if idx is None:
                return
            self._advance_for(idx)

    def _advance_for(self, idx):
        var_name, current, end, step, body_start = self.for_stack[idx]
        # GW-BASIC: the loop variable may be modified in the body; read its
        # current value before adding the step.
        cur = self.get_var(var_name)
        if not isinstance(cur, (int, float)):
            cur = 0
        current = cur + step
        self.assign(var_name, current)
        if self.for_should_continue(current, end, step):
            self.for_stack[idx] = (var_name, current, end, step, body_start)
            bl, bs = body_start
            raise Goto(bl, bs)
        del self.for_stack[idx]

    def do_locate(self, params):
        # LOCATE [row][,[col][,[cursor][,[start][,stop]]]]
        # param3 = cursor visibility (0=off, nonzero=on); param4/5 = cursor
        # start/stop scan lines (0-31).  row/col are not range-checked:
        # before a SCREENSIZE window exists they record a desktop position
        # for the window's top-left corner, and inside a window they
        # address the text page relative to the window.
        def val(p):
            return int(self.eval(p)) if p is not None else None
        row = val(params[0]) if len(params) > 0 else None
        col = val(params[1]) if len(params) > 1 else None
        cursor = val(params[2]) if len(params) > 2 else None
        start = val(params[3]) if len(params) > 3 else None
        stop = val(params[4]) if len(params) > 4 else None
        # row/col are not range-checked: before a SCREENSIZE window exists
        # they record a desktop pixel position for the window's top-left
        # corner (any value, e.g. LOCATE 400,300), and inside a window they
        # address the text page relative to the window.
        if row is not None or col is not None:
            # row/col are 1-based (manual LOCATE); the screen's cursor
            # coordinates are 0-based (csrlin() returns cursor_row + 1).
            self.screen.locate(row - 1 if row is not None else self.screen.cursor_row,
                               col - 1 if col is not None else self.screen.cursor_col)
        if cursor is not None:
            self.screen.cursor_visible = cursor != 0
        if start is not None:
            if start < 0 or start > 31:
                raise BasicError("Illegal function call")
            self.screen.cursor_start = start
        if stop is not None:
            if stop < 0 or stop > 31:
                raise BasicError("Illegal function call")
            self.screen.cursor_stop = stop
        # Record where this LOCATE left the cursor (1-based): the next
        # SCREENSIZE places the OS window's top-left corner there.  Captured
        # after the row/col handling, so a partial LOCATE ("LOCATE 5" or
        # "LOCATE ,7") records the full resulting position.
        self.screen.locate_pos = (self.screen.cursor_row + 1,
                                  self.screen.cursor_col + 1)

    def do_resume(self, line=None):
        if self.error_line is None:
            raise BasicError("RESUME without error")
        # RESUME or RESUME 0 resumes at the statement that caused the error.
        if line is None or int(line) == 0:
            target = self.error_line
        else:
            target = int(line)
        # Clear error_line (a fresh error at/after the target may trap again)
        # and arm a one-shot re-run guard: RESUME/RESUME 0 re-executes the
        # statement that errored, and if it errors AGAIN it must abort rather
        # than re-trap - an unconditional RESUME to a line that always errors
        # would otherwise loop forever.  The guard is consumed by the first
        # error on that line, or discarded once the line has executed cleanly,
        # so a genuinely NEW error on a LATER line still traps normally.
        self.error_line = None
        self._resume_suppress = True
        raise Goto(target, 0, True)

    def do_resume_next(self):
        if self.error_line is None:
            raise BasicError("RESUME without error")
        nxt = self.next_line_map.get(self.error_line)
        # Clear error_line; RESUME NEXT resumes at the line AFTER the erroring
        # one, so there is no re-run of the failing statement to guard against.
        # The handler flag is disarmed when the Goto is caught (error_line is
        # None), so a fresh error afterwards traps normally.
        self.error_line = None
        if nxt is None:
            raise Stop()
        raise Goto(nxt, 0, True)

    def do_restore(self, line=None):
        if line is None:
            self.data_ptr = 0
            return
        target = int(line)
        # Manual RESTORE: the next READ accesses the first item in the
        # specified DATA statement.  When target is not itself a DATA
        # line, use the first DATA line at/after target (standard
        # GW-BASIC); with no DATA line at/after target the pool is
        # exhausted and the next READ is "OUT OF DATA".
        for ln in sorted(self.data_line_map):
            if ln >= target:
                self.data_ptr = self.data_line_map[ln]
                return
        self.data_ptr = len(self.data)

    def do_while(self, stmt):
        pos = self.find_matching_wend_pos(self.pc, self.cur_stmt_idx)
        if pos is None:
            raise BasicError("WHILE without WEND")
        wend_line, wend_idx = pos
        cond = self.eval(stmt[1])
        if not cond:
            # Do not push onto while_stack: we are not entering the loop,
            # so there is no matching WEND to pop. Pushing here would leave
            # a stale entry that corrupts nested WHILE/WEND matching.  Skip
            # to the statement after the WEND (same line for a single-line
            # WHILE, or the next line).
            if wend_idx + 1 < len(self.program[wend_line]):
                raise Goto(wend_line, wend_idx + 1)
            raise Goto(self.next_line_map.get(wend_line), 0)
        # Body start: the statement after the WHILE on the same line (a
        # single-line WHILE carries its body on the WHILE line), or the next
        # line (a multi-line WHILE).
        if self.cur_stmt_idx + 1 < len(self.cur_line):
            body_start = (self.pc, self.cur_stmt_idx + 1)
        else:
            body_start = (self.next_line_map.get(self.pc), 0)
        self.while_stack.append((self.pc, self.cur_stmt_idx, body_start))

    def do_wend(self):
        if not self.while_stack:
            raise BasicError("WEND without WHILE")
        while_line, while_idx, _ = self.while_stack.pop()
        # Re-execute the WHILE so its condition is re-tested and the stack
        # entry re-pushed (same pattern as DO/LOOP's back-edge).
        raise Goto(while_line, while_idx)

    def _on_index(self, expr, lines):
        # GW-BASIC rounds the (non-integer) value, then requires 1..len(lines);
        # negative or >255 is an "Illegal function call".
        if not isinstance(expr, (int, float)):
            raise BasicError("Illegal function call")
        if expr < 0 or expr > 255:
            raise BasicError("Illegal function call")
        idx = int(expr + 0.5) if expr >= 0 else int(expr - 0.5)
        if 1 <= idx <= len(lines):
            return idx
        return None

    def do_on_goto(self, stmt):
        idx = self._on_index(self.eval(stmt[1]), stmt[2])
        if idx is not None:
            raise Goto(stmt[2][idx - 1])

    def do_on_gosub(self, stmt):
        idx = self._on_index(self.eval(stmt[1]), stmt[2])
        if idx is not None:
            raise Gosub(stmt[2][idx - 1])

    def do_read(self, targets):
        for target in targets:
            if self.data_ptr >= len(self.data):
                raise BasicError("Out of DATA")
            is_string, value = self.data[self.data_ptr]
            self.data_ptr += 1
            if target[0] == 'var':
                name = target[1]
                vt = self.var_type(name)
                if vt == 'string':
                    if not is_string:
                        raise BasicError("Type Mismatch")
                    self.vars[name] = value
                else:
                    if is_string:
                        raise BasicError("Type Mismatch")
                    self.vars[name] = self.coerce(name, value)
            else:
                name = target[1]
                idx = tuple(int(self.eval(e)) for e in target[2])
                self._check_bounds(name, idx)
                if name not in self.arrays:
                    self.arrays[name] = {}
                vt = self.var_type(name)
                if vt == 'string':
                    if not is_string:
                        raise BasicError("Type Mismatch")
                    self.arrays[name][idx] = value
                else:
                    if is_string:
                        raise BasicError("Type Mismatch")
                    self.arrays[name][idx] = self.coerce(name, value)

    def do_def_type(self, stmt):
        type_name = stmt[1]
        for name in stmt[2]:
            self.def_types[name.upper()] = type_name

    def _arrays_in_use(self):
        # True if any array has been dimensioned (DIM/REDIM) or implicitly
        # created, i.e. its bounds are recorded.
        return len(self.array_dims) > 0

    def do_dim(self, stmt):
        # DIM name(dims)[,name(dims)...] - multiple arrays per statement.
        for name, dims_expr in stmt[1]:
            dims = [int(self.eval(d)) for d in dims_expr]
            base = self.option_base
            for d in dims:
                if d < base:
                    raise BasicError("Illegal dimension")
            if len(dims) > 255:
                raise BasicError("Illegal dimension")
            # An array already explicitly dimensioned cannot be re-DIM'd
            # without a prior ERASE/CLEAR ("Duplicate Definition", err 10).
            if name in self.array_dims and self.array_dims[name][2]:
                raise BasicError("Duplicate Definition")
            self.array_dims[name] = (base, dims, True)
            if name in self.arrays:
                # Manual (DIM): "The DIM statement sets all the elements
                # of the specified arrays to an initial value of zero."  This
                # matters for arrays already in implicit use, e.g.
                #   A(3)=7 : DIM A(5)  ->  A(3) is reset to 0.
                if self.var_type(name) == 'string':
                    zero = ""
                else:
                    zero = self.coerce(name, 0)
                for idx in self.arrays[name]:
                    self.arrays[name][idx] = zero
            else:
                self.arrays[name] = {}

    def do_erase(self, names):
        # ERASE list of array variables.
        for name in names:
            self.arrays[name] = {}
            self.array_dims.pop(name, None)

    def do_swap(self, stmt):
        a, b = stmt[1], stmt[2]
        # The two variables must be of the same type.
        ta = self._target_type(a)
        tb = self._target_type(b)
        if (ta == 'string') != (tb == 'string'):
            raise BasicError("Type mismatch")
        va = self.eval_target(a)
        vb = self.eval_target(b)
        self.assign_target(a, vb)
        self.assign_target(b, va)

    def _target_type(self, target):
        name = target[1]
        if self.var_type(name) == 'string':
            return 'string'
        return 'numeric'

    def _check_let_type(self, target, value):
        # A typeless variable (no suffix, no DEFxxx) may hold either a number
        # or a string; using it later in the wrong context raises a Type
        # mismatch.  Typed variables must match on assignment: a string
        # variable ($ or DEFSTR) may only receive a string value, and a
        # numeric variable (%, !, # or DEFINT/DEFSNG/DEFDBL) may only receive
        # a numeric value.  Assigning the wrong type to a typed variable is a
        # "Type mismatch": GW-BASIC does not implicitly convert (e.g. X$ = 3
        # or X$ = INSTR(...) is a Type mismatch).
        vt = self.var_type(target[1])
        if vt == 'default':
            return
        is_str = isinstance(value, str)
        if vt == 'string' and not is_str:
            raise BasicError("Type mismatch")
        if vt in ('integer', 'single', 'double') and is_str:
            raise BasicError("Type mismatch")

    # -- file I/O statements ------------------------------------------------- #
    def do_open(self, stmt):
        # The mode is either a mode word stored as a plain string by the
        # parser (OPEN ... FOR OUTPUT, or the first-syntax form
        # OPEN OUTPUT, 1, "file") or an expression node (string constant
        # "I"/"O"/"R"/"A"/"B", a full word, or a number 0-4).
        if stmt[1] is None:
            mode = None
        elif isinstance(stmt[1], str):
            mode = stmt[1]
        else:
            mode = self.eval(stmt[1])
        filenum = int(self.eval(stmt[2]))
        # The OPEN ... FOR form stores the filename as a plain string.
        filename = stmt[3] if isinstance(stmt[3], str) else self.eval(stmt[3])
        # reclen omitted -> 128-byte records (manual OPEN).
        record_len = int(self.eval(stmt[4])) if stmt[4] is not None else 128
        # Manual OPEN: reclen within 1-32767, else "Illegal function call";
        # the file is not opened.
        if record_len < 1 or record_len > 32767:
            raise BasicError("Illegal function call")
        if mode is None:
            mode_str = 'INPUT'
        elif isinstance(mode, str):
            mode_map = {'I': 'INPUT', 'O': 'OUTPUT', 'R': 'RANDOM',
                        'A': 'APPEND', 'B': 'BINARY',
                        'INPUT': 'INPUT', 'OUTPUT': 'OUTPUT',
                        'APPEND': 'APPEND', 'RANDOM': 'RANDOM',
                        'BINARY': 'BINARY'}
            mode_str = mode_map.get(mode.upper())
            if mode_str is None:
                raise BasicError("Bad file mode (54)")
        else:
            mode_map = {0: 'INPUT', 1: 'OUTPUT', 2: 'APPEND',
                        3: 'RANDOM', 4: 'BINARY'}
            mode_str = mode_map.get(int(mode))
            if mode_str is None:
                raise BasicError("Bad file mode (54)")
        # BINARY files are byte streams with no record structure, so there is
        # no record length: each GET/PUT transfers one byte (an explicit
        # reclen is not significant in this mode).
        if mode_str == 'BINARY':
            record_len = 1
        self.files.open(mode_str, filenum, filename, record_len)

    def do_close(self, expr):
        if expr is None:
            self.files.close()
        elif isinstance(expr, list):
            for e in expr:
                self.files.close(int(self.eval(e)))
        else:
            self.files.close(int(self.eval(expr)))

    def do_get(self, stmt):
        filenum = int(self.eval(stmt[1]))
        recnum = self.eval(stmt[2]) if stmt[2] is not None else None
        var = stmt[3]
        # Omitted record number: the next record after the last GET
        # (manual GETF).
        if recnum is None:
            recnum = self.files.next_rec(filenum)
        if var is None:
            record = self.files.get_record(filenum, recnum)
            self._populate_fields(filenum, record)
            return
        is_string = self.var_type(var[1]) == 'string'
        value = self.files.get(filenum, recnum, is_string)
        self.assign_target(var, value)

    def do_get_key(self, var):
        ch = self.system.get()
        if var[0] == 'var':
            self.assign(var[1], ch)
        else:
            self.assign_target(var, ch)

    # -- GET/PUT graphics sprites (manual GET/PUT) ---------------------------- #
    def _sprite_meta(self, values, w, h):
        """Store a captured screen area as (w, h, values).  GW-BASIC packs
        screen captures into a tightly packed block of color indices; w and h
        are the width and height of the captured rectangle (x2-x1+1, y2-y1+1)
        after clamping to the screen.  The program DIMs the array to FNSS4(w,h)
        which equals w*h/2 elements (two pixels per element for 4-bit color);
        the PUT back uses the same w and h to reconstruct the image."""
        return (w, h, list(values))

    def do_get_graphics(self, stmt):
        # GET (x1,y1)-(x2,y2),arr$ (manual GET, graphics).
        x1 = int(self.eval(stmt[1])); y1 = int(self.eval(stmt[2]))
        x2 = int(self.eval(stmt[3])); y2 = int(self.eval(stmt[4]))
        var = stmt[5]
        if x2 < x1:
            x1, x2 = x2, x1
        if y2 < y1:
            y1, y2 = y2, y1
        # Clamp to screen
        cx1 = max(0, x1); cy1 = max(0, y1)
        cx2 = min(self.screen.cols - 1, x2); cy2 = min(self.screen.rows - 1, y2)
        w = max(1, cx2 - cx1 + 1)
        h = max(1, cy2 - cy1 + 1)
        values = self.screen._get_graphics(x1, y1, x2, y2)
        name = var[1]
        self.arrays[name] = {'__sprite__': self._sprite_meta(values, w, h)}

    def do_put_graphics(self, stmt):
        # PUT (x,y),arr$ [,[color][,XOR|OR|AND]] (manual PUT, graphics).
        x = self.eval(stmt[1]); y = self.eval(stmt[2])
        var = stmt[3]
        color = self.eval(stmt[4]) if stmt[4] is not None else None
        mode = stmt[5]
        arr = self.arrays.get(var[1])
        meta = arr.get('__sprite__') if isinstance(arr, dict) else None
        if meta is None:
            raise BasicError("Illegal function call")
        w, h, values = meta
        self.screen._put_graphics(x, y, w, h, values, color, mode)

    def do_put(self, stmt):
        filenum = int(self.eval(stmt[1]))
        recnum = self.eval(stmt[2]) if stmt[2] is not None else None
        # Omitted record number -> the next available record (manual PUTF).
        if recnum is None:
            recnum = self.files.next_rec(filenum)
        data = stmt[3]
        if data is None:
            record = self._build_record(filenum)
            self.files.put_record(filenum, recnum, record)
            return
        # File numeric output is rendered at the value's own precision
        # (manual 6.1.1) using a round-trip writer: a double keeps full
        # precision, and a single is written as the shortest text that
        # reproduces it exactly (so GET/INPUT# recovers the same value).
        value, kind = self.eval_with_kind(data)
        is_string = isinstance(value, str)
        self.files.put(
            filenum, recnum, is_string, value,
            fmt=lambda v, _k=kind: (
                _fmt_num(v) if _k == 'single' else self.format_number_kind(v, _k)))

    def _populate_fields(self, filenum, record):
        for pos, length, var_name in self.fields.get(filenum, []):
            self.assign(var_name, record[pos - 1:pos - 1 + length])

    def _build_record(self, filenum):
        length = self.files.record_len(filenum)
        record = ' ' * length
        for pos, flen, var_name in self.fields.get(filenum, []):
            value = str(self.get_var(var_name))
            record = (record[:pos - 1] + value[:flen].ljust(flen)
                      + record[pos - 1 + flen:])
        return record

    def do_seek(self, stmt):
        filenum = int(self.eval(stmt[1]))
        var = stmt[2]
        self.assign_target(var, self.files.seek(filenum))

    def do_line_input(self, stmt):
        filenum = int(self.eval(stmt[1]))
        var = stmt[2]
        self.assign_target(var, self.files.line_input(filenum))

    def do_line_input_key(self, var, prompt=None):
        # LINE INPUT [;][prompt string;]string variable.
        if prompt is not None:
            p = self.eval(prompt)
            if p:
                self.write(str(p), newline=False)
        try:
            line = self.io.read_line()
        except EOFError:
            raise BasicError("Input past end (62)")
        if var[0] == 'var':
            self.assign(var[1], line)
        else:
            self.assign_target(var, line)

    def do_field(self, stmt):
        # FIELD #n, width AS var [,width AS var]... - contiguous fields
        # starting at position 1 (manual FIELD).
        filenum = int(self.eval(stmt[1]))
        fields = stmt[2]
        reclen = self.files.record_len(filenum)
        pos = 1
        new_fields = []
        for num_expr, var in fields:
            width = int(self.eval(num_expr))
            new_fields.append((pos, width, var[1]))
            pos += width
        if pos - 1 > reclen:
            raise BasicError("FIELD overflow (50)")
        self.fields[filenum] = new_fields

    def do_field_old(self, stmt):
        # Legacy single-field form: FIELD #n, pos, width AS var.
        filenum = int(self.eval(stmt[1]))
        pos = int(self.eval(stmt[2]))
        width = int(self.eval(stmt[3]))
        var = stmt[4]
        reclen = self.files.record_len(filenum)
        if pos + width - 1 > reclen:
            raise BasicError("FIELD overflow (50)")
        self.fields.setdefault(filenum, []).append((pos, width, var[1]))

    def do_redim(self, stmt):
        name = stmt[1]
        dims = [int(self.eval(d)) for d in stmt[2]]
        preserve = stmt[3]
        base = self.option_base
        for d in dims:
            if d < base:
                raise BasicError("Illegal dimension")
        if not preserve or name not in self.arrays:
            self.arrays[name] = {}
        self.array_dims[name] = (base, dims, True)

    def _load_program_file(self, filename):
        """Load a .BAS file into a new program dict (manual LOAD/RUN).

        The .BAS extension is assumed when the name has none.
        Returns the program dict; raises "File not found (53)" if missing.
        """
        filename = str(filename)
        if not os.path.exists(filename):
            if not os.path.splitext(filename)[1] and os.path.exists(filename + '.BAS'):
                filename = filename + '.BAS'
            else:
                raise BasicError("File not found (53)")
        program = {}
        for ln, rest in _iter_logical_lines(filename):
            program[ln] = parse_program_line(rest)
        return program

    def do_run(self, stmt):
        # RUN [line number] | RUN filename (manual RUN).
        arg = self.eval(stmt[1]) if stmt[1] is not None else None
        if arg is None:
            # Bare RUN: restart the current program from its first line.
            self.reset_state()
            target = self.lines[0] if self.lines else None
            if target is None:
                raise Stop()
            self._filter_skip_else(target)
            raise Goto(target)
        if isinstance(arg, str):
            # RUN filename: close files, delete current memory contents,
            # load the file and run it from its first line.
            program = self._load_program_file(arg)
            self.files.close()
            self.program.clear()
            self.program.update(program)
            self.lines = sorted(self.program.keys())
            self.next_line_map = self._build_next_line_map()
            self.build_data_pool()
            self.reset_state()
            self.fields = {}
            target = self.lines[0] if self.lines else None
            if target is None:
                raise Stop()
            self._filter_skip_else(target)
            raise Goto(target)
        # RUN line number: restart state, then begin at that line.
        target = int(arg)
        if target not in self.program:
            raise BasicError("Undefined line number")
        self.reset_state()
        self._filter_skip_else(target)
        raise Goto(target)

    def _sleep_seconds(self, n):
        """Sleep for n seconds, pumping the GUI between small slices so the
        window stays live, up to date and closable (a single blocking
        time.sleep would freeze the window for the entire pause)."""
        try:
            n = float(n)
        except (TypeError, ValueError):
            n = 0.0
        if n <= 0:
            return
        end = time.time() + n
        while True:
            # Ctrl+C while the window is focused: stop immediately instead of
            # waiting for the pause to finish (the run loop also checks this
            # after SLEEP returns, but checking here avoids the wait).
            if self.screen._stop_requested:
                self.screen._stop_requested = False
                raise KeyboardInterrupt
            remaining = end - time.time()
            if remaining <= 0:
                break
            time.sleep(min(0.05, remaining))
            if not self.screen.pump():
                break  # window closed during the pause

    def do_wait(self, args):
        # WAIT port, n[, j] (manual WAIT): suspend until
        # (INport(port) XOR j) AND n is nonzero.  A single argument is
        # treated as a short delay (extension used by this interpreter).
        if len(args) == 1:
            v = self.eval(args[0])
            if isinstance(v, (int, float)) and v > 0:
                self._sleep_seconds(min(float(v), 5.0))
            return
        port = int(self.eval(args[0]))
        n = int(self.eval(args[1]))
        j = int(self.eval(args[2])) if len(args) > 2 else 0
        # n and j must be integer expressions in the range 0 to 255
        # (manual WAIT; Appendix A lists an improper argument to WAIT
        # under error 5, "Illegal function call").
        if n < 0 or n > 255 or j < 0 or j > 255:
            raise BasicError("Illegal function call")
        # Bounded loop: simulated ports are static, so a condition that
        # never becomes true must not hang the interpreter.
        for _ in range(100000):
            if ((self.system.inp(port) ^ j) & n) != 0:
                return

    def do_error(self, expr):
        # ERROR n (manual ERROR): n must be > 0 and < 255.  Known codes
        # simulate that error with its standard message; unknown codes
        # produce "Unprintable Error".
        n = int(self.eval(expr))
        if n < 1 or n > 254:
            raise BasicError("Illegal function call")
        raise BasicError(self._error_message(n), code=n)

    def _error_message(self, n):
        """Standard error message for a GW-BASIC error code (Appendix A).

        Codes the manual leaves unlisted (31-49, 56, 59-60, 65, 68, 69,
        ...) fall through to "Unprintable Error"; 37 keeps the
        implementation's "Illegal dimension" message.
        """
        table = {
            1: "NEXT without FOR",
            2: "Syntax error",
            3: "RETURN without GOSUB",
            4: "Out of DATA",
            5: "Illegal function call",
            6: "Overflow",
            7: "Out of memory",
            8: "Undefined line number",
            9: "Subscript out of range",
            10: "Duplicate Definition",
            11: "Division by zero",
            12: "Illegal direct",
            13: "Type mismatch",
            14: "Out of string space",
            15: "String too long",
            16: "String formula too complex",
            17: "Can't continue",
            18: "Undefined user function",
            19: "No RESUME",
            20: "RESUME without error",
            21: "Unprintable Error",
            22: "Missing operand",
            23: "Line buffer overflow",
            24: "Device Timeout",
            25: "Device Fault",
            26: "FOR Without NEXT",
            27: "Out of Paper",
            28: "Unprintable Error",
            29: "WHILE without WEND",
            30: "WEND without WHILE",
            37: "Illegal dimension",
            50: "FIELD overflow",
            51: "Internal error",
            52: "Bad file number",
            53: "File not found",
            54: "Bad file mode",
            55: "File already open",
            57: "Device I/O Error",
            58: "File already exists",
            62: "Input past end",
            63: "Bad record number",
            64: "Bad filename",
            66: "Direct statement in file",
            67: "Too many files",
            70: "Permission Denied",
            71: "Disk not Ready",
            72: "Disk media error",
            73: "Advanced Feature",
            74: "Rename across disks",
            75: "Path/File Access Error",
            76: "Path not found",
        }
        return table.get(n, "Unprintable Error")

    def do_pset_preset(self, stmt):
        # PSET/PRESET (x,y) | x,y | STEP(x,y) [,[color]] (manual PSET).
        # STEP coordinates are relative to the most recently referenced
        # point; the referenced point is remembered for LINE/PSET.
        tag, x, y, color, step = stmt
        xv = self.eval(x)
        yv = self.eval(y)
        if step:
            xv = self.screen.last_x + xv
            yv = self.screen.last_y + yv
        xi, yi = int(xv), int(yv)
        # Manual PSET: coordinate values outside the 16-bit integer range
        # (-32768 to 32767) cause an "Overflow" error.
        if xi < -32768 or xi > 32767 or yi < -32768 or yi > 32767:
            raise BasicError("Overflow")
        self.screen.last_x = xi
        self.screen.last_y = yi
        if tag == 'preset' and color is None:
            # PRESET without a color clears the pixel: standard GW-BASIC
            # PRESET is PSET with color 0.
            c = 0
        else:
            c = self.eval(color) if color is not None else self.screen.fg
            if color is not None and not self.screen.is_text():
                # Manual PSET: a color value beyond the mode's color range
                # (e.g. greater than 3 in SCREEN 1) is an "Illegal function
                # call" error.  Defined RGB() colors (16+) are legal in
                # graphics modes; an UNDEFINED index 16+ is a legal legacy
                # value (it wraps % 16 when stored), so it is accepted.
                ci = int(c)
                # Custom-size modes use a full 256-color (15) palette.
                cmax = GFX_COLOR_MAX.get(self.screen.mode, 15)
                if ci < 0 or (ci > cmax and ci < 16):
                    raise BasicError("Illegal function call")
        if tag == 'pset':
            self.screen.pset(xi, yi, c)
        else:
            self.screen.preset(xi, yi, c)
        # PSET/PRESET reference the point, so DRAW continues from it (manual
        # DRAW: the current position is the last point plotted by PSET/LINE).
        self.screen.last_point = (xi, yi)
        self.last_point = (xi, yi)

    def do_write(self, stmt):
        filenum = stmt[1]
        items = stmt[2]
        if filenum is not None:
            # Each value is written at its own precision (manual 6.1.1): a
            # single with seven digits, a double with up to sixteen, matching
            # the console branch and the screen.  Kinds are resolved here
            # because a value alone does not carry its precision.
            typed = [self.eval_with_kind(e) for e in items]
            values = [v for v, _k in typed]
            fmts = [lambda v, _k=_k: self.format_number_kind(v, _k)
                    for _v, _k in typed]
            self.files.write_typed(int(self.eval(filenum)), values, fmts)
        else:
            parts = []
            for e in items:
                v, k = self.eval_with_kind(e)
                if isinstance(v, str):
                    parts.append('"%s"' % v.replace('"', '""'))
                else:
                    parts.append(self.format_number_kind(v, k))
            # WRITE separates items with a comma and a space (manual WRITE).
            self.write(', '.join(parts))

    def do_mid_assign(self, args, value):
        # MID$(A$, start[, m]) = newval: the replacement never goes beyond
        # the original length of A$ (manual MIDSS).
        name = args[0][1]
        s = str(self.get_var(name))
        orig_len = len(s)
        start = int(self.eval(args[1]))
        if len(args) >= 3:
            m = int(self.eval(args[2]))
        else:
            m = orig_len - start + 1
        new_val = str(self.eval(value))
        if start < 1 or start > orig_len:
            return  # nothing to replace
        use = min(m if m > 0 else 0, orig_len - start + 1)
        new_chars = new_val[:use]
        self.assign(name, s[:start - 1] + new_chars + s[start - 1 + use:])

    def do_lset_rset(self, stmt, left=True):
        # LSET/RSET stringvar = stringexp (manual LSET/RSET): the value is
        # justified in the variable's CURRENT length - LSET left-justified
        # (space-padded on the right), RSET right-justified (space-padded
        # on the left); a longer value is truncated.
        target = stmt[1]
        value = str(self.eval(stmt[2]))
        if target[0] != 'var':
            raise BasicError("Illegal function call")
        name = target[1]
        if self.var_type(name) != 'string':
            raise BasicError("Type mismatch")
        # Fielded variables are justified in the declared FIELD width, not the
        # variable's current length (manual LSET/RSET: "left-justifies the
        # string in the field"); a non-fielded variable uses its current length
        # (manual: "left-justify a string in the variable's current length").
        # Using current length for a field var would blank it when unassigned.
        field_width = None
        for field_list in self.fields.values():
            for pos, width, var_name in field_list:
                if var_name == name:
                    field_width = width
                    break
            if field_width is not None:
                break
        length = field_width if field_width is not None else len(str(self.get_var(name)))
        if left:
            value = value[:length].ljust(length)
        else:
            value = value[-length:] if length else ''
            value = value.rjust(length)
        self.assign(name, value)

    def do_print_file(self, stmt):
        filenum = int(self.eval(stmt[1]))
        items = stmt[3]
        out = []
        col = 0
        # The mandatory comma (or semicolon) after the file number is a
        # syntax separator, not a print-zone separator: the first item of
        # the list starts at column 0 (manual/PRINTF.html: PRINT#1, A with
        # A=26 gives a diskette image of " 26" -- sign column only, no
        # leading zone).  Zones of 14 spaces are created only by commas
        # inside the expression list.
        for item in items:
            if item[0] == 'using':
                text = self.format_using(str(self.eval(item[1])),
                                         [self.eval(a) for a in item[2]])
                out.append(text)
                col += len(text)
                continue
            first = item[0]
            sep = item[1]
            if isinstance(first, tuple) and first[0] in ('__tab__', '__spc__'):
                marker, n, expr = first
                n_val = int(self.eval(n))
                if marker == '__tab__':
                    if n_val < 1 or n_val > 255:
                        raise BasicError("Illegal function call")
                    target = n_val - 1  # 1-based column -> 0-based index
                    if target > col:
                        out.append(' ' * (target - col))
                        col = target
                    else:
                        # Already beyond space n: TAB goes to that position
                        # on the NEXT LINE (manual TAB).
                        out.append('\n' + ' ' * target)
                        col = target
                else:
                    if n_val < 0 or n_val > 255:
                        raise BasicError("Illegal function call")
                    # n greater than the screen width wraps: n MOD width
                    # (manual SPC).
                    width = self.screen.cols
                    if width > 0 and n_val > width:
                        n_val = n_val % width
                    if n_val > 0:
                        out.append(' ' * n_val)
                        col += n_val
                if expr is not None:
                    # Trailing TAB/SPC (no item after it) only positions;
                    # there is no value to print (manual TAB/SPC).
                    value, k = self.eval_with_kind(expr)
                    s = self.format_value_kind(value, k)
                    out.append(s)
                    col += len(s)
                    if sep == ',':
                        next_zone = ((col // 14) + 1) * 14
                        out.append(' ' * (next_zone - col))
                        col = next_zone
                continue
            expr, sep = item
            value, k = self.eval_with_kind(expr)
            s = self.format_value_kind(value, k)
            out.append(s)
            col += len(s)
            if sep == ',':
                next_zone = ((col // 14) + 1) * 14
                out.append(' ' * (next_zone - col))
                col = next_zone
        text = ''.join(out)
        last = items[-1] if items else None
        # A trailing ';' or ',' suppresses the newline (GW-BASIC behavior).
        # A TAB/SPC is not itself a data item: it positions the item that
        # follows it, so the newline is governed by that item's own separator
        # (last[1]), not by the presence of the TAB/SPC marker (manual TAB/SPC).
        suppress = False
        if last is not None:
            if last[0] == 'using':
                suppress = False
            elif (isinstance(last[0], tuple)
                    and last[0][0] in ('__tab__', '__spc__')
                    and last[0][2] is None):
                # A TAB/SPC at the end of the list (no item after it) has an
                # implied semicolon: no line return (manual TAB/SPC).
                suppress = True
            else:
                suppress = last[1] in (';', ',')
        self.files.print_to(filenum, text, newline=not suppress)

    def do_input_file(self, stmt):
        filenum = int(self.eval(stmt[1]))
        var_names = stmt[2]
        target_types = {n.upper(): self.var_type(n) for n in var_names}
        values = self.files.input_from(filenum, var_names, target_types)
        for name, val in zip(var_names, values):
            self.assign(name, val)

    # -- graphics statements ------------------------------------------------- #
    def do_line(self, stmt):
        x1 = self.eval(stmt[1]) if stmt[1] is not None else None
        y1 = self.eval(stmt[2]) if stmt[2] is not None else None
        x2 = self.eval(stmt[3]); y2 = self.eval(stmt[4])
        if x1 is None:
            # Relative form "LINE -(x2,y2)": the omitted first coordinate is
            # the last point referenced by a previous LINE (manual LINE).
            if self.last_point is None:
                raise BasicError("Illegal function call")
            x1, y1 = self.last_point
        color = self.eval(stmt[5]) if stmt[5] is not None else self.screen.fg
        bf = stmt[6] or ''
        style = self.eval(stmt[7]) if stmt[7] is not None else None
        # Manual LINE: the BF parameter used with the style parameter is a
        # "Syntax" error (style is illegal for filled boxes).
        if style is not None and 'F' in bf.upper():
            raise BasicError("Syntax")
        self.screen.line(x1, y1, x2, y2, color, bf, style)
        # LINE references its endpoint, so DRAW continues from it (manual DRAW).
        self.screen.last_point = (int(x2), int(y2))
        self.last_point = (x2, y2)

    def do_circle(self, stmt):
        x = self.eval(stmt[1]); y = self.eval(stmt[2]); r = self.eval(stmt[3])
        color = self.eval(stmt[4]) if stmt[4] is not None else None
        start = self.eval(stmt[5]) if stmt[5] is not None else None
        end = self.eval(stmt[6]) if stmt[6] is not None else None
        aspect = self.eval(stmt[7]) if stmt[7] is not None else None
        # The center of the circle becomes the current graphics position
        # (manual CIRCLE); POINT (function) retrieves it.
        self.screen.last_x = int(x)
        self.screen.last_y = int(y)
        self.screen.circle(x, y, r, color, start, end, aspect)

    def do_paint(self, stmt):
        x = self.eval(stmt[1]); y = self.eval(stmt[2])
        color = self.eval(stmt[3]) if stmt[3] is not None else None
        border = self.eval(stmt[4]) if stmt[4] is not None else None
        bckgrnd = self.eval(stmt[5]) if len(stmt) > 5 and stmt[5] is not None else None
        self.screen.paint(x, y, color, border, bckgrnd)

    def do_mouse(self, stmt):
        # MOUSE x [, y [, button]] (extension): wait for a mouse click on
        # the graphics window; store the click location (world coordinates,
        # matching the active WINDOW mapping) and the button number in the
        # variables.  Closing the window while waiting stops the program,
        # like pressing ESC (there is no "no click" sentinel: world
        # coordinates can legitimately be negative, so -1 would collide).
        var_names = stmt[1]
        screen = self.screen
        if screen.virtual or screen._root is None:
            raise BasicError("Mouse not available (no graphics window)")
        x, y, b = self._mouse_wait()
        wx, wy = screen._phys_to_world(x, y)
        self.assign(var_names[0], wx)
        if len(var_names) > 1:
            self.assign(var_names[1], wy)
        if len(var_names) > 2:
            self.assign(var_names[2], b)

    def _mouse_wait(self):
        """Block until a click is queued for the window.

        Returns the (x, y, button) event.  Mirrors _sleep_seconds: pump the
        GUI between small slices so the window stays live and closable, and
        honour a stop request (ESC / close box) immediately -- closing the
        window while waiting stops the program, like pressing ESC."""
        screen = self.screen
        while True:
            if screen._stop_requested:
                screen._stop_requested = False
                raise KeyboardInterrupt
            ev = screen.pop_mouse_event()
            if ev is not None:
                return ev
            if not screen.pump():
                raise KeyboardInterrupt  # window closed while waiting
            time.sleep(0.005)

    def do_play(self, node):
        # PLAY string expression (manual PLAY): the music macro language.
        s = self.eval(node)
        if not isinstance(s, str):
            raise BasicError("Type Mismatch")
        if PlayMusic(self.system, self).play(s) \
                and self.system._winsound is None:
            # Off-Windows the playback is simulated; approximate a starting
            # note with the terminal bell, like SOUND.
            self.output_func('\a')

    # -- MUSICFILE / PLAYMUSIC -------------------------------------------------- #
    def _music_key(self, ref):
        # The registry key for a music handle: (upper name, index tuple).
        # Validates the reference with the same semantics as any other use
        # of the variable (an array must be DIM'd or an implicit array in
        # range; a string variable or array is a Type Mismatch).
        if ref[0] == 'var':
            name = ref[1]
            if self.var_type(name) == 'string':
                raise BasicError("Type Mismatch")
            return (name.upper(), ())
        name = ref[1]
        idx = tuple(int(self.eval(e)) for e in ref[2])
        self._check_bounds(name, idx)
        if self.var_type(name) == 'string':
            raise BasicError("Type Mismatch")
        return (name.upper(), idx)

    def _music_ref_name(self, ref):
        # The handle spelled as the user wrote it ("a", "abc(2)") for
        # error messages.
        if ref[0] == 'var':
            return ref[1]
        return '%s(%s)' % (ref[1], ', '.join(str(int(self.eval(e)))
                                             for e in ref[2]))

    def do_musicfile(self, ref, path):
        # MUSICFILE variable, file name: bind a .wav/.mp3/.wma file to the
        # variable.
        # The file must exist now (fail fast); playback is PLAYMUSIC's job.
        key = self._music_key(ref)
        if not os.path.exists(path):
            raise BasicError("File not found: %s" % path)
        self.music[key] = path

    def do_playmusic(self, ref):
        # PLAYMUSIC variable: play the bound .wav/.mp3/.wma non-blocking
        # (MCI);
        # a new PLAYMUSIC interrupts the music currently playing (one at a
        # time).  Off-Windows the playback is simulated (terminal bell),
        # like SOUND.
        key = self._music_key(ref)
        if key not in self.music:
            raise BasicError("No music assigned to %s"
                             % self._music_ref_name(ref))
        path = self.music[key]
        if not os.path.exists(path):
            raise BasicError("File not found: %s" % path)
        if not self.system.music_play(path):
            self.output_func('\a')

    # -- DO...LOOP ----------------------------------------------------------- #
    def do_do(self, stmt):
        # DO...LOOP: the DO line's condition, if any, is pre-tested.  If it
        # is not satisfied -- DO WHILE with a false expression, or DO UNTIL
        # with an already-true expression -- the body and the matching LOOP
        # are skipped entirely, and control continues with the statement
        # after the LOOP.  A condition on the LOOP line is post-tested in
        # do_loop; a DO without a condition always runs the body.
        do_cond = stmt[1]
        if do_cond is not None and not self._loop_condition_holds(do_cond):
            pos = self.find_matching_loop_pos(self.pc, self.cur_stmt_idx)
            if pos is not None:
                line, idx = pos
                if idx + 1 < len(self.program[line]):
                    raise Goto(line, idx + 1)
                raise Goto(self.next_line_map.get(line), 0)
            # No matching LOOP (malformed program): fall through as before.
        # Store the DO's position (line + statement index) so a loop-back
        # re-executes the DO (re-pushing the stack) but skips any statements
        # that precede it on the same line.
        self.do_stack.append((self.pc, self.cur_stmt_idx, do_cond))

    def do_loop(self, stmt):
        if not self.do_stack:
            raise BasicError("LOOP without DO")
        do_line, do_idx, do_cond = self.do_stack.pop()
        # The LOOP line's own condition (LOOP WHILE/UNTIL) is the
        # post-condition.  The DO line's condition was already pre-tested in
        # do_do, so a bare LOOP just repeats: looping back re-executes the DO
        # and its pre-test (an unconditioned DO...LOOP loops forever).
        cond = stmt[1]
        if cond is not None and not self._loop_condition_holds(cond):
            return
        raise Goto(do_line, do_idx)

    # -- PRINT USING --------------------------------------------------------- #
    def format_using(self, fmt, args):
        """Format ``args`` per a GW-BASIC PRINT USING format string.

        Implements the format language from the GW-BASIC manual
        (manual/PRINTUSING.html):
          String fields:  !  (first char),  \\n spaces\\  (2+n chars),
                          &  (variable length, as-is)
          Numeric fields: # digit positions, . decimal, leading/trailing +,
                          trailing -, ** / $$ / **$ prefixes, , thousands
                          separator, ^^^^ exponential format
          _  escapes the next character as a literal
          %  is printed in front of a number that overflows its field
        Any other character is printed literally.  Each field consumes the
        next argument in order; when there are more arguments than fields,
        the last field (and the literal text preceding it) is repeated for
        the remaining arguments.
        """
        segments = self._parse_using_format(fmt)
        field_idx = [i for i, s in enumerate(segments) if s[0] == 'field']
        if not field_idx:
            return ''.join(s[1] for s in segments)
        n_fields = len(field_idx)
        tail_start = (field_idx[-2] + 1) if n_fields >= 2 else 0
        tail = segments[tail_start:]
        out = []
        ai = 0
        m = len(args)
        # Segments before the tail
        for seg in segments[:tail_start]:
            if seg[0] == 'lit':
                out.append(seg[1])
            else:
                if ai < m:
                    out.append(self._format_using_field(seg[1], args[ai]))
                    ai += 1
                else:
                    out.append(self._format_using_field(seg[1], None))
        # The tail (contains the last field): once for the last field, then
        # again for each extra argument.
        num_tail = (m - ai) if ai < m else 1
        for _t in range(num_tail):
            for seg in tail:
                if seg[0] == 'lit':
                    out.append(seg[1])
                else:
                    if ai < m:
                        out.append(self._format_using_field(seg[1], args[ai]))
                        ai += 1
                    else:
                        out.append(self._format_using_field(seg[1], None))
        return ''.join(out)

    def _parse_using_format(self, fmt):
        """Parse a PRINT USING format string into literal/field segments."""
        segments = []
        i = 0
        n = len(fmt)
        while i < n:
            c = fmt[i]
            if c == '!':
                segments.append(('field', ('str', 1)))
                i += 1
            elif c == '\\':
                j = i + 1
                spaces = 0
                while j < n and fmt[j] == ' ':
                    spaces += 1
                    j += 1
                if j < n and fmt[j] == '\\':
                    segments.append(('field', ('str', 2 + spaces)))
                    i = j + 1
                else:
                    segments.append(('lit', c))
                    i += 1
            elif c == '&':
                segments.append(('field', ('str', None)))
                i += 1
            elif c == '_':
                i += 1
                if i < n:
                    segments.append(('lit', fmt[i]))
                    i += 1
            else:
                if fmt.startswith('**$', i):
                    k = i + 3
                elif fmt[i:i + 2] in ('**', '$$'):
                    k = i + 2
                else:
                    k = i
                j = k
                while j < n and fmt[j] in '#.,+-^':
                    j += 1
                run = fmt[i:j]
                is_field_start = (c in '#.,+-^') \
                    or (fmt[i:i + 2] in ('**', '$$')) \
                    or fmt.startswith('**$', i)
                if is_field_start and ('#' in run or '.' in run):
                    segments.append(('field', ('num', run)))
                    i = j
                else:
                    segments.append(('lit', c))
                    i += 1
        # Merge consecutive literals
        merged = []
        for seg in segments:
            if seg[0] == 'lit' and merged and merged[-1][0] == 'lit':
                merged[-1] = ('lit', merged[-1][1] + seg[1])
            else:
                merged.append(seg)
        return merged

    def _format_using_field(self, spec, arg):
        """Format one argument with one field spec."""
        if spec[0] == 'str':
            width = spec[1]
            s = self._using_str_arg(arg)
            if width is None:
                return s
            if width == 1:
                return s[:1] if s else ' '
            return s[:width].ljust(width)
        return self._format_using_number(spec[1], self._using_num_arg(arg))

    def _using_str_arg(self, arg):
        """An argument rendered as a string (for string fields)."""
        if arg is None:
            return ''
        if isinstance(arg, str):
            return arg
        if isinstance(arg, float) and arg == int(arg):
            return str(int(arg))
        return str(arg)

    def _using_num_arg(self, arg):
        """An argument as a number (for numeric fields)."""
        if arg is None:
            return 0.0
        if isinstance(arg, (int, float)):
            return float(arg)
        try:
            return float(arg)
        except (TypeError, ValueError):
            raise BasicError("Type mismatch")

    def _using_commas(self, ip, comma_thousands):
        """Insert a thousands separator every three integer digits."""
        if not comma_thousands:
            return ip
        groups = []
        while len(ip) > 3:
            groups.insert(0, ip[-3:])
            ip = ip[:-3]
        groups.insert(0, ip)
        return ','.join(groups)

    def _format_using_number(self, field, v):
        # --- Prefix: ** (asterisk fill), $$ (dollar), **$ (both) ---
        asterisk_fill = False
        dollar = False
        extra_int = 0
        rest = field
        if rest.startswith('**$'):
            asterisk_fill = True
            dollar = True
            extra_int = 2
            rest = rest[3:]
        elif rest.startswith('**'):
            asterisk_fill = True
            extra_int = 2
            rest = rest[2:]
        elif rest.startswith('$$'):
            dollar = True
            # The dollar sign is printed directly left of the formatted
            # number (like + / -) and does not add a digit position, so a
            # full-width number such as 150.9 in "$$###.##" prints "$150.90"
            # with no leading space.
            extra_int = 0
            rest = rest[2:]

        # --- Sign specifiers ---
        leading_sign = rest.startswith('+')
        trailing_sign = rest.endswith('+')
        trailing_minus = rest.endswith('-')
        if leading_sign:
            rest = rest[1:]
        if trailing_sign:
            rest = rest[:-1]
        if trailing_minus:
            rest = rest[:-1]

        # --- Exponential? ---
        exponential = '^^^^' in rest
        if exponential:
            rest = rest.replace('^^^^', '')

        # --- Integer / fractional parts ---
        if '.' in rest:
            int_part, frac_part = rest.split('.', 1)
        else:
            int_part, frac_part = rest, ''
        comma_thousands = ',' in int_part
        int_positions = len(int_part.replace(',', '')) + extra_int
        frac_positions = len(frac_part)

        # --- 24-digit limit (manual PRINT USING) ---
        if int_positions + frac_positions > 24:
            raise BasicError("Illegal function call")

        neg = v < 0
        av = abs(v)

        if exponential:
            return self._format_using_exp(int_positions, frac_positions,
                                          leading_sign, trailing_sign,
                                          trailing_minus, asterisk_fill,
                                          dollar, v)

        # --- Round ---
        if frac_positions > 0:
            rounded = round(av, frac_positions)
        else:
            rounded = float(round(av))
        if frac_positions > 0:
            s = '%.*f' % (frac_positions, rounded)
        else:
            s = '%d' % int(rounded)
        ip, fp = (s.split('.') if '.' in s else (s, ''))

        # --- Implicit sign (occupies a digit position) ---
        sign_char = ''
        if neg and not (leading_sign or trailing_sign or trailing_minus):
            sign_char = '-'
        avail = int_positions - (1 if sign_char else 0)
        overflow = len(ip) > avail

        if overflow:
            # % in front of the full number (manual PRINT USING)
            num = self._using_commas(ip, comma_thousands)
            if frac_positions > 0:
                num += '.' + fp
            if sign_char:
                num = sign_char + num
            if leading_sign:
                num = ('-' if neg else '+') + num
            if trailing_sign:
                num += ('-' if neg else '+')
            if trailing_minus:
                num += ('-' if neg else ' ')
            if dollar:
                num = '$' + num
            return '%' + num

        # --- Thousands separator, implicit sign, padding ---
        ip = sign_char + self._using_commas(ip, comma_thousands)
        total_width = int_positions + ip.count(',')
        pad_char = '*' if asterisk_fill else ' '
        if len(ip) < total_width:
            ip = ip.rjust(total_width, pad_char)

        # --- Assemble ---
        if frac_positions > 0:
            result = ip + '.' + fp
        else:
            result = ip

        # --- Explicit sign specifiers ---
        if leading_sign:
            result = ('-' if neg else '+') + result
        if trailing_sign:
            result += ('-' if neg else '+')
        if trailing_minus:
            result += ('-' if neg else ' ')

        # --- Dollar: immediately left of the first non-pad character ---
        if dollar:
            pos = None
            for k, ch in enumerate(result):
                if ch not in (' ', '*'):
                    pos = k
                    break
            if pos is None:
                pos = len(result)
            result = result[:pos] + '$' + result[pos:]

        return result

    def _format_using_exp(self, int_positions, frac_positions, leading_sign,
                          trailing_sign, trailing_minus, asterisk_fill,
                          dollar, v):
        """Exponential (^^^^) numeric field formatting."""
        neg = v < 0
        av = abs(v)
        if leading_sign or trailing_sign or trailing_minus:
            digits_before = int_positions
        else:
            digits_before = int_positions - 1
        digits_before = max(0, digits_before)
        if av == 0:
            e = 0
            m = 0.0
        else:
            e = math.floor(math.log10(av)) - (digits_before - 1)
            m = round(av / (10 ** e), frac_positions)
            if m >= 10 ** digits_before:
                m /= 10
                e += 1
        if digits_before > 0:
            mantissa = '%.*f' % (frac_positions, m)
            ip, fp = mantissa.split('.')
            mantissa = ip.rjust(digits_before, '0') + '.' + fp
        else:
            mantissa = '.' + ('%.*f' % (frac_positions, m)).split('.')[1]
        exp_str = ('E+%02d' if e >= 0 else 'E-%02d') % abs(e)
        if leading_sign:
            sign = '-' if neg else '+'
        elif trailing_minus or trailing_sign:
            sign = ''
        else:
            sign = '-' if neg else ' '
        result = sign + mantissa + exp_str
        if trailing_sign:
            result += '-' if neg else '+'
        if trailing_minus:
            result += '-' if neg else ' '
        if dollar:
            result = '$' + result
        return result

    # -- main loop ----------------------------------------------------------- #
    def run(self, start_line=None):
        if start_line is None:
            start_line = self.lines[0] if self.lines else None
        if start_line is None:
            return
        self.pc = start_line
        self.pc_stmt = 0
        self.gosub_stack = []
        self._resume_actions = None
        self.for_stack = []
        self.while_stack = []
        self.skip_else_stack = []
        self._stopped = False
        # A fresh RUN starts with no sound: a STOP leaves the previous run's
        # music / SOUND tone running (a stopped program's world is frozen,
        # not torn down - see BasicREPL.run's finally), and it must not
        # leak into the new run.  CONT deliberately does NOT stop it: it
        # resumes the stopped run mid-play.
        self.system.stop_speaker()
        self.system.music_stop()
        self._running = True
        try:
            _wayne_run(self)
        finally:
            self._running = False

    def cont(self):
        """CONT (manual CONT): resume execution from the current pc after a
        STOP, break, or trace stop.  The interpreter state (variables and
        stacks) is kept.  No-op if there is nothing to continue."""
        if not self._stopped or self.pc is None:
            return
        self._stopped = False
        # First line after a CONT displays at once instead of waiting
        # for the remainder of the interval used before the stop.
        self._trace_last = None
        self._running = True
        try:
            _wayne_run(self)
        finally:
            self._running = False

    def _run_loop(self):
        while self.pc is not None:
            # Drain the window's Tk queue (throttled to ~50 Hz, see
            # Screen.pump_if_due) BEFORE the stop check below: a line that
            # draws nothing never pumps the window on its own, so without
            # this the window's ESC / close-box events would never be
            # processed in a tight non-drawing loop and the stop flag would
            # never be set (the window would appear uncloseable).
            self.screen.pump_if_due()
            # A stop requested while the tkinter window was focused is captured
            # by the window's ESC/close-box handler (see Screen._on_escape),
            # which sets a flag because the console is not focused in that case.
            # Raise KeyboardInterrupt here so it is handled exactly like a
            # console Ctrl+C: run()/cont() close the window and return to the
            # Ok prompt.  Checked every line so even a tight loop with no SLEEP
            # stops promptly.
            if self.screen._stop_requested:
                self.screen._stop_requested = False
                raise KeyboardInterrupt
            if self.screen._interrupt:
                # Ctrl+C landed inside a tkinter callback (see
                # Screen._on_configure): deliver it at this clean boundary,
                # exactly like a console Ctrl+C would be.
                self.screen._interrupt = False
                raise KeyboardInterrupt
            # TRACE ON [lines per second]: display the line about to be
            # executed, then pace the program to the configured rate
            # (default 3, range 1-100).  While tracing, execution is
            # held between lines until the interval has elapsed, so the
            # program runs at no more than the specified lines per
            # second (it runs at full speed when tracing is off).  Loop
            # bodies re-enter this loop once per iteration (FOR/NEXT,
            # WHILE/WEND and DO/LOOP branch back via Goto), so every
            # executed line is paced and displayed.
            if self.trace and self.trace_rate is not None:
                if self._trace_last is not None:
                    delay = self._trace_last + self.trace_rate - time.time()
                    if delay > 0:
                        time.sleep(delay)
                self._trace_last = time.time()
                if self.trace_pause:
                    self._trace_pause_count -= 1
                text = self.source.get(self.pc)
                if text is not None:
                    self.io.write_console("Trace: %6d %s" % (self.pc, text), newline=True)
                else:
                    self.io.write_console("Trace: line %d" % self.pc, newline=True)
            self._step_line()
            # TRACE ON <rate> PAUSE: after every <rate> traced lines (i.e. one
            # second of tracing), wait for a key press and then continue
            # (a classic PAUSE), rather than breaking out to the Ok prompt.
            # When the traced line ends the program (pc is None) there is
            # nothing to wait for.
            if (self.trace_pause and self.pc is not None
                    and self._trace_pause_count <= 0):
                self._trace_pause_count = self.trace_lps or 1
                self._pause_wait()
            # Batch-render any graphics changes made by this line.  Allow a
            # paint for this line: render() updates the canvas item cheaply,
            # but the actual window paint (cv.update) is deferred until the
            # end of the loop iteration (the GOTO back-edge), so a frame
            # composed of many lines forces the window to paint once per frame
            # rather than once per line (see render / _paint_due).
            self.screen._paint_due = True
            self.screen.flush()

    def do_pause(self):
        # PAUSE (extension): stop until the user presses SPACE or ENTER,
        # then continue; other keys are ignored.  Keys come through the
        # I/O middle layer (the window's keyboard while it is open -
        # polling the console too - else the console).  Ctrl+C ends
        # execution as anywhere (read_key returns 'ctrl_c' on some consoles
        # and raises on others; ESC / the close box raise while the window
        # is focused).  On a non-tty console (piped input, the test
        # harness) a LINE is read instead so the wait never hangs: any
        # line, including an empty one (ENTER), resumes; on EOF the program
        # simply continues.
        try:
            if sys.stdin.isatty():
                while True:
                    key = self.io.read_key()
                    if key is None:
                        continue
                    if key == 'ctrl_c':
                        raise KeyboardInterrupt()
                    if key in ('enter', ' '):
                        break
            else:
                self.io.read_line()
        except EOFError:
            # No more input; just continue (the program will finish
            # normally).
            pass

    def _pause_wait(self):
        """TRACE ON <rate> PAUSE: pause after a traced line and resume only
        when the user presses ENTER or the SPACE BAR (no message is printed).
        Any other key is ignored and the wait continues.  Ctrl+C ends
        execution (its KeyboardInterrupt propagates up and stops the program).
        On an interactive console a single key is read at a time; when stdin
        is not a tty (e.g. redirected input or the test harness) a line is read
        instead so the wait does not hang, and any non-empty line (or an empty
        line, i.e. ENTER) resumes.  On EOF the program simply continues."""
        try:
            if sys.stdin.isatty():
                while True:
                    # Keys come through the I/O middle layer: the window's
                    # keyboard while it is open, the console otherwise.
                    key = self.io.read_key()
                    if key is None:
                        continue
                    # 'ctrl_c' is returned (not raised) on some consoles; treat
                    # it as Ctrl+C so execution ends as requested.
                    if key == 'ctrl_c':
                        raise KeyboardInterrupt()
                    if key in ('enter', ' '):
                        break
            else:
                self.io.read_line()
        except EOFError:
            # No more input; just continue (the program will finish normally).
            pass

    def _step_line(self):
        try:
            # A RETURN from a GOSUB whose statement sat inside a single-line
            # IF's THEN/ELSE actions first resumes that action list (set by
            # the Return handler from the GOSUB stack entry), then continues
            # with the statements after the IF on the same line.
            if self._resume_actions is not None:
                steps, if_line, line_c, stmt_c = self._resume_actions
                # pc stays at the IF line while the steps run (ERL and
                # break messages); restore the resume line afterwards.
                self.pc = if_line
                self._exec_action_steps(steps, if_line, line_c, stmt_c)
                self.pc = line_c
                self.pc_stmt = stmt_c
                self._resume_actions = None
            line = self.program.get(self.pc)
            if line is None:
                raise BasicError("Undefined line number")
            self.execute_line(line, start_idx=self.pc_stmt)
            # The resumed line (a RESUME/RESUME 0 re-run) has executed without
            # error, so its one-shot re-run guard is now consumed: a later,
            # genuinely new error must trap normally again.
            self._resume_suppress = False
            self.pc = self.next_line_map.get(self.pc)
            self.pc_stmt = 0
        except Goto as g:
            # A Goto leaves the error handler only when it is raised by a
            # RESUME: do_resume / do_resume_next clear error_line before
            # raising, so error_line is None exactly when the RESUME has
            # already ended the trap.  A GOTO/GOSUB/RETURN that fires while
            # the handler is still active (error_line set) must NOT disarm
            # it - otherwise the handler's own control flow (e.g. a GOTO
            # back into the program) would be mistaken for a fresh error
            # and re-enter the trap, halting the interpreter.
            if self.error_line is None:
                self._in_error_handler = False
            # A non-RESUME jump discards any pending re-run guard (e.g. the
            # resumed line itself executed a GOTO); the RESUME's own jump
            # keeps the guard alive for the target line it is about to run.
            if not g.resuming_from_handler:
                self._resume_suppress = False
            # A jump abandons any IF-action continuation a RETURN left
            # pending.
            self._resume_actions = None
            if g.line not in self.program:
                # Fail here, while pc is still the GOTO line (so ERL is
                # that line, not the undefined target), via the normal
                # trap path.
                self._trap_or_raise(BasicError("Undefined line number"))
            else:
                self._filter_skip_else(g.line)
                self.pc = g.line
                self.pc_stmt = g.stmt_idx
        except Gosub as g:
            if self.error_line is None:
                self._in_error_handler = False
            if g.line not in self.program:
                # A GOSUB to an undefined line reports ERR=8 without
                # pushing a return address: the subroutine was never
                # entered, so a later RETURN must not jump back to the
                # GOSUB line (that would re-run the code after it).
                self._trap_or_raise(BasicError("Undefined line number"))
            else:
                cont = None
                if_line = None
                if g.resume is not None:
                    # The GOSUB sat inside a single-line IF's THEN/ELSE
                    # actions: the RETURN resumes that action list at the
                    # recorded point, then continues with the statements
                    # after the IF.  While a continuation is already running
                    # (a GOSUB in the resumed slice), the IF's line and
                    # following statement come from it - cur_stmt_idx may
                    # still belong to a line the subroutine ran through;
                    # otherwise they are taken from the IF statement just
                    # executed.
                    cont = g.resume
                    if self._resume_actions is not None:
                        (if_line, line, stmt_idx) = \
                            (self._resume_actions[1], self._resume_actions[2],
                             self._resume_actions[3])
                        self._resume_actions = None
                    elif self.cur_stmt_idx + 1 < len(self.cur_line):
                        if_line = self.pc
                        line, stmt_idx = self.pc, self.cur_stmt_idx + 1
                    else:
                        if_line = self.pc
                        line, stmt_idx = self.next_line_map.get(self.pc), 0
                elif g.trap_key is not None:
                    # A GOSUB entered by an ON KEY(n) trap interrupted the
                    # statement about to run (cur_stmt_idx), so it resumes
                    # there.
                    line, stmt_idx = self.pc, self.cur_stmt_idx
                elif self.cur_stmt_idx + 1 < len(self.cur_line):
                    # A plain GOSUB resumes at the statement following it
                    # (manual RETURN): the next statement on the GOSUB's
                    # own line, or the next line if it was that line's
                    # last statement.
                    line, stmt_idx = self.pc, self.cur_stmt_idx + 1
                else:
                    line, stmt_idx = self.next_line_map.get(self.pc), 0
                self.gosub_stack.append(GosubEntry(line, stmt_idx, g.trap_key,
                                                   cont, if_line))
                self.pc = g.line
                self.pc_stmt = 0
        except Return as r:
            if self.error_line is None:
                self._in_error_handler = False
            if r.line is not None:
                # Non-local RETURN (manual RETURN): jump to the specified
                # line while eliminating any GOSUB entry an event trap
                # created, and re-arm the trap's event (plus any active
                # GOTO trap) as if the trap had returned normally.
                if self.gosub_stack and self.gosub_stack[-1].trap_key is not None:
                    self._rearm_key(self.gosub_stack.pop().trap_key)
                for n, t in list(self.key_traps.items()):
                    if t.get('in_trap'):
                        t['in_trap'] = False
                        self._rearm_key(n)
                self._resume_actions = None
                self._filter_skip_else(r.line)
                self.pc = r.line
                self.pc_stmt = 0
            elif not self.gosub_stack:
                # Raised from inside the except-handler (not the try block
                # above), so route it through the same trap logic as any
                # other runtime error; otherwise an untrapped "RETURN
                # without GOSUB" could never be trapped (manual Appendix A).
                self._resume_actions = None
                self._trap_or_raise(BasicError("RETURN without GOSUB"))
            else:
                entry = self.gosub_stack.pop()
                if entry.trap_key is not None:
                    # The GOSUB was entered by an ON KEY(n) trap: re-arm
                    # the event (automatic ON, manual ON KEY) unless the
                    # trap routine explicitly turned it off.
                    self._rearm_key(entry.trap_key)
                # Abandon any continuation left pending by a jump out of
                # one; an entry whose RETURN lands mid-action-list (a GOSUB
                # inside IF actions) starts its own.
                self._resume_actions = None
                if entry.cont is not None:
                    self._resume_actions = (entry.cont, entry.if_line,
                                            entry.line, entry.stmt_idx)
                    # pc stays at the IF line while the steps run (ERL and
                    # break messages); the step machinery restores the
                    # resume line before the statements after the IF.
                    self.pc = entry.if_line
                    self.pc_stmt = entry.stmt_idx
                else:
                    self.pc = entry.line
                    self.pc_stmt = entry.stmt_idx
        except Break as b:
            self._stopped = True
            self.io.write("Break in line %d"
                          % (b.line if b.line is not None else self.pc),
                          newline=True)
            if self._resume_actions is not None:
                # A STOP/trace stop inside an IF action continuation the
                # step driver just rewound past the STOP: CONT re-runs the
                # remaining steps (pc at the IF line while they run), then
                # the statements after the IF on the same line.
                self.pc = self._resume_actions[2]
                self.pc_stmt = self._resume_actions[3]
            else:
                # Advance past the break so CONT resumes at the following
                # line (a trace stop already leaves pc at the next line).
                self.pc = self.next_line_map.get(self.pc)
                self.pc_stmt = 0
            raise
        except Stop:
            self._stopped = False
            self.pc = None
            self._resume_actions = None
        except BasicError as e:
            self._resume_actions = None
            self._trap_or_raise(e)

    def _trap_or_raise(self, e):
        """Trap a runtime error if a handler is active, else re-raise.

        Shared by the BasicError catch in _step_line and by errors raised
        from inside its except-handlers (e.g. RETURN without GOSUB), which
        would otherwise bypass the trap entirely.
        """
        # A RESUME/RESUME 0 re-run of the resumed line aborts instead of
        # re-trapping (see do_resume); consume the one-shot guard here.  Any
        # other error - including a fresh one on a later line - falls through
        # to the normal trap logic below.
        if self._resume_suppress:
            self._resume_suppress = False
            self._stopped = False
            raise e
        if self.error_handler is not None and not self._in_error_handler:
            # Manual ON COM/KEY: an error trap automatically disables all
            # event trapping.
            for t in self.key_traps.values():
                t['state'] = 'off'
                t['pending'] = False
            self.vars['ERR'] = self._error_number(e)
            self.vars['ERROR$'] = str(e)
            # ERL is the line that caused the error (65535 for
            # direct-mode errors).
            self.vars['ERL'] = self.pc if self.pc is not None else 65535
            self.error_line = self.pc
            self._trapped_error = str(e)
            self._in_error_handler = True
            self.pc = self.error_handler
            self._filter_skip_else(self.pc)
        else:
            self._stopped = False
            raise e

    def _error_number(self, e):
        """Map a BasicError message to a GW-BASIC error number.

        Numbers follow the manual's Appendix A table; messages that the
        manual leaves unlisted (31-49 range) keep their implementation
        numbers (37 Illegal dimension, 45 LOOP without DO).
        """
        if isinstance(e, BasicError) and e.code is not None:
            return e.code
        msg = str(e).lower()
        if 'file not found' in msg:
            return 53
        if 'input past end' in msg or 'eof' in msg:
            return 62
        if 'bad file number' in msg or 'file not open' in msg:
            return 52
        if 'file already open' in msg:
            return 55
        if 'file already exists' in msg:
            return 58
        if 'bad file mode' in msg or 'invalid file mode' in msg:
            return 54
        if 'bad record number' in msg:
            return 63
        if 'division by zero' in msg:
            return 11
        if 'subscript out of range' in msg:
            return 9
        if 'illegal dimension' in msg:
            return 37
        if 'illegal function call' in msg:
            return 5
        if 'out of data' in msg:
            return 4
        if 'undefined line number' in msg:
            return 8
        if 'duplicate definition' in msg:
            return 10
        if 'type mismatch' in msg:
            return 13
        if 'field overflow' in msg:
            return 50
        if 'overflow' in msg:
            return 6
        if 'unprintable error' in msg:
            return 21
        if 'undefined user function' in msg or 'undefined function' in msg:
            return 18
        if 'next without for' in msg:
            return 1
        if 'return without gosub' in msg:
            return 3
        if 'resume without error' in msg:
            return 20
        if 'for without next' in msg:
            return 26
        if 'while without wend' in msg:
            return 29
        if 'wend without while' in msg:
            return 30
        if 'syntax error' in msg:
            return 2
        if 'without' in msg:  # LOOP/DO and other unlisted "without" errors
            return 45
        return 0

    def run_immediate(self, stmts):
        """Execute statements in immediate (no line number) mode."""
        self._immediate_mode = True
        try:
            for stmt in stmts:
                if stmt[0] == 'def_fn':
                    # DEF FN is illegal in the direct (immediate) mode.
                    raise BasicError("Illegal function call")
                self.execute_statement(stmt)
        except (Goto, Gosub, Return):
            raise BasicError("GOTO/GOSUB/RETURN not allowed in immediate mode")
        except Stop:
            pass
        except BasicError as e:
            # Direct-mode error: record it in ERR/ERROR$/ERL (ERL is
            # 65535 in direct mode) and let the caller print the message.
            self.vars['ERR'] = self._error_number(e)
            self.vars['ERROR$'] = str(e)
            self.vars['ERL'] = 65535
            raise
        finally:
            self._immediate_mode = False


# --------------------------------------------------------------------------- #
#  REPL / environment
# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
#  Single-key input (for the LEDIT in-place line editor)
# --------------------------------------------------------------------------- #
def _enable_vt_processing():
    """Enable ANSI/VT escape-sequence processing on the console output.

    Windows 10+ understands VT sequences once the
    ENABLE_VIRTUAL_TERMINAL_PROCESSING flag is set on the stdout handle.
    This is a no-op on other platforms.
    """
    if os.name != 'nt':
        return
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.GetStdHandle(-11)  # STD_OUTPUT_HANDLE
        mode = ctypes.c_uint32()
        if kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            kernel32.SetConsoleMode(handle, mode.value | 0x0004)
            return
    except Exception:
        pass
    try:
        # Fallback: on Windows 10+ an empty os.system() call enables VT.
        os.system('')
    except Exception:
        pass


# Windows extended-key scan codes (arrow / editing keys) as returned by
# msvcrt after the 0x00/0xE0 prefix byte.
_WIN_EXT_KEYS = {
    'H': 'up', 'P': 'down', 'K': 'left', 'M': 'right',
    'G': 'home', 'O': 'end', 'S': 'delete',
    'I': 'pageup', 'J': 'pagedown',
}


def _read_key_win():
    """Read one key press from the Windows console (msvcrt).

    getwch reads through ReadConsole internally, so it discards
    non-key events (FOCUS / MOUSE) and blocks until a key arrives.  In
    the prompt's raw console mode a Ctrl+C arrives as a plain 0x03
    character (no CTRL_C_EVENT is generated), which the Ok-prompt
    editor turns into its cancel.  The caller (_console_key_pending)
    gates this read so it only blocks while the prompt loop is
    idle-pumping the graphics window."""
    import msvcrt
    ch = msvcrt.getwch()
    if ch in ('\x00', '\xe0'):
        try:
            code = msvcrt.getwch()
        except Exception:
            return None
        return _WIN_EXT_KEYS.get(code)
    if ch in ('\r', '\n'):
        return 'enter'
    if ch == '\x08':
        return 'backspace'
    if ch == '\x1b':
        return 'escape'
    if ch == '\x03':
        return 'ctrl_c'
    if ch == '\x1a':
        return 'eof'
    if ch == '\t':
        return 'tab'
    if ch.isprintable():
        return ch
    return None


def _decode_key_byte(b, fd):
    """Decode one raw console byte into a normalized key token.

    ``b`` is the first byte of the key; multi-byte sequences (arrows,
    DELETE) are completed by reading follow-up bytes from ``fd``.  Shared
    by _read_key_unix and the Ok-prompt line reader (which may read bytes
    outside cbreak mode).  Returns None for unrecognized keys.
    """
    import select
    if b == 0x1b:  # Escape, or the start of an arrow/edit sequence
        ready, _, _ = select.select([fd], [], [], 0.05)
        if ready:
            c1 = os.read(fd, 1)
            if c1 and c1[0] == 0x5b:  # '['
                c2 = os.read(fd, 1)
                if c2:
                    arrow = {0x41: 'up', 0x42: 'down',
                             0x43: 'right', 0x44: 'left'}
                    if c2[0] in arrow:
                        return arrow[c2[0]]
                    if c2[0] == 0x33:  # '3' -> DELETE (ESC [ 3 ~)
                        os.read(fd, 1)  # consume the trailing '~'
                        return 'delete'
        return 'escape'
    if b in (0x0d, 0x0a):
        return 'enter'
    if b in (0x7f, 0x08):  # DEL / BS
        return 'backspace'
    if b == 0x03:
        return 'ctrl_c'
    if b == 0x09:
        return 'tab'
    if 0x20 <= b < 0x7f:
        return chr(b)
    return None


def _read_key_unix():
    """Read one key press using termios cbreak mode (Unix)."""
    import termios
    import tty
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    try:
        tty.setcbreak(fd)
        ch = os.read(fd, 1)
        if not ch:
            return None
        return _decode_key_byte(ch[0], fd)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)


def _read_key():
    """Read one key press and return a normalized token.

    Tokens: 'left','right','up','down','home','end','pageup','pagedown',
    'delete','backspace','enter','escape','ctrl_c','eof','tab', or a
    printable character.  Returns None for unrecognized keys.
    """
    if os.name == 'nt':
        return _read_key_win()
    return _read_key_unix()


class IoDevice:
    """The single middle layer between the interpreter and I/O.

    While the graphics window is open, the window IS the CGA/EGA monitor:
    every byte printed goes to the window (composited into the pixel buffer
    or the text grid, depending on the screen mode) and every key read comes
    from the window's keyboard.  The instant the window closes, I/O returns
    to the console.  The rest of the code never touches stdout/stdin (or
    tkinter) directly - it calls write(), read_key() and read_line(), which
    route each byte to the right place.  The BASIC program cannot tell the
    difference from the old monitor: it simply uses it.
    """

    def __init__(self, screen, console_write, console_read_line,
                 console_read_key):
        self.screen = screen
        self._console_write = console_write
        self._console_read_line = console_read_line
        self._console_read_key = console_read_key

    # -- status --------------------------------------------------------------
    def window_live(self):
        """True while the graphics window exists (and has not been
        destroyed): that is when the monitor is the window, not the
        console."""
        return (self.screen._root is not None
                and not self.screen.virtual)

    def _stopped(self):
        """True while a program is halted at a STOP awaiting CONT (or a new
        RUN): then the developer's console is the monitor for the
        interactive session - every print and every key read goes to it
        even while the graphics window is still open, frozen on its last
        frame.  The interpreter's _stopped flag is set by the run loop's
        Break handler (before the "Break in line N" message is printed) and
        cleared by CONT / RUN before the first line runs, so the window
        takes the monitor back the moment the program resumes.  With no
        window open it is irrelevant: the console is the monitor anyway."""
        interp = self.screen._interp
        if interp is None:
            return False
        return bool(getattr(interp, '_stopped', False))

    # -- output --------------------------------------------------------------
    def write(self, text, newline=True):
        # Stopped at a STOP: the console is the monitor (see _stopped),
        # even while the window is still open.
        if self.window_live() and not self._stopped():
            self.screen.print_text(text, newline)
        else:
            self._console_write(text + ('\n' if newline else ''))

    def write_console(self, text, newline=True):
        """Force output to the console even while the graphics window is
        open (TRACE lines must not be composited into the window).  Flushes
        after each write so TRACE ON <rate> pacing is visible line-by-line;
        the console stream is otherwise block-buffered and would dump all
        the traced lines at once (the window path never had this, since Tk
        renders each line immediately)."""
        self._console_write(text + ('\n' if newline else ''))
        try:
            sys.stdout.flush()
        except Exception:
            pass

    # -- input ---------------------------------------------------------------
    def pop_window_key(self):
        """Pop one normalized key from the window's queue, or None.

        The window's <Key> adapter feeds the system key queue (the same one
        INKEY$/GET consume), shaped exactly like console keys (see
        Screen._on_window_key).  It is translated to the same normalized
        tokens the console readers return (see _read_key)."""
        if not self.window_live():
            return None
        interp = self.screen._interp
        if interp is None:
            return None
        system = interp.system
        if not system.key_events:
            return None
        ev = system.key_events.pop(0)
        ch = ev.get('ch')
        if ch:
            b = ord(ch[0])
            if b in (13, 10):
                return 'enter'
            if b == 8:
                return 'backspace'
            if b == 3:
                return 'ctrl_c'
            if b == 26:
                return 'eof'
            if b < 32:
                return None  # other control characters: not text
            return ch
        token = ev.get('token')
        if token:
            return token  # 'enter', 'up', 'down', 'left', 'right', ...
        return None  # bare scan-code extended key: not a text token

    def _next_window_key(self):
        """Pump the window and pop one key from its queue, or None."""
        key = self.pop_window_key()
        if key is not None:
            return key
        try:
            self.screen.pump()
        except Exception:
            pass
        return self.pop_window_key()

    def _console_has_key(self):
        # Strict gate exactly where a blocking console read could freeze
        # the open window (see _console_key_pending); with no window the
        # original fail-open peek path applies.
        try:
            return _console_key_pending(strict=self.window_live())
        except Exception:
            return False

    def read_key(self):
        """One normalized key press: from the window while it is open, from
        the console once it is closed.  While the window is open the read
        polls both keyboards (whichever the user is typing on wins) instead
        of blocking on the console, so a key typed into the window is never
        missed.  Stopped at a STOP (_stopped): always the console, even
        with the window open (the debugging session runs on the console).
        """
        if self.window_live() and not self._stopped():
            while True:
                key = self._next_window_key()
                if key is None and self._console_has_key():
                    key = self._console_read_key()
                if key is not None:
                    return key
                if self.screen._stop_requested:
                    # ESC / close box while blocked waiting for a key: stop
                    # the program exactly like a console Ctrl+C would (see
                    # Screen._on_escape); the run loop turns the flag into
                    # the same KeyboardInterrupt.
                    self.screen._stop_requested = False
                    raise KeyboardInterrupt
                time.sleep(0.02)
        return self._console_read_key()

    def read_line(self):
        """One line of text: from the window while it is open, from the
        console once it is closed (see read_key for the polling).  A
        BACKSPACE deletes the last character; navigation / function keys are
        ignored (they are not part of a text line).

        While the window is open it IS the old monitor, so the line is echoed
        exactly like a terminal: each typed character is drawn, BACKSPACE
        erases the last one, and ENTER moves the cursor to a fresh line.  On
        the console the OS already echoes, so nothing is drawn there.
        Stopped at a STOP (_stopped): the console line reader is used even
        while the window is open."""
        if self.window_live() and not self._stopped():
            buf = []
            while True:
                key = self._next_window_key()
                if key is None and self._console_has_key():
                    key = self._console_read_key()
                if key is None:
                    if self.screen._stop_requested:
                        # ESC / close box while blocked waiting for input:
                        # stop the program exactly like a console Ctrl+C
                        # would (see Screen._on_escape).
                        self.screen._stop_requested = False
                        raise KeyboardInterrupt
                    time.sleep(0.02)
                    continue
                if key == 'enter':
                    # New line, like the console does on Enter.
                    self.write('\n', newline=False)
                    return ''.join(buf)
                if key == 'ctrl_c':
                    raise KeyboardInterrupt
                if key == 'eof':
                    raise EOFError
                if key == 'backspace':
                    if buf:
                        buf.pop()
                        # Neither text nor graphics mode honours \x08 as a
                        # cursor move (it would draw a glyph), so the echoed
                        # char is simply overwritten in place: step the text
                        # cursor one column left and redraw a space.  (This
                        # is a cosmetic detail; the buffer is what counts.)
                        self._erase_last_echoed_char()
                    continue
                if len(key) == 1:
                    buf.append(key)
                    self.write(key, newline=False)
                    continue
        return self._console_read_line()

    def _erase_last_echoed_char(self):
        """Overwrite the last echoed character with a space (BACKSPACE echo).

        The text cursor has just advanced past the character, so stepping it
        one column left and drawing a blank cell erases it.  Works in both
        text and graphics (text-page) modes; clamps at the page's left edge.
        """
        try:
            scr = self.screen
            if scr.is_text():
                cols = scr.cols
            else:
                cols, _rows = scr._gfx_text_page()
            if scr.cursor_col > 0:
                scr.cursor_col -= 1
            self.write(' ', newline=False)
        except Exception:
            pass


# #############################################################################
#  Wayne: compiled execution engine (BASIC -> Python)
#
#  Everything below is an add-on: the built-in interpreter above stays
#  intact and is still used for immediate mode (statements typed at the Ok
#  prompt) and as an invisible per-statement fallback (cone()) for anything
#  the compiler does not generate natively.
#
#  On RUN (and CONT) the in-memory BASIC program is compiled once into
#  native Python: one function per line, plain Python expressions (with
#  GW-BASIC's single-precision rounding and overflow rules exactly as the
#  interpreter applies them), and direct pc assignment for control flow
#  (no per-iteration exception raising).  The generated module runs in a
#  dispatcher loop (_wayne_run_loop) that mirrors the interpreter's
#  per-line duties (window pump, stop/trace handling, error trapping) and
#  shares all runtime state (vars, arrays, stacks) with the interpreter,
#  so STOP/CONT and immediate mode see exactly the same program state.
#  Every RUN recompiles from the current in-memory program; the user never
#  sees or edits the generated Python.
#
#  Debug switches (environment variables, invisible in normal use):
#    WAYNE_FORCE_INTERP=1  never compile (interpreter baseline for A/B)
#    WAYNE_DUMP=<path>     write the generated Python to <path>
#    WAYNE_REPORT=1        print which statements used the interpreter
#                          fallback (cone) after each RUN
# #############################################################################

class CompileSkip(Exception):
    """Raised when a program cannot be compiled; the built-in interpreter
    loop runs it instead (invisible to the user)."""
    pass


# --------------------------------------------------------------------------- #
#  Runtime helpers for the generated code (first argument: the interpreter)
# --------------------------------------------------------------------------- #
def _w_ct(g):
    """Statement-start key-trap check (ON COM/KEY); raises on a trapped key."""
    g._check_key_traps()


def _w_cv(g, name):
    """Read a scalar variable: (value, kind) (manual 6.1.1/6.2.2)."""
    v = g.get_var(name)
    return (v, g._value_kind(v, g.var_type(name)))


def _w_cvt(g, name):
    """Fast read of an UNSUFFIXED scalar (name already upper-case): one
    vars lookup and one exact-name DEFxxx lookup, with the same value
    and kind rules as get_var() + _value_kind() (default value is "" only
    when the name is DEFSTR'd; kind from value + declared type)."""
    t = g.def_types.get(name)
    v = g.vars.get(name, "" if t == 'string' else 0)
    if isinstance(v, str):
        return (v, 'string')
    if t == 'integer':
        return (v, 'int')
    if t == 'double':
        return (v, 'double')
    return (v, 'single')


def _w_cvs(g, name, dflt, kind):
    """Fast read of a SUFFIXED scalar (name already upper-case): the type
    suffix fixes the type, hence the kind and the undefined default; the
    read is a single dict lookup."""
    return (g.vars.get(name, dflt), kind)


def _w_noa(g, name):
    """Call a no-argument function (RND, INKEY$, TIMER, SCREEN, ...)."""
    return g.call_noarg_k(name)


def _w_ar(g, name, idx):
    """Read an array element (bounds-checked): (value, kind)."""
    v = g.get_arr(name, idx)
    return (v, g._value_kind(v, g.var_type(name)))


def _w_leaf(v, k=None):
    """Wrap a value (and optionally its kind) as an expression node the
    interpreter's own eval_with_kind() consumes unchanged ('num' v k,
    'num' v, or 'str' s).  A bare ('num', v) classifies as int/single
    from the value - safe for the int()/str() consumers (subscripts,
    file numbers, widths), which never look at the kind."""
    if isinstance(v, str):
        return ('str', v)
    if k is None:
        return ('num', v)
    return ('num', v, k)


def _w_clet(g, name, v):
    """X = value: type check + store (manual assignment rules)."""
    g._check_let_type(('var', name), v)
    g.assign(name, v)


def _w_clet_a(g, name, idx, v):
    """A(...) = value: type check + bounds check + store."""
    g._check_let_type(('arr', name, []), v)
    g._check_bounds(name, idx)
    if name not in g.arrays:
        g.arrays[name] = {}
    g.arrays[name][idx] = g.coerce(name, v)


def _w_om(g, r):
    """Arithmetic overflow: non-fatal warning + signed machine infinity
    (manual 6.4.1.2 - not trapped by ON ERROR GOTO)."""
    g._runtime_warning("Overflow")
    return g._machine_infinity(r)


def _w_ri(g, v):
    """Round a \\ / MOD operand to an integer (manual 6.4.1.1)."""
    # This interpreter widens \\/MOD to the 64-bit range; keep the
    # generated C check in step with Interpreter._round_int_operand.
    return g._round_int_operand(v)


def _w_n16(g, v):
    """Convert to a 16-bit two's-complement integer (manual 6.4.3)."""
    return g._to_int16(v)


def _w_cbk(g, name, args_k):
    """Call a built-in function with precision tracking (manual 6.3)."""
    return g.call_builtin_k(name, args_k)


def _w_uc(g, name, args_k):
    """Call a DEF FN user function, or fall back to an array reference
    (mirrors the tail of eval_with_kind's 'call' handling)."""
    upper = name.upper()
    if name in g.def_fns or upper in g.def_fns:
        return g.call_def_fn_k(name, args_k)
    if name not in g.arrays and name not in g.array_dims:
        raise BasicError("Undefined User Function")
    try:
        idx = tuple(int(a) for a, _k in args_k)
    except (TypeError, ValueError):
        raise BasicError("Undefined function")
    v = g.get_arr(name, idx)
    return (v, g._value_kind(v, g.var_type(name)))


def _w_vp(g, arg_nodes):
    """VARPTR: needs the argument NODE (identity), not the value."""
    return g._varptr(arg_nodes)


def _w_vps(g, arg_nodes):
    """VARPTR$: the three-byte string form of VARPTR."""
    return g._varptr_str(arg_nodes)


def _w_goto_fast(g, line, idx=0):
    """GOTO / loop back-edge without an exception: applies _step_line's
    Goto bookkeeping (error-handler, re-run guard, skip-else filter,
    undefined-target trap) and sets pc/pc_stmt directly.  Returns the
    target line, or None when the target was undefined and the error was
    routed through the normal trap path."""
    if g.error_line is None:
        g._in_error_handler = False
    g._resume_suppress = False
    g._resume_actions = None
    if line not in g.program:
        # Fail here, while pc is still the GOTO line (so ERL is that
        # line, not the undefined target), via the normal trap path.
        g._trap_or_raise(BasicError("Undefined line number"))
        return None
    g._filter_skip_else(line)
    g.pc = line
    g.pc_stmt = idx
    return line


def _w_nx(g, var):
    """NEXT: advance the matching FOR frame (counter read live from the
    variable, per _advance_for).  Returns the body-start (line, stmt_idx)
    to jump back to, or None when the loop has ended."""
    fs = g.for_stack
    if not fs:
        raise BasicError("NEXT without FOR")
    if var is None:
        idx = len(fs) - 1
    else:
        # frames store the counter name upper-cased (case-insensitive)
        idx = None
        var_up = var.upper()
        for i in range(len(fs) - 1, -1, -1):
            if fs[i][0] == var_up:
                idx = i
                break
        if idx is None:
            raise BasicError("NEXT without matching FOR")
    vn, _cur, end, step, bs = fs[idx]
    c = g.get_var(vn)
    if not isinstance(c, (int, float)):
        c = 0
    c = c + step
    g.assign(vn, c)
    # for_should_continue inlined (a pure sign check on step).
    if step > 0:
        keep = c <= end
    elif step < 0:
        keep = c >= end
    else:
        keep = True
    if keep:
        fs[idx] = (vn, c, end, step, bs)
        return bs
    del fs[idx]
    return None


def _w_nxm(g, vars_):
    """NEXT I,J: close the innermost matching loop, then the next outer
    matching loop (manual FORNEXT)."""
    fs = g.for_stack
    if not fs:
        raise BasicError("NEXT without FOR")
    vars_up = [v.upper() for v in vars_]
    while True:
        idx = None
        for i in range(len(fs) - 1, -1, -1):
            if fs[i][0] in vars_up:
                idx = i
                break
        if idx is None:
            return None
        vn, _cur, end, step, bs = fs[idx]
        c = g.get_var(vn)
        if not isinstance(c, (int, float)):
            c = 0
        c = c + step
        g.assign(vn, c)
        # for_should_continue inlined (a pure sign check on step).
        if step > 0:
            keep = c <= end
        elif step < 0:
            keep = c >= end
        else:
            keep = True
        if keep:
            fs[idx] = (vn, c, end, step, bs)
            return bs
        del fs[idx]


def _w_oi(g, v, lines):
    """ON expression GOTO/GOSUB: round + range-check (manual ON)."""
    return g._on_index(v, lines)


def _w_cone(g, stmt):
    """Invisible fallback: run one statement through the built-in
    interpreter (the same AST node, the same handler - correctness by
    construction)."""
    if getattr(g, '_wayne_report', False):
        g._wayne_falls.append((g.pc, stmt[0]))
    g.execute_statement(stmt)


# --------------------------------------------------------------------------- #
#  The compiler
# --------------------------------------------------------------------------- #
class WayneCompiler:
    """Compiles the interpreter's in-memory program (line -> list of
    statement-tuple AST - the same parsed nodes the interpreter executes,
    so syntax agreement is by construction) into a generated Python
    module: one function per line, plus static AST objects registered as
    D<i> globals and shared runtime helpers."""

    # Tags that may appear inside a single-line IF ... THEN/ELSE actions
    # list in compiled code.  Anything else (GOSUB, FOR/DO/WHILE, STOP in
    # an action, ...) makes the whole IF use the interpreter's action
    # machinery (cone), which owns same-line loops inside IF actions.
    SIMPLE = {
        'let', 'print', 'print_file', 'input', 'input_file', 'write',
        'read', 'restore', 'dim', 'redim', 'erase', 'swap', 'open',
        'close', 'get', 'put', 'seek', 'kill', 'line_input',
        'line_input_key', 'get_key', 'wait', 'error', 'on_error', 'trap',
        'resume', 'resume_next', 'end', 'stop', 'system', 'goto',
        'on_goto', 'on_gosub', 'if', 'cls', 'beep', 'sound', 'sleep',
        'setfps', 'locate', 'option', 'def_fn', 'def_type', 'type',
        'common', 'key', 'key_state', 'key_on', 'key_off', 'key_list',
        'environ', 'cursor', 'color', 'ink', 'screen', 'textsize',
        'textrotate', 'textfont', 'view', 'window', 'wclose', 'draw',
        'out', 'poke', 'on_key', 'pause', 'def_seg', 'bload', 'bsave',
        'mid_assign', 'lset', 'rset', 'field', 'field_old',
    }

    def __init__(self, g):
        self.g = g
        self.prog = g.program
        self.next_map = g.next_line_map
        self.data = []

    def d(self, obj):
        """Register a static object; returns the D<i> suffix for it."""
        self.data.append(obj)
        return len(self.data) - 1

    @staticmethod
    def _nv(t):
        t[0] += 1
        return 'v%d' % t[0]

    # -- expressions -------------------------------------------------------- #
    def ex(self, node, L, ind, t):
        """Emit code that evaluates an expression node, assigning
        (value, kind) to fresh names; returns the (v, k) names."""
        tag = node[0]
        if tag == 'num':
            v = self._nv(t)
            k = self._nv(t)
            val = node[1]
            if len(node) > 2:
                lit_kind = node[2]
                if (lit_kind == 'single' and isinstance(val, int)
                        and not (isinstance(val, bool))
                        and not (-8388607 <= val <= 8388607)):
                    # A single-precision integer constant beyond the range
                    # a single holds exactly: round it to its single value
                    # at the point it is materialized (the interpreter does
                    # this via the single-precision arithmetic/store the
                    # value flows through, e.g. PUT or X = lit).
                    L.append('%s%s = rs(%r)' % (ind, v, val))
                else:
                    L.append('%s%s = %r' % (ind, v, val))
                L.append('%s%s = %r' % (ind, k, lit_kind))
            else:
                # Two-tuple pseudo-numbers: classify from the value itself
                # (same rule as eval_with_kind).
                L.append('%s%s = %r' % (ind, v, val))
                L.append('%s%s = %r' % (ind, k,
                          'int' if isinstance(val, int) else 'single'))
            return v, k
        if tag == 'str':
            v = self._nv(t)
            k = self._nv(t)
            L.append('%s%s = %r' % (ind, v, node[1]))
            L.append('%s%s = "string"' % (ind, k))
            return v, k
        if tag == 'var':
            v = self._nv(t)
            k = self._nv(t)
            name = node[1]
            upper = name.upper()
            if upper in NOARG_FUNCTIONS:
                L.append('%s%s, %s = noa(g, %r)' % (ind, v, k, upper))
            elif upper[-1] not in '$%!#':
                # Unsuffixed: fast read (one vars + one def_types lookup).
                L.append('%s%s, %s = cvt(g, %r)' % (ind, v, k, upper))
            elif upper in ('TIME$', 'DATE$'):
                # Live clock/date strings must go through get_var.
                L.append('%s%s, %s = cv(g, %r)' % (ind, v, k, name))
            else:
                # The suffix fixes the type: constant default and kind.
                suf = upper[-1]
                if suf == '$':
                    d, knd = '', 'string'
                elif suf == '%':
                    d, knd = 0, 'int'
                elif suf == '!':
                    d, knd = 0, 'single'
                else:  # '#'
                    d, knd = 0, 'double'
                L.append('%s%s, %s = cvs(g, %r, %r, %r)' % (ind, v, k, upper, d, knd))
            return v, k
        if tag == 'arr':
            v = self._nv(t)
            k = self._nv(t)
            subs = []
            for sub in node[2]:
                sv, _sk = self.ex(sub, L, ind, t)
                subs.append('int(%s)' % sv)
            L.append('%s%s, %s = ar(g, %r, (%s,))'
                     % (ind, v, k, node[1], ', '.join(subs)))
            return v, k
        if tag == 'unop':
            op = node[1]
            cv, ck = self.ex(node[2], L, ind, t)
            v = self._nv(t)
            k = self._nv(t)
            if op == 'NOT':
                # NOT X = -(X+1), 16-bit (manual 6.4.3).
                L.append('%s%s = -n16(g, %s) - 1' % (ind, v, cv))
                L.append('%s%s = "int"' % (ind, k))
            else:
                # '-' / '+': same TypeError behavior on strings as the
                # interpreter's eval_with_kind.
                L.append('%s%s = %s%s' % (ind, v,
                          '-' if op == '-' else '', cv))
                L.append('%s%s = %s' % (ind, k, ck))
            return v, k
        if tag == 'binop':
            return self._ex_binop(node, L, ind, t)
        if tag == 'ifexp':
            # IF cond THEN a ELSE b: only the selected branch is evaluated.
            cv, _ck = self.ex(node[1], L, ind, t)
            v = self._nv(t)
            k = self._nv(t)
            L.append('%sif %s:' % (ind, cv))
            tv, tk = self.ex(node[2], L, ind + '    ', t)
            L.append('%s    %s, %s = %s, %s' % (ind, v, k, tv, tk))
            L.append('%selse:' % ind)
            ev, ek = self.ex(node[3], L, ind + '    ', t)
            L.append('%s    %s, %s = %s, %s' % (ind, v, k, ev, ek))
            return v, k
        if tag == 'call':
            name = node[1]
            upper = name.upper()
            v = self._nv(t)
            k = self._nv(t)
            if upper == 'VARPTR':
                L.append('%s%s = vp(g, D%d)' % (ind, v, self.d(node[2])))
                L.append('%s%s = "int"' % (ind, k))
                return v, k
            if upper == 'VARPTR$':
                L.append('%s%s = vps(g, D%d)' % (ind, v, self.d(node[2])))
                L.append('%s%s = "string"' % (ind, k))
                return v, k
            pairs = []
            for a in node[2]:
                av, ak = self.ex(a, L, ind, t)
                pairs.append('(%s, %s)' % (av, ak))
            args = '[%s]' % ', '.join(pairs)
            if upper in BUILTIN_FUNCTIONS:
                L.append('%s%s, %s = cbk(g, %r, %s)' % (ind, v, k, upper, args))
            else:
                L.append('%s%s, %s = uc(g, %r, %s)' % (ind, v, k, name, args))
            return v, k
        raise CompileSkip('unknown expression node %r' % (tag,))

    def _ex_binop(self, node, L, ind, t):
        op = node[1]
        av, ak = self.ex(node[2], L, ind, t)
        bv, bk = self.ex(node[3], L, ind, t)
        v = self._nv(t)
        k = self._nv(t)
        # Manual 6.3: a double operand wins; everything else is single.
        dbl = '(%s == "double" or %s == "double")' % (ak, bk)

        def chk(i):
            # _check_overflow (non-fatal warning + machine infinity),
            # then single-precision rounding (skipped for the integer
            # fast path - an int result is exact and representable),
            # then the result kind.
            L.append('%sif g._trap and (%s > MX or %s < _MX):' % (i, v, v))
            L.append('%s    %s = om(g, %s)' % (i, v, v))
            L.append('%sif not %s:' % (i, dbl))
            L.append('%s    if isinstance(%s, int) and -8388607 <= %s <= 8388607:'
                     % (i, v, v))
            L.append('%s        pass' % i)
            L.append('%s    else:' % i)
            L.append('%s        %s = rs(%s)' % (i, v, v))
            L.append('%s%s = "double" if %s else "single"' % (i, k, dbl))

        if op == '+':
            L.append('%sif isinstance(%s, str) or isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s    if isinstance(%s, str) and isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s        %s = %s + %s' % (ind, v, av, bv))
            L.append('%s        %s = "string"' % (ind, k))
            L.append('%s    else:' % ind)
            L.append('%s        raise BE("Type mismatch")' % ind)
            L.append('%selse:' % ind)
            L.append('%s    %s = %s + %s' % (ind, v, av, bv))
            chk(ind + '    ')
        elif op in ('-', '*'):
            L.append('%sif isinstance(%s, str) or isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s    raise BE("Type mismatch")' % ind)
            L.append('%selse:' % ind)
            sym = '-' if op == '-' else '*'
            L.append('%s    %s = %s %s %s' % (ind, v, av, sym, bv))
            chk(ind + '    ')
        elif op == '/':
            L.append('%sif isinstance(%s, str) or isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s    raise BE("Type mismatch")' % ind)
            L.append('%selse:' % ind)
            i2 = ind + '    '
            L.append('%sif %s == 0:' % (i2, bv))
            L.append('%s    g._runtime_warning("Division by zero")' % i2)
            L.append('%s    %s = g._machine_infinity(%s)' % (i2, v, av))
            L.append('%s    %s = "single"' % (i2, k))
            L.append('%selse:' % i2)
            L.append('%s    %s = %s / %s' % (i2, v, av, bv))
            chk(i2 + '    ')
        elif op == '^':
            L.append('%sif isinstance(%s, str) or isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s    raise BE("Type mismatch")' % ind)
            L.append('%selse:' % ind)
            i2 = ind + '    '
            L.append('%sif %s == 0 and %s < 0:' % (i2, av, bv))
            L.append('%s    g._runtime_warning("Division by zero")' % i2)
            L.append('%s    %s = g._machine_infinity(1)' % (i2, v))
            L.append('%s    %s = "single"' % (i2, k))
            L.append('%selif %s < 0 and %s != int(%s):' % (i2, av, bv, bv))
            L.append('%s    raise BE("Illegal function call")' % i2)
            L.append('%selse:' % i2)
            L.append('%s    try:' % i2)
            L.append('%s        %s = %s ** %s' % (i2, v, av, bv))
            L.append('%s    except OverflowError:' % i2)
            L.append('%s        g._runtime_warning("Overflow")' % i2)
            L.append('%s        %s = g._machine_infinity(%s)' % (i2, v, av))
            L.append('%s        %s = "single"' % (i2, k))
            L.append('%s    else:' % i2)
            chk(i2 + '        ')
        elif op == '\\':
            ai = self._nv(t)
            bi = self._nv(t)
            L.append('%s%s = ri(g, %s)' % (ind, ai, av))
            L.append('%s%s = ri(g, %s)' % (ind, bi, bv))
            L.append('%sif %s == 0:' % (ind, bi))
            L.append('%s    g._runtime_warning("Division by zero")' % ind)
            L.append('%s    %s = g._machine_infinity(%s)' % (ind, v, ai))
            L.append('%s    %s = "single"' % (ind, k))
            L.append('%selse:' % ind)
            L.append('%s    %s = int(%s / %s)' % (ind, v, ai, bi))
            L.append('%s    %s = "int"' % (ind, k))
        elif op == 'MOD':
            ai = self._nv(t)
            bi = self._nv(t)
            L.append('%s%s = ri(g, %s)' % (ind, ai, av))
            L.append('%s%s = ri(g, %s)' % (ind, bi, bv))
            L.append('%sif %s == 0:' % (ind, bi))
            L.append('%s    g._runtime_warning("Division by zero")' % ind)
            L.append('%s    %s = g._machine_infinity(%s)' % (ind, v, ai))
            L.append('%s    %s = "single"' % (ind, k))
            L.append('%selse:' % ind)
            L.append('%s    %s = %s - int(%s / %s) * %s'
                     % (ind, v, ai, ai, bi, bi))
            L.append('%s    %s = "int"' % (ind, k))
        elif op == '&':
            # String concatenation at each operand's own precision.
            L.append('%s%s = g.format_value_kind(%s, %s) + g.format_value_kind(%s, %s)'
                     % (ind, v, av, ak, bv, bk))
            L.append('%s%s = "string"' % (ind, k))
        elif op in ('=', '<>', '<', '>', '<=', '>='):
            as_ = self._nv(t)
            bs_ = self._nv(t)
            L.append('%s%s = isinstance(%s, str)' % (ind, as_, av))
            L.append('%s%s = isinstance(%s, str)' % (ind, bs_, bv))
            L.append('%sif %s != %s:' % (ind, as_, bs_))
            # A number always sorts before a string (manual 6.4.2).
            if op == '=':
                L.append('%s    %s = 0' % (ind, v))
            elif op == '<>':
                L.append('%s    %s = -1' % (ind, v))
            elif op in ('<', '<='):
                L.append('%s    %s = -1 if not %s else 0' % (ind, v, as_))
            else:
                L.append('%s    %s = -1 if %s else 0' % (ind, v, as_))
            L.append('%selse:' % ind)
            if op == '=':
                L.append('%s    %s = -1 if %s == %s else 0' % (ind, v, av, bv))
            elif op == '<>':
                L.append('%s    %s = -1 if %s != %s else 0' % (ind, v, av, bv))
            else:
                L.append('%s    %s = -1 if %s %s %s else 0'
                         % (ind, v, av, op, bv))
            L.append('%s%s = "int"' % (ind, k))
        elif op in ('AND', 'OR', 'XOR'):
            x = self._nv(t)
            y = self._nv(t)
            L.append('%s%s = n16(g, %s)' % (ind, x, av))
            L.append('%s%s = n16(g, %s)' % (ind, y, bv))
            sym = {'AND': '&', 'OR': '|', 'XOR': '^'}[op]
            L.append('%s%s = %s %s %s' % (ind, v, x, sym, y))
            L.append('%s%s &= 0xFFFF' % (ind, v))
            L.append('%sif %s >= 0x8000:' % (ind, v))
            L.append('%s    %s -= 0x10000' % (ind, v))
            L.append('%s%s = "int"' % (ind, k))
        elif op in ('EQV', 'IMP'):
            # Table 6.2: Boolean 0/-1 result (manual 6.4.3).
            tx = self._nv(t)
            ty = self._nv(t)
            L.append('%sif isinstance(%s, str) or isinstance(%s, str):'
                     % (ind, av, bv))
            L.append('%s    raise BE("Type mismatch")' % ind)
            L.append('%s%s = -1 if %s else 0' % (ind, tx, av))
            L.append('%s%s = -1 if %s else 0' % (ind, ty, bv))
            if op == 'EQV':
                L.append('%s%s = -1 if (%s == 0) == (%s == 0) else 0'
                         % (ind, v, tx, ty))
            else:
                L.append('%s%s = 0 if (%s != 0 and %s == 0) else -1'
                         % (ind, v, tx, ty))
            L.append('%s%s = "int"' % (ind, k))
        else:
            raise CompileSkip('unknown operator %r' % (op,))
        return v, k

    # -- statement fragments ------------------------------------------------ #
    def _target_leaves(self, tgt, L, ind, t):
        """An assignment/read target as a node with pre-evaluated (leaf)
        subscripts: ('var', name) or ('arr', name, [leaf, ...])."""
        if tgt[0] == 'var':
            return "('var', %r)" % (tgt[1],)
        subs = []
        for sub in tgt[2]:
            sv, _sk = self.ex(sub, L, ind, t)
            subs.append('leaf(%s)' % sv)
        return "('arr', %r, [%s])" % (tgt[1], ', '.join(subs))

    def _print_items(self, items, L, ind, t):
        """PRINT items list with pre-evaluated leaves (consumed by
        do_print / do_print_file's own eval_with_kind)."""
        parts = []
        for item in items:
            if item[0] == 'using':
                ev, _ = self.ex(item[1], L, ind, t)
                arg_parts = []
                for a in item[2]:
                    ea, _ = self.ex(a, L, ind, t)
                    arg_parts.append('leaf(%s)' % ea)
                parts.append("('using', leaf(%s), [%s])"
                             % (ev, ', '.join(arg_parts)))
            else:
                first, sep = item
                if (isinstance(first, tuple)
                        and first[0] in ('__tab__', '__spc__')):
                    marker, nnode, expr = first
                    ev, ek = self.ex(nnode, L, ind, t)
                    if expr is not None:
                        # The trailing item is displayed at its own kind
                        # (do_print's eval_with_kind): pass the kind.
                        ee, ek2 = self.ex(expr, L, ind, t)
                        e = 'leaf(%s, %s)' % (ee, ek2)
                    else:
                        e = 'None'
                    parts.append('((%r, leaf(%s, %s), %s), %r)'
                                 % (marker, ev, ek, e, sep))
                else:
                    ev, ek = self.ex(first, L, ind, t)
                    parts.append('(leaf(%s, %s), %r)' % (ev, ek, sep))
        return ', '.join(parts)

    # -- statements --------------------------------------------------------- #
    def stmt(self, stmt, L, ind, t):
        """Emit code for one statement (no pc_stmt guard: the caller has
        set cur_stmt_idx and checked key traps)."""
        tag = stmt[0]
        if tag == 'let':
            ev, _ek = self.ex(stmt[2], L, ind, t)
            tgt = stmt[1]
            if tgt[0] == 'var':
                L.append('%sclet(g, %r, %s)' % (ind, tgt[1], ev))
            else:
                subs = []
                for sub in tgt[2]:
                    sv, _sk = self.ex(sub, L, ind, t)
                    subs.append('int(%s)' % sv)
                L.append('%sclet_a(g, %r, (%s,), %s)'
                         % (ind, tgt[1], ', '.join(subs), ev))
        elif tag == 'print':
            L.append('%sg.do_print([%s])'
                     % (ind, self._print_items(stmt[1], L, ind, t)))
        elif tag == 'print_file':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            parts = self._print_items(stmt[3], L, ind, t)
            L.append('%sg.do_print_file(("print_file", leaf(%s), None, [%s]))'
                     % (ind, ev, parts))
        elif tag == 'input':
            if stmt[1] is not None:
                ev, _ek = self.ex(stmt[1], L, ind, t)
                p = 'leaf(%s)' % ev
            else:
                p = 'None'
            names = ', '.join(repr(n) for n in stmt[2])
            suppress = stmt[3] if len(stmt) > 3 else False
            L.append('%sg.do_input(%s, [%s], %r)' % (ind, p, names, suppress))
        elif tag == 'input_file':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            names = ', '.join(repr(n) for n in stmt[2])
            L.append('%sg.do_input_file(("input_file", leaf(%s), [%s]))'
                     % (ind, ev, names))
        elif tag == 'write':
            # WRITE items are bare expressions (no separators), each
            # evaluated at its own kind by do_write.
            wparts = []
            for e in stmt[2]:
                ev, ek = self.ex(e, L, ind, t)
                wparts.append('leaf(%s, %s)' % (ev, ek))
            if stmt[1] is None:
                f = 'None'
            else:
                ev, _ek = self.ex(stmt[1], L, ind, t)
                f = 'leaf(%s)' % ev
            L.append('%sg.do_write(("write", %s, [%s]))'
                     % (ind, f, ', '.join(wparts)))
        elif tag == 'goto':
            L.append('%sgoto_fast(g, %r); return 1' % (ind, stmt[1]))
        elif tag == 'gosub':
            # Top-level GOSUB: the dispatcher's except-Gosub computes the
            # resume point from cur_line/cur_stmt_idx, exactly like
            # _step_line.  (A GOSUB inside IF actions is cone'd - see
            # _actions_simple - because it needs the action-step
            # continuation machinery.)
            L.append('%sraise Gosub(%r)' % (ind, stmt[1]))
        elif tag == 'return':
            L.append('%sraise Return(%r)' % (ind, stmt[1]))
        elif tag == 'on_goto':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            lines = repr(stmt[2])
            L.append('%s_i = oi(g, %s, %s)' % (ind, ev, lines))
            L.append('%sif _i is not None:' % ind)
            L.append('%s    goto_fast(g, %s[_i - 1]); return 1' % (ind, lines))
        elif tag == 'on_gosub':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            lines = repr(stmt[2])
            L.append('%s_i = oi(g, %s, %s)' % (ind, ev, lines))
            L.append('%sif _i is not None:' % ind)
            L.append('%s    raise Gosub(%s[_i - 1])' % (ind, lines))
        elif tag == 'if':
            self._stmt_if(L, ind, t, stmt)
        elif tag == 'for':
            self._stmt_for(L, ind, t, stmt)
        elif tag == 'next':
            L.append('%s_r = nx(g, %r)' % (ind, stmt[1]))
            L.append('%sif _r is not None:' % ind)
            L.append('%s    g.pc, g.pc_stmt = _r' % ind)
            L.append('%s    return 1' % ind)
        elif tag == 'next_multi':
            L.append('%s_r = nxm(g, %r)' % (ind, stmt[1]))
            L.append('%sif _r is not None:' % ind)
            L.append('%s    g.pc, g.pc_stmt = _r' % ind)
            L.append('%s    return 1' % ind)
        elif tag == 'while':
            self._stmt_while(L, ind, t, stmt)
        elif tag == 'wend':
            L.append('%sif not g.while_stack:' % ind)
            L.append('%s    raise BE("WEND without WHILE")' % ind)
            L.append('%s_wl, _wi, _ = g.while_stack.pop()' % ind)
            L.append('%sgoto_fast(g, _wl, _wi); return 1' % ind)
        elif tag == 'do':
            cond = stmt[1]
            if cond is not None:
                cd = self.d(cond)
                L.append('%sif not g._loop_condition_holds(D%d):' % (ind, cd))
                L.append('%s    _pos = g.find_matching_loop_pos(g.pc, g.cur_stmt_idx)' % ind)
                L.append('%s    if _pos is not None:' % ind)
                L.append('%s        _dl, _di = _pos' % ind)
                L.append('%s        if _di + 1 < len(g.program[_dl]):' % ind)
                L.append('%s            goto_fast(g, _dl, _di + 1); return 1' % ind)
                L.append('%s        goto_fast(g, g.next_line_map.get(_dl), 0); return 1' % ind)
            if cond is not None:
                L.append('%sg.do_stack.append((g.pc, g.cur_stmt_idx, D%d))'
                         % (ind, cd))
            else:
                L.append('%sg.do_stack.append((g.pc, g.cur_stmt_idx, None))' % ind)
        elif tag == 'loop':
            cond = stmt[1]
            L.append('%sif not g.do_stack:' % ind)
            L.append('%s    raise BE("LOOP without DO")' % ind)
            L.append('%s_dl, _di, _ = g.do_stack.pop()' % ind)
            if cond is not None:
                cd = self.d(cond)
                L.append('%sif g._loop_condition_holds(D%d):' % (ind, cd))
                L.append('%s    goto_fast(g, _dl, _di); return 1' % ind)
            else:
                L.append('%sgoto_fast(g, _dl, _di); return 1' % ind)
        elif tag == 'else':
            L.append('%sg.do_else(D%d)' % (ind, self.d(stmt)))
        elif tag == 'read':
            tgts = []
            for tgt in stmt[1]:
                if tgt[0] == 'var':
                    tgts.append("('var', %r)" % (tgt[1],))
                else:
                    subs = []
                    for sub in tgt[2]:
                        sv, _sk = self.ex(sub, L, ind, t)
                        subs.append('leaf(%s)' % sv)
                    tgts.append("('arr', %r, [%s])" % (tgt[1], ', '.join(subs)))
            L.append('%sg.do_read([%s])' % (ind, ', '.join(tgts)))
        elif tag == 'restore':
            L.append('%sg.do_restore(%r)' % (ind, stmt[1]))
        elif tag == 'dim':
            parts = []
            for name, dims_expr in stmt[1]:
                subs = []
                for sub in dims_expr:
                    sv, _sk = self.ex(sub, L, ind, t)
                    subs.append('leaf(%s)' % sv)
                parts.append('(%r, [%s])' % (name, ', '.join(subs)))
            L.append('%sg.do_dim(("dim", [%s]))' % (ind, ', '.join(parts)))
        elif tag == 'redim':
            subs = []
            for sub in stmt[2]:
                sv, _sk = self.ex(sub, L, ind, t)
                subs.append('leaf(%s)' % sv)
            L.append('%sg.do_redim(("redim", %r, [%s], %r))'
                     % (ind, stmt[1], ', '.join(subs), stmt[3]))
        elif tag == 'erase':
            L.append('%sg.do_erase(%r)' % (ind, list(stmt[1])))
        elif tag == 'swap':
            a = self._target_leaves(stmt[1], L, ind, t)
            b = self._target_leaves(stmt[2], L, ind, t)
            L.append('%sg.do_swap(("swap", %s, %s))' % (ind, a, b))
        elif tag == 'open':
            mode = stmt[1]
            if mode is None:
                m = 'None'
            elif isinstance(mode, str):
                m = repr(mode)
            else:
                ev, _ek = self.ex(mode, L, ind, t)
                m = 'leaf(%s)' % ev
            fv, _fk = self.ex(stmt[2], L, ind, t)
            fname = stmt[3]
            if isinstance(fname, str):
                fm = repr(fname)
            else:
                ev, _ek = self.ex(fname, L, ind, t)
                fm = 'leaf(%s)' % ev
            if stmt[4] is not None:
                ev, _ek = self.ex(stmt[4], L, ind, t)
                rl = 'leaf(%s)' % ev
            else:
                rl = 'None'
            L.append('%sg.do_open(("open", %s, leaf(%s), %s, %s))'
                     % (ind, m, fv, fm, rl))
        elif tag == 'close':
            expr = stmt[1]
            if expr is None:
                L.append('%sg.do_close(None)' % ind)
            elif isinstance(expr, list):
                parts = []
                for sub in expr:
                    sv, _sk = self.ex(sub, L, ind, t)
                    parts.append('leaf(%s)' % sv)
                L.append('%sg.do_close([%s])' % (ind, ', '.join(parts)))
            else:
                ev, _ek = self.ex(expr, L, ind, t)
                L.append('%sg.do_close(leaf(%s))' % (ind, ev))
        elif tag == 'get':
            fv, _fk = self.ex(stmt[1], L, ind, t)
            if stmt[2] is not None:
                rv, _rk = self.ex(stmt[2], L, ind, t)
                r = 'leaf(%s)' % rv
            else:
                r = 'None'
            if stmt[3] is None:
                vt = 'None'
            else:
                vt = self._target_leaves(stmt[3], L, ind, t)
            L.append('%sg.do_get(("get", leaf(%s), %s, %s))'
                     % (ind, fv, r, vt))
        elif tag == 'seek':
            fv, _fk = self.ex(stmt[1], L, ind, t)
            vt = self._target_leaves(stmt[2], L, ind, t)
            L.append('%sg.do_seek(("seek", leaf(%s), %s))' % (ind, fv, vt))
        elif tag == 'kill':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            L.append('%sg.files.kill(%s)' % (ind, ev))
        elif tag == 'put':
            fv, _fk = self.ex(stmt[1], L, ind, t)
            if stmt[2] is not None:
                rv, _rk = self.ex(stmt[2], L, ind, t)
                r = 'leaf(%s)' % rv
            else:
                r = 'None'
            if stmt[3] is None:
                d = 'None'
            else:
                ev, ek = self.ex(stmt[3], L, ind, t)
                d = 'leaf(%s, %s)' % (ev, ek)
            L.append('%sg.do_put(("put", leaf(%s), %s, %s))'
                     % (ind, fv, r, d))
        elif tag == 'line_input':
            fv, _fk = self.ex(stmt[1], L, ind, t)
            vt = self._target_leaves(stmt[2], L, ind, t)
            L.append('%sg.do_line_input(("line_input", leaf(%s), %s))'
                     % (ind, fv, vt))
        elif tag == 'line_input_key':
            vt = self._target_leaves(stmt[1], L, ind, t)
            if len(stmt) > 2 and stmt[2] is not None:
                ev, _ek = self.ex(stmt[2], L, ind, t)
                p = 'leaf(%s)' % ev
            else:
                p = 'None'
            L.append('%sg.do_line_input_key(%s, %s)' % (ind, vt, p))
        elif tag == 'get_key':
            vt = self._target_leaves(stmt[1], L, ind, t)
            L.append('%sg.do_get_key(%s)' % (ind, vt))
        elif tag == 'wait':
            parts = []
            for sub in stmt[1]:
                sv, _sk = self.ex(sub, L, ind, t)
                parts.append('leaf(%s)' % sv)
            L.append('%sg.do_wait([%s])' % (ind, ', '.join(parts)))
        elif tag == 'error':
            ev, _ek = self.ex(stmt[1], L, ind, t)
            L.append('%sg.do_error(leaf(%s))' % (ind, ev))
        elif tag == 'on_error':
            ln = stmt[1]
            L.append('%sif %r == 0 and g._in_error_handler:' % (ind, ln))
            L.append('%s    raise BE(g._trapped_error or "Error")' % ind)
            L.append('%sg.error_handler = None if %r in (None, 0) else %r'
                     % (ind, ln, ln))
            L.append('%sg._in_error_handler = False' % ind)
        elif tag == 'resume':
            L.append('%sg.do_resume(%r)' % (ind, stmt[1]))
        elif tag == 'resume_next':
            L.append('%sg.do_resume_next()' % ind)
        elif tag == 'end':
            L.append('%sg.files.close()' % ind)
            L.append('%sraise Stop()' % ind)
        elif tag == 'stop':
            L.append('%sraise Break(g.pc)' % ind)
        elif tag == 'system':
            L.append('%sg.files.close()' % ind)
            L.append('%sraise Stop()' % ind)
        elif tag == 'new':
            L.append('%sg.program.clear()' % ind)
            L.append('%sg.reset_state()' % ind)
            L.append('%sg.trace = False' % ind)
            L.append('%sg.trace_rate = None' % ind)
            L.append('%sg.trace_pause = False' % ind)
            L.append('%sg._new_cleared = True' % ind)
            L.append('%sraise Stop()' % ind)
        elif tag in ('rem', 'data', 'endif', 'palette', 'palette_using',
                     'edit', 'lprint', 'lprint_using', 'on_timer'):
            pass  # no code (same as the interpreter)
        elif tag == 'cls':
            if stmt[1] is not None:
                ev, _ek = self.ex(stmt[1], L, ind, t)
                L.append('%sif int(%s) not in (0, 1, 2):' % (ind, ev))
                L.append('%s    raise BE("Illegal function call")' % ind)
            L.append('%sg.screen.cls()' % ind)
            L.append('%sif g.screen.virtual:' % ind)
            L.append('%s    g.output_func("\\033[2J\\033[H")' % ind)
        elif tag == 'beep':
            L.append('%sg.output_func("\\a")' % ind)
        elif tag == 'sound':
            ev1, _ = self.ex(stmt[1], L, ind, t)
            ev2, _ = self.ex(stmt[2], L, ind, t)
            L.append('%sif g.system.sound(%s, %s) and g.system._winsound is None:'
                     % (ind, ev1, ev2))
            L.append('%s    g.output_func("\\a")' % ind)
        elif tag == 'sleep':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg._sleep_seconds(%s)' % (ind, ev))
        elif tag == 'setfps':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg.screen.set_fps(%s)' % (ind, ev))
        elif tag == 'locate':
            parts = []
            for p in stmt[1]:
                if p is None:
                    parts.append('None')
                else:
                    ev, _ = self.ex(p, L, ind, t)
                    parts.append('leaf(%s)' % ev)
            L.append('%sg.do_locate([%s])' % (ind, ', '.join(parts)))
        elif tag == 'option':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%s_nb = int(%s)' % (ind, ev))
            L.append('%sif _nb not in (0, 1):' % ind)
            L.append('%s    raise BE("Illegal function call")' % ind)
            L.append('%sif _nb != g.option_base and g._arrays_in_use():' % ind)
            L.append('%s    raise BE("Illegal function call")' % ind)
            L.append('%sg.option_base = _nb' % ind)
        elif tag == 'def_fn':
            # The body is evaluated at call time (call_def_fn_k), so store
            # the static AST nodes.
            L.append('%sg.def_fns[%r] = (D%d, D%d)'
                     % (ind, stmt[1], self.d(stmt[2]), self.d(stmt[3])))
        elif tag == 'def_type':
            for name in stmt[2]:
                L.append('%sg.def_types[%r] = %r'
                         % (ind, name.upper(), stmt[1]))
        elif tag == 'type':
            L.append('%sg.types[%r] = D%d' % (ind, stmt[1], self.d(stmt[2])))
        elif tag == 'common':
            L.append('%sg.common_vars = getattr(g, "common_vars", []) + %r'
                     % (ind, list(stmt[1])))
        elif tag == 'key':
            ev1, _ = self.ex(stmt[1], L, ind, t)
            ev2, _ = self.ex(stmt[2], L, ind, t)
            L.append('%s_n = int(%s)' % (ind, ev1))
            L.append('%sif not ((1 <= _n <= 10) or (15 <= _n <= 20)):' % ind)
            L.append('%s    raise BE("Illegal function call")' % ind)
            L.append('%s_s = str(%s)' % (ind, ev2))
            L.append('%sif 1 <= _n <= 10:' % ind)
            L.append('%s    g.key_defs[_n] = _s[:15]' % ind)
            L.append('%selse:' % ind)
            L.append('%s    if len(_s) < 2:' % ind)
            L.append('%s        raise BE("Illegal function call")' % ind)
            L.append('%s    g.key_defs[_n] = (ord(_s[0]), ord(_s[1]))' % ind)
        elif tag == 'key_state':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg.do_key_state(leaf(%s), %r)' % (ind, ev, stmt[2]))
        elif tag == 'key_on':
            L.append('%sg.system.key_on()' % ind)
        elif tag == 'key_off':
            L.append('%sg.system.key_off()' % ind)
        elif tag == 'key_list':
            L.append('%sfor _n in sorted(g.key_defs):' % ind)
            L.append('%s    _v = g.key_defs[_n]' % ind)
            L.append('%s    if isinstance(_v, tuple):' % ind)
            L.append('%s        g.write("KEY %%d = CHR$(%%d)+CHR$(%%d)\\n" %% (_n, _v[0], _v[1]), newline=False)' % ind)
            L.append('%s    else:' % ind)
            L.append('%s        g.write("KEY %%d = \\"%%s\\"\\n" %% (_n, _v.ljust(15)), newline=False)' % ind)
        elif tag == 'environ':
            if stmt[1] is not None:
                ev, _ = self.ex(stmt[1], L, ind, t)
                L.append('%sg.system.environ(%s)' % (ind, ev))
            else:
                L.append('%sg.system.environ(None)' % ind)
        elif tag == 'cursor':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg.screen.cursor(%s)' % (ind, ev))
        elif tag == 'color':
            parts = []
            for p in stmt[1:4]:
                if p is None:
                    parts.append('None')
                else:
                    ev, _ = self.ex(p, L, ind, t)
                    parts.append(ev)
            L.append('%sg.screen.color(%s)' % (ind, ', '.join(parts)))
        elif tag == 'ink':
            ev1, _ = self.ex(stmt[1], L, ind, t)
            if stmt[2] is None:
                L.append('%sg.screen.ink(%s, None)' % (ind, ev1))
            else:
                ev2, _ = self.ex(stmt[2], L, ind, t)
                L.append('%sg.screen.ink(%s, %s)' % (ind, ev1, ev2))
        elif tag == 'screen':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg.screen.set_mode(int(%s))' % (ind, ev))
            if stmt[3] is not None:
                ev, _ = self.ex(stmt[3], L, ind, t)
                L.append('%sg.screen.apage = int(%s)' % (ind, ev))
            if stmt[4] is not None:
                ev, _ = self.ex(stmt[4], L, ind, t)
                L.append('%sg.screen.vpage = int(%s)' % (ind, ev))
        elif tag == 'textsize':
            if stmt[1] is None:
                L.append('%sg.screen.textsize(None)' % ind)
            else:
                ev, _ = self.ex(stmt[1], L, ind, t)
                L.append('%sg.screen.textsize(%s)' % (ind, ev))
        elif tag == 'textrotate':
            if stmt[1] is None:
                L.append('%sg.screen.textrotate(None)' % ind)
            else:
                ev, _ = self.ex(stmt[1], L, ind, t)
                L.append('%sg.screen.textrotate(%s)' % (ind, ev))
        elif tag == 'textfont':
            L.append('%sg.screen.textfont(%r, %r, %r)'
                     % (ind, stmt[1], stmt[2], stmt[3]))
        elif tag == 'view':
            if stmt[1] is None:
                L.append('%sg.screen.view_rect = None' % ind)
                L.append('%sg.screen.view_screen = False' % ind)
            else:
                parts = []
                for p in stmt[1:5]:
                    ev, _ = self.ex(p, L, ind, t)
                    parts.append(ev)
                parts.append(repr(stmt[5]))
                L.append('%sg.screen.view(%s)' % (ind, ', '.join(parts)))
        elif tag == 'window':
            if stmt[1] is None:
                L.append('%sg.screen.window(None)' % ind)
            else:
                parts = []
                for p in stmt[1:5]:
                    ev, _ = self.ex(p, L, ind, t)
                    parts.append(ev)
                parts.append(repr(stmt[5]))
                L.append('%sg.screen.window(%s)' % (ind, ', '.join(parts)))
        elif tag == 'wclose':
            L.append('%sg.screen.wclose()' % ind)
        elif tag == 'pause':
            L.append('%sg.do_pause()' % ind)
        elif tag == 'draw':
            ev, _ = self.ex(stmt[1], L, ind, t)
            L.append('%sg.screen.draw(str(%s))' % (ind, ev))
        elif tag == 'out':
            ev1, _ = self.ex(stmt[1], L, ind, t)
            ev2, _ = self.ex(stmt[2], L, ind, t)
            L.append('%sg.system.out(%s, %s)' % (ind, ev1, ev2))
        elif tag == 'poke':
            pairs = []
            for addr, val in stmt[1]:
                ea, _ = self.ex(addr, L, ind, t)
                ev, _ = self.ex(val, L, ind, t)
                pairs.append('(%s, %s)' % (ea, ev))
            L.append('%sfor _a, _b in [%s]:' % (ind, ', '.join(pairs)))
            L.append('%s    g.system.poke(_a, _b)' % ind)
        elif tag == 'bload':
            ev1, _ = self.ex(stmt[1], L, ind, t)
            if stmt[2] is not None:
                ev2, _ = self.ex(stmt[2], L, ind, t)
                m = ev2
            else:
                m = 'None'
            if stmt[3] is not None:
                ev3, _ = self.ex(stmt[3], L, ind, t)
                s = ev3
            else:
                s = 'None'
            L.append('%sg.system.bload(%s, %s, %s)' % (ind, ev1, m, s))
        elif tag == 'bsave':
            parts = []
            for p in stmt[1:4]:
                ev, _ = self.ex(p, L, ind, t)
                parts.append(ev)
            L.append('%sg.system.bsave(%s)' % (ind, ', '.join(parts)))
        elif tag == 'def_seg':
            if stmt[1] is not None:
                ev, _ = self.ex(stmt[1], L, ind, t)
                L.append('%sg.system.def_seg(%s)' % (ind, ev))
            else:
                L.append('%sg.system.def_seg(None)' % ind)
        elif tag == 'trap':
            L.append('%sg._trap = %r' % (ind, stmt[1]))
        elif tag == 'on_key':
            L.append('%sg.do_on_key(%r, %r)' % (ind, stmt[1], stmt[2]))
        elif tag == 'mid_assign':
            subs = []
            for sub in stmt[1][1:]:
                sv, _ = self.ex(sub, L, ind, t)
                subs.append('leaf(%s)' % sv)
            ev, ek = self.ex(stmt[2], L, ind, t)
            L.append('%sg.do_mid_assign((%r, %s), leaf(%s, %s))'
                     % (ind, stmt[1][0], ', '.join(subs), ev, ek))
        elif tag in ('lset', 'rset'):
            ev, ek = self.ex(stmt[2], L, ind, t)
            L.append('%sg.do_lset_rset((%r, %s, leaf(%s, %s)), left=%r)'
                     % (ind, tag, stmt[1], ev, ek, tag == 'lset'))
        elif tag == 'field':
            fv, _ = self.ex(stmt[1], L, ind, t)
            parts = []
            for w_expr, var in stmt[2]:
                ev, _ = self.ex(w_expr, L, ind, t)
                parts.append('(leaf(%s), %r)' % (ev, var))
            L.append('%sg.do_field(("field", leaf(%s), [%s]))'
                     % (ind, fv, ', '.join(parts)))
        elif tag == 'field_old':
            parts = []
            for p in stmt[1:4]:
                ev, _ = self.ex(p, L, ind, t)
                parts.append('leaf(%s)' % ev)
            L.append('%sg.do_field_old(("field_old", %s, %s, %s, %r))'
                     % (ind, parts[0], parts[1], parts[2], stmt[4]))
        else:
            # Invisible interpreter fallback: same AST node, same handler
            # (graphics drawing, PLAY, RANDOMIZE, SCREENSIZE, ...).
            L.append('%scone(g, D%d)' % (ind, self.d(stmt)))

    # -- control-flow statements -------------------------------------------- #
    def _stmt_for(self, L, ind, t, stmt):
        # Manual FORNEXT (reading (b)): the final value is set on the
        # counter BEFORE the initial-value expression is evaluated.
        var = stmt[1]
        ev, _ = self.ex(stmt[3], L, ind, t)   # end first
        L.append('%sg.assign(%r, %s)' % (ind, var, ev))
        sv, _ = self.ex(stmt[2], L, ind, t)   # then start
        tv, _ = self.ex(stmt[4], L, ind, t)   # then step
        L.append('%sg.assign(%r, %s)' % (ind, var, sv))
        L.append('%sif g.for_should_continue(%s, %s, %s):' % (ind, sv, ev, tv))
        L.append('%s    _bs = ((g.pc, g.cur_stmt_idx + 1)'
                 % ind)
        L.append('%s            if g.cur_stmt_idx + 1 < len(g.cur_line)'
                 % ind)
        L.append('%s            else (g.next_line_map.get(g.pc), 0))' % ind)
        L.append('%s    g.for_stack.append((%r, %s, %s, %s, _bs))'
                 % (ind, var.upper(), sv, ev, tv))
        L.append('%selse:' % ind)
        L.append('%s    # Empty loop: skip to just past the matching NEXT.' % ind)
        L.append('%s    _np = g.find_matching_next_pos(g.pc, g.cur_stmt_idx)' % ind)
        L.append('%s    if _np is not None:' % ind)
        L.append('%s        _nl, _ni = _np' % ind)
        L.append('%s        if _ni + 1 < len(g.program[_nl]):' % ind)
        L.append('%s            goto_fast(g, _nl, _ni + 1); return 1' % ind)
        L.append('%s        goto_fast(g, g.next_line_map.get(_nl), 0); return 1' % ind)

    def _stmt_while(self, L, ind, t, stmt):
        L.append('%s_pos = g.find_matching_wend_pos(g.pc, g.cur_stmt_idx)' % ind)
        L.append('%sif _pos is None:' % ind)
        L.append('%s    raise BE("WHILE without WEND")' % ind)
        L.append('%s_wl, _wi = _pos' % ind)
        cv, _ = self.ex(stmt[1], L, ind, t)
        L.append('%sif not %s:' % (ind, cv))
        L.append('%s    # Not entering: skip to just past the WEND.' % ind)
        L.append('%s    if _wi + 1 < len(g.program[_wl]):' % ind)
        L.append('%s        goto_fast(g, _wl, _wi + 1); return 1' % ind)
        L.append('%s    goto_fast(g, g.next_line_map.get(_wl), 0); return 1' % ind)
        L.append('%s_bs = ((g.pc, g.cur_stmt_idx + 1)'
                 % ind)
        L.append('%s        if g.cur_stmt_idx + 1 < len(g.cur_line)'
                 % ind)
        L.append('%s        else (g.next_line_map.get(g.pc), 0))' % ind)
        L.append('%sg.while_stack.append((g.pc, g.cur_stmt_idx, _bs))' % ind)

    # -- IF ------------------------------------------------------------------ #
    def _actions_simple(self, actions):
        for a in actions:
            if a[0] == 'stmt':
                tag = a[1][0]
                if tag == 'if':
                    c = a[1]
                    if not (self._actions_simple(c[2])
                            and (c[3] is None or self._actions_simple(c[3]))):
                        return False
                elif tag not in self.SIMPLE:
                    return False
            elif a[0] in ('goto', 'fall'):
                # 'fall' = multi-line IF (body on the following lines);
                # _stmt_if owns its ELSE-claiming/terminator logic.
                continue
            else:
                return False
        return True

    def _stmt_if(self, L, ind, t, stmt):
        cond, then_a, else_a = stmt[1], stmt[2], stmt[3]
        then_fall = (then_a == [('fall',)])
        if not (self._actions_simple(then_a)
                and (else_a is None or self._actions_simple(else_a))):
            # GOSUB / FOR / DO / WHILE / STOP inside the actions: let the
            # interpreter's action machinery own this IF.
            L.append('%scone(g, D%d)' % (ind, self.d(stmt)))
            return
        cv, _ = self.ex(cond, L, ind, t)
        L.append('%s_cl = {m[1] for m in g.skip_else_stack}' % ind)
        L.append('%sif %s:' % (ind, cv))
        if then_fall:
            # Multi-line IF ... THEN: fall through to the THEN block; find
            # and claim the matching ELSE at runtime (same as do_if).
            L.append('%s    _tgt = g.find_matching_else(g.pc, _cl)' % ind)
            L.append('%s    if _tgt is not None:' % ind)
            L.append('%s        g.skip_else_stack.append((g.pc, _tgt[0]))' % ind)
        else:
            self._stmt_actions(then_a, L, ind + '    ', t)
            if else_a is None:
                # A THEN statement on the IF line claims a later ELSE line
                # (nested IFs may have claimed some already: re-read).
                L.append('%s    _cl2 = {m[1] for m in g.skip_else_stack}' % ind)
                L.append('%s    _tgt = g.find_matching_else(g.pc, _cl2)' % ind)
                L.append('%s    if _tgt is not None:' % ind)
                L.append('%s        g.skip_else_stack.append((g.pc, _tgt[0]))' % ind)
        if else_a is not None:
            L.append('%selse:' % ind)
            if else_a == [('fall',)]:
                # Bare "ELSE" at end of line: fall into the following line
                # (the ELSE block), exactly like do_if's exec_actions.
                L.append('%s    pass' % ind)
            else:
                self._stmt_actions(else_a, L, ind + '    ', t)
        elif then_fall:
            # Block ends at the first unmatched ELSE or ENDIF line.
            L.append('%selse:' % ind)
            L.append('%s    _tgt = g.find_if_terminator(g.pc, _cl)' % ind)
            L.append('%s    if _tgt is not None:' % ind)
            L.append('%s        _ln, _kind, _hs = _tgt' % ind)
            L.append('%s        if _kind == "else":' % ind)
            L.append('%s            if _hs:' % ind)
            L.append('%s                raise Goto(_ln)' % ind)
            L.append('%s            raise Goto(g.next_line_map[_ln])' % ind)
            L.append('%s        raise Goto(g.next_line_map.get(_ln))' % ind)
            L.append('%s    raise Goto(g.next_line_map[g.pc])' % ind)
        # single-line IF with no ELSE: do nothing

    def _stmt_actions(self, actions, L, ind, t):
        """Emit code for a single-line IF's THEN/ELSE action list."""
        for a in actions:
            if a[0] == 'goto':
                L.append('%sgoto_fast(g, %r); return 1' % (ind, a[1]))
            elif a[0] == 'stmt':
                L.append('%sif g._trap: ct(g)' % ind)
                self.stmt(a[1], L, ind, t)
            # ('fall',) contributes no code

    # -- line / module assembly ---------------------------------------------- #
    def line(self, num):
        stmts = self.prog[num]
        L = []
        L.append('def L%d():' % num)
        L.append('    g = G')
        L.append('    g.cur_line = DL%d' % num)
        t = [0]
        for i, s in enumerate(stmts):
            # pc_stmt guards give mid-line entry (GOSUB resume, RETURN,
            # RESUME, key-trap re-entry, single-line FOR bodies) exactly the
            # interpreter's execute_line(start_idx) semantics.
            L.append('    if g.pc_stmt <= %d:' % i)
            L.append('        g.cur_stmt_idx = %d' % i)
            L.append('        if g._trap: ct(g)')
            self.stmt(s, L, '        ', t)
        # Fall through (no explicit jump): return None; the dispatcher
        # advances g.pc via next_line_map, exactly like _step_line.
        return '\n'.join(L)

    def source(self):
        parts = []
        for i, obj in enumerate(self.data):
            parts.append('D%d = %r' % (i, obj))
        for num in self.g.lines:
            parts.append(self.line(num))
            parts.append('')
        return '\n'.join(parts)


# --------------------------------------------------------------------------- #
#  Compiled run loop + cache management
# --------------------------------------------------------------------------- #
def compile_program(g):
    """Compile the in-memory program; returns {line: function} or raises
    CompileSkip (any failure silently falls back to the interpreter)."""
    try:
        c = WayneCompiler(g)
        src = c.source()
        dump = os.environ.get('WAYNE_DUMP')
        if dump:
            with open(dump, 'w', encoding='utf-8') as f:
                f.write('# wayne.py generated Python (debug dump)\n')
                f.write(src)
        ns = {
            '__builtins__': __builtins__,
            'G': g,
            'Goto': Goto, 'Gosub': Gosub, 'Return': Return,
            'Break': Break, 'Stop': Stop, 'BE': BasicError,
            'MX': g._MACHINE_MAX, '_MX': -g._MACHINE_MAX,
            'ct': _w_ct, 'cv': _w_cv, 'cvt': _w_cvt, 'cvs': _w_cvs,
            'noa': _w_noa, 'ar': _w_ar,
            'leaf': _w_leaf, 'clet': _w_clet, 'clet_a': _w_clet_a,
            'om': _w_om, 'rs': round_single, 'ri': _w_ri, 'n16': _w_n16,
            'cbk': _w_cbk, 'uc': _w_uc, 'vp': _w_vp, 'vps': _w_vps,
            'goto_fast': _w_goto_fast, 'nx': _w_nx, 'nxm': _w_nxm,
            'oi': _w_oi, 'cone': _w_cone,
        }
        for i, obj in enumerate(c.data):
            ns['D%d' % i] = obj
        for num in g.lines:
            ns['DL%d' % num] = g.program[num]
        exec(src, ns)
        fns = {num: ns['L%d' % num] for num in g.lines}
        return fns
    except CompileSkip:
        raise
    except Exception:
        # A compile-time bug must never kill the user's RUN: fall back to
        # the interpreter (invisible).
        raise CompileSkip('compile failed')


def _wayne_compiled_funcs(g):
    """Return the compiled {line: function} map for the current program,
    or None when the interpreter loop must be used."""
    if os.environ.get('WAYNE_FORCE_INTERP'):
        return None
    c = getattr(g, '_compiled', None)
    if c is False:
        return None
    if isinstance(c, dict):
        return c
    try:
        fns = compile_program(g)
    except CompileSkip:
        g._compiled = False
        return None
    g._compiled = fns
    return fns


def _wayne_run_loop(g, fns):
    """The compiled execution loop: _run_loop's per-line duties with
    _step_line replaced by a call to the generated line function.  The
    exception handlers below are _step_line's, verbatim."""
    while g.pc is not None:
        # Drain the window's Tk queue (throttled) BEFORE the stop check.
        g.screen.pump_if_due()
        if g.screen._stop_requested:
            g.screen._stop_requested = False
            raise KeyboardInterrupt
        if g.screen._interrupt:
            g.screen._interrupt = False
            raise KeyboardInterrupt
        # TRACE ON [lines per second]: display + pace (see _run_loop).
        if g.trace and g.trace_rate is not None:
            if g._trace_last is not None:
                delay = g._trace_last + g.trace_rate - time.time()
                if delay > 0:
                    time.sleep(delay)
            g._trace_last = time.time()
            if g.trace_pause:
                g._trace_pause_count -= 1
            text = g.source.get(g.pc)
            if text is not None:
                g.io.write_console("Trace: %6d %s" % (g.pc, text), newline=True)
            else:
                g.io.write_console("Trace: line %d" % g.pc, newline=True)
        try:
            # A RETURN from a GOSUB whose statement sat inside a single-line
            # IF's THEN/ELSE actions first resumes that action list (set by
            # the Return handler from the GOSUB stack entry), then continues
            # with the statements after the IF on the same line.
            if g._resume_actions is not None:
                steps, if_line, line_c, stmt_c = g._resume_actions
                # pc stays at the IF line while the steps run (ERL and
                # break messages); restore the resume line afterwards.
                g.pc = if_line
                g._exec_action_steps(steps, if_line, line_c, stmt_c)
                g.pc = line_c
                g.pc_stmt = stmt_c
                g._resume_actions = None
            line = g.program.get(g.pc)
            if line is None:
                raise BasicError("Undefined line number")
            # A None result means the line fell through to the end; any
            # other return value means the line jumped (GOTO / loop
            # back-edge) and already set g.pc / g.pc_stmt.
            if fns[g.pc]() is None:
                # The line executed without error: its one-shot re-run
                # guard (a RESUME re-run) is now consumed, and control
                # continues with the next line.
                g._resume_suppress = False
                g.pc = g.next_line_map.get(g.pc)
                g.pc_stmt = 0
        except Goto as e:
            # A Goto leaves the error handler only when it is raised by a
            # RESUME (do_resume / do_resume_next clear error_line first).
            if g.error_line is None:
                g._in_error_handler = False
            if not e.resuming_from_handler:
                g._resume_suppress = False
            # A jump abandons any IF-action continuation a RETURN left
            # pending.
            g._resume_actions = None
            if e.line not in g.program:
                # Fail here, while pc is still the GOTO line (so ERL is
                # that line, not the undefined target), via the normal
                # trap path.
                g._trap_or_raise(BasicError("Undefined line number"))
            else:
                g._filter_skip_else(e.line)
                g.pc = e.line
                g.pc_stmt = e.stmt_idx
        except Gosub as e:
            if g.error_line is None:
                g._in_error_handler = False
            if e.line not in g.program:
                # A GOSUB to an undefined line reports ERR=8 without
                # pushing a return address.
                g._trap_or_raise(BasicError("Undefined line number"))
            else:
                cont = None
                if_line = None
                if e.resume is not None:
                    # The GOSUB sat inside a single-line IF's THEN/ELSE
                    # actions (via the cone fallback): resume that action
                    # list, then continue after the IF.
                    cont = e.resume
                    if g._resume_actions is not None:
                        (if_line, line_c, stmt_c) = \
                            (g._resume_actions[1], g._resume_actions[2],
                             g._resume_actions[3])
                        g._resume_actions = None
                    elif g.cur_stmt_idx + 1 < len(g.cur_line):
                        if_line = g.pc
                        line_c, stmt_c = g.pc, g.cur_stmt_idx + 1
                    else:
                        if_line = g.pc
                        line_c, stmt_c = g.next_line_map.get(g.pc), 0
                elif e.trap_key is not None:
                    # A GOSUB entered by an ON KEY(n) trap interrupted the
                    # statement about to run (cur_stmt_idx): resume there.
                    line_c, stmt_c = g.pc, g.cur_stmt_idx
                elif g.cur_stmt_idx + 1 < len(g.cur_line):
                    line_c, stmt_c = g.pc, g.cur_stmt_idx + 1
                else:
                    line_c, stmt_c = g.next_line_map.get(g.pc), 0
                g.gosub_stack.append(GosubEntry(line_c, stmt_c, e.trap_key,
                                                cont, if_line))
                g.pc = e.line
                g.pc_stmt = 0
        except Return as r:
            if g.error_line is None:
                g._in_error_handler = False
            if r.line is not None:
                # Non-local RETURN (manual RETURN).
                if g.gosub_stack and g.gosub_stack[-1].trap_key is not None:
                    g._rearm_key(g.gosub_stack.pop().trap_key)
                for n, tr in list(g.key_traps.items()):
                    if tr.get('in_trap'):
                        tr['in_trap'] = False
                        g._rearm_key(n)
                g._resume_actions = None
                g._filter_skip_else(r.line)
                g.pc = r.line
                g.pc_stmt = 0
            elif not g.gosub_stack:
                g._resume_actions = None
                g._trap_or_raise(BasicError("RETURN without GOSUB"))
            else:
                entry = g.gosub_stack.pop()
                if entry.trap_key is not None:
                    g._rearm_key(entry.trap_key)
                g._resume_actions = None
                if entry.cont is not None:
                    g._resume_actions = (entry.cont, entry.if_line,
                                         entry.line, entry.stmt_idx)
                    g.pc = entry.if_line
                    g.pc_stmt = entry.stmt_idx
                else:
                    g.pc = entry.line
                    g.pc_stmt = entry.stmt_idx
        except Break as b:
            g._stopped = True
            g.io.write("Break in line %d"
                       % (b.line if b.line is not None else g.pc),
                       newline=True)
            if g._resume_actions is not None:
                g.pc = g._resume_actions[2]
                g.pc_stmt = g._resume_actions[3]
            else:
                # Advance past the break so CONT resumes at the following
                # line (a trace stop already leaves pc at the next line).
                g.pc = g.next_line_map.get(g.pc)
                g.pc_stmt = 0
            raise
        except Stop:
            g._stopped = False
            g.pc = None
            g._resume_actions = None
        except BasicError as e:
            g._resume_actions = None
            g._trap_or_raise(e)
        # TRACE ON <rate> PAUSE (see _run_loop): once per <rate> lines.
        if (g.trace_pause and g.pc is not None
                and g._trace_pause_count <= 0):
            g._trace_pause_count = g.trace_lps or 1
            g._pause_wait()
        # Batch-render any graphics changes made by this line.
        g.screen._paint_due = True
        g.screen.flush()


def _wayne_run(g):
    """wayne's RUN/CONT entry: execute via the compiled Python when
    possible, else the built-in interpreter loop (same state, same
    semantics either way)."""
    fns = _wayne_compiled_funcs(g)
    if fns is not None:
        if os.environ.get('WAYNE_REPORT'):
            g._wayne_report = True
            g._wayne_falls = []
        try:
            _wayne_run_loop(g, fns)
        finally:
            if getattr(g, '_wayne_report', False):
                g._wayne_report = False
                falls = g._wayne_falls
                g._wayne_falls = None
                try:
                    if falls:
                        counts = {}
                        for _pc, tag in falls:
                            counts[tag] = counts.get(tag, 0) + 1
                        detail = ', '.join('%s=%d' % kv
                                           for kv in sorted(counts.items()))
                        g.io.write('Wayne: compiled path; %d interpreter-fallback statement(s): %s'
                                   % (len(falls), detail), newline=True)
                    else:
                        g.io.write('Wayne: compiled path; 0 interpreter fallbacks',
                                   newline=True)
                except Exception:
                    pass
    else:
        if os.environ.get('WAYNE_REPORT'):
            g.io.write('Wayne: interpreter path (whole program skipped compilation)',
                       newline=True)
        g._run_loop()


class BasicREPL:
    def __init__(self, output_func=None, input_func=None, gui=False):
        self.program = {}
        self.source = {}
        self.output_func = output_func if output_func is not None else sys.stdout.write
        self.input_func = input_func if input_func is not None else input
        self.gui = gui
        # The file the in-memory program came from (a LOAD/RUN file or a
        # saved name).  A bare SAVE writes back here; COMPILE never changes
        # it.  None for a NEW program that has never been saved.
        self.last_file = None
        # Where the in-memory program lives on disk (or will): equals
        # last_file while the two agree, or a timestamped temp .bas name in
        # the working folder once COMPILE had to build an unsaved program.
        # A SAVE renames the temp onto the real name, if one is parked.
        self.most_recent_file = None
        # True once the program has changed (a line entered, deleted, or
        # renumbered) since the last LOAD or SAVE.  LOAD, NEW, and SAVE
        # clear it; COMPILE never does (it compiles a temp instead).
        self.dirty = False
        # True while most_recent_file is a temp .bas created by COMPILE and
        # never saved to a real name.  LOAD and NEW delete such a temp (and
        # its exe) when they replace the program.
        self._temp_unsaved = False
        # Path of the .exe produced by the last COMPILE (used by a bare CRUN).
        self._compile_exe = None
        self._type_block = None
        # Multi-line IF continuation buffer: a list of (line_num, text) pairs
        # accumulating the lines of an IF statement that spans multiple lines
        # (manual IF: nesting is limited only by line length).  Cleared when
        # the IF is complete or on NEW/LOAD.
        self._if_buffer = None
        # The current line: the last line referenced by EDIT, LIST, or an
        # error message (manual EDIT); used by the "." line reference.
        self.current_line = None
        # AUTO mode (manual AUTO): (next line number, increment) while
        # automatic line numbering is active, None otherwise.
        self.auto = None
        self.interpreter = Interpreter(self.program, self.output_func, self.input_func, self.gui)
        self.interpreter.screen._interp = self.interpreter
        # The I/O middle layer (see IoDevice): routes every print and key of
        # both the program and the interpreter's own messages to the
        # graphics window while it is open and to the console once it is
        # closed.
        self.io = IoDevice(self.interpreter.screen, self.output_func,
                           self.input_func, _read_key)
        self.interpreter._io = self.io

    def _emit(self, text, newline=True):
        self.io.write(text, newline)

    def update_interpreter(self):
        self.interpreter.program = self.program
        self.interpreter.source = self.source
        self.interpreter.lines = sorted(self.program.keys())
        self.interpreter.next_line_map = self.interpreter._build_next_line_map()
        self.interpreter.build_data_pool()
        self.interpreter._compiled = None  # invalidate compiled cache

    def load_line(self, line):
        line = line.strip()
        if not line:
            return
        parts = line.split(None, 1)
        if not parts[0].isdigit():
            # Immediate-mode (unnumbered) statement.
            try:
                stmts = parse_program_line(line)
                self.interpreter.run_immediate(stmts)
            except BasicError as e:
                self._emit("Error: %s" % e)
            # Show the result immediately: immediate mode has no run-loop
            # end-of-line flush, so a graphics statement typed here (e.g.
            # SCREENSIZE / WINDOW) would otherwise not open its window until
            # some later statement.  No-op when nothing was drawn.
            self.interpreter.screen.paint_now()
            return
        line_num = int(parts[0])
        rest = parts[1] if len(parts) > 1 else ''
        if not rest:
            # A line number by itself deletes that line from the program
            # (standard GW-BASIC behavior).  A nonexistent line is a no-op.
            if line_num in self.program:
                del self.program[line_num]
                self.source.pop(line_num, None)
                self.dirty = True
                self.update_interpreter()
            return
        upper = rest.strip().upper()
        # Multi-line TYPE ... END TYPE block (manual TYPE): accumulate the
        # field lines and let _finish_type_block synthesize the one-line
        # "TYPE name (fields...)" statement at END TYPE.  A TYPE line that
        # already contains parentheses is the one-line form and parses
        # normally below.
        if self._type_block is not None:
            if upper == 'END TYPE' or upper.startswith('END TYPE'):
                self._finish_type_block(line_num)
            else:
                self._type_block['lines'].append(rest.strip())
            return
        if upper == 'TYPE' or upper.startswith('TYPE '):
            if '(' not in rest:
                self._type_block = {'start': line_num,
                                    'name': rest.strip()[4:].strip(),
                                    'lines': []}
                return
        # Multi-line IF ... THEN ... ELSE continuation (manual IF: nesting is
        # limited only by line length, so an IF's THEN/ELSE may sit on the
        # following line(s)).  We only intercept the safe case where a line
        # is *just* an IF expression (no THEN/ELSE/GOTO on it yet); lines
        # that already contain THEN/ELSE parse normally and are unaffected.
        if self._if_buffer is not None:
            # A REM-only line inside a multi-line IF carries no code: skip
            # it instead of feeding it to the continuation parser (a
            # flattened REM token would swallow the following THEN/ELSE
            # and the IF could never complete).
            try:
                toks = tokenize(rest)
            except BasicError:
                toks = []  # malformed line: not a REM; _finalize_if_buffer
                           # below reports the real error
            if toks and toks[0][0] == 'rem':
                return
            self._if_buffer['follow'].append(rest)
            self._finalize_if_buffer()
            return
        if _is_bare_if_expression(rest) or _is_bare_if_comma(rest):
            # Incomplete IF (e.g. "IF A > 3" or "IF A > 3 ,"): start
            # accumulating the THEN/ELSE continuation lines.
            self._if_buffer = {'start': line_num, 'text': rest, 'follow': []}
            return
        try:
            stmts = parse_program_line(rest)
            self.program[line_num] = stmts
            self.source[line_num] = rest
            self.dirty = True
            self.update_interpreter()
        except BasicError as e:
            self._emit("Syntax error in line %d: %s" % (line_num, e))

    def _check_open_if_buffer(self):
        """Called after loading a complete program from a file.  If a
        multi-line IF was still open at end of file, every line after it
        has been absorbed into the buffer; report a syntax error at the IF's
        start line and discard the partial statement so the rest of the
        program is not silently lost from memory."""
        if self._if_buffer is not None:
            self._emit("Syntax error in line %d: IF statement is not completed "
                       "before end of file" % self._if_buffer['start'])
            self._if_buffer = None

    def _finalize_if_buffer(self):
        """Try to complete the multi-line IF being accumulated in
        _if_buffer.  When complete, store its AST on the start line and
        clear the buffer; otherwise keep accumulating."""
        buf = self._if_buffer
        if buf is None:
            return
        try:
            stmts, consumed, needs_more = \
                parse_statement_with_continuation(buf['text'],
                                                  buf['follow'])
        except BasicError as e:
            # A malformed continuation line (e.g. an unterminated string)
            # must not kill the interpreter: report it and discard the
            # partial IF so the next line starts fresh.
            self._if_buffer = None
            self._emit("Syntax error in line %d: %s" % (buf['start'], e))
            return
        if needs_more:
            return
        self._if_buffer = None
        self.program[buf['start']] = stmts
        # Record a joined source view for the start line (for LIST/trace).
        joined = (buf['text'] + ' ' + ' '.join(buf['follow'][:consumed])).strip()
        self.source[buf['start']] = joined
        self.dirty = True
        self.update_interpreter()

    def _finish_type_block(self, end_line):
        tb = self._type_block
        self._type_block = None
        fields = []
        for text in tb['lines']:
            m = re.match(r'(\S+)\s+AS\s+(\S+)(?:\s*\*\s*(\d+))?',
                         text, re.IGNORECASE)
            if m:
                fname, ftype, flen = m.group(1), m.group(2).upper(), m.group(3)
                if flen:
                    fields.append('%s AS %s (%s)' % (fname, ftype, flen))
                else:
                    fields.append('%s AS %s' % (fname, ftype))
        type_stmt = 'TYPE %s (%s)' % (tb['name'], ', '.join(fields))
        try:
            stmts = parse_program_line(type_stmt)
            self.program[tb['start']] = stmts
            self.source[tb['start']] = type_stmt
            self.dirty = True
            self.update_interpreter()
        except BasicError as e:
            self._emit("Syntax error in line %d: %s" % (tb['start'], e))

    def run(self, start_line=None):
        self.update_interpreter()
        self.interpreter.reset_state()  # every RUN starts with fresh state
        # True once the program has TERMINATED (not merely stopped for CONT):
        # its files must then be closed, as END does ("END closes all files";
        # END at the end of a program is optional, so a run-off-the-end
        # behaves the same).  Without this, a program that ends in an
        # untrapped error (or runs off the end) leaves its files open - and
        # locked on Windows - while the interpreter sits at the command level.
        terminated = False
        try:
            try:
                self.interpreter.run(start_line)
                # Normal completion: ran off the end (or END/SYSTEM, which
                # already closed the files - closing again is a no-op).
                terminated = True
            except Break:
                # STOP: "Break in line nnnnn" was already printed; return to
                # the command level without a Python traceback (manual STOP).
                self._emit("")
            except TraceStop:
                # TRACE ON: "Break in line nnnnn" was already printed; return to
                # the command level so the user can CONT (manual TRACE).
                pass
            except BasicError as e:
                # Include the line that caused the error (manual: "Error in
                # line nnnnn"); the interpreter's pc is that line while a
                # program is running.
                if self.interpreter.pc is not None:
                    self._emit("Error in line %d: %s" % (self.interpreter.pc, e))
                    self.current_line = self.interpreter.pc
                else:
                    self._emit("Error: %s" % e)
                # An untrapped error terminates the program: close its files
                # so none stays open (and locked on Windows) while we sit
                # back at the command level.
                terminated = True
            except KeyboardInterrupt:
                # Ctrl+C (console) or ESC/X (window): stop the running
                # BASIC program and return to the interpreter prompt
                # without exiting the interpreter, and close the graphics
                # window.  Both stop routes end up here: the console
                # Ctrl+C arrives as a KeyboardInterrupt raised in the main
                # thread, and the window's ESC / close box sets the stop
                # flags which the run loop turns into the same exception.
                # The window is destroyed HERE, at a clean Python boundary
                # outside any window event dispatch - destroying it from
                # inside the interrupt handling used to crash the
                # interpreter.
                self.interpreter.screen.close()
                self._emit("Break")
                # Ctrl+C/ESC/X terminates the program (it is not
                # CONT-resumable): close its files like any finished run.
                terminated = True
        finally:
            if terminated:
                # Stopped programs (Break, TraceStop) keep their files open
                # AND keep any sound running: the program's world - a
                # PLAYMUSIC'd file, a ringing SOUND tone - is frozen at the
                # stop, not torn down, so CONT resumes it exactly as it was
                # (quiet it at the prompt with STOPMUSIC).  A terminated run
                # closes its files and stops all sound here (music also
                # stops when the graphics window closes - see Screen.close).
                self.interpreter.files.close()
                self.interpreter.system.stop_speaker()
                self.interpreter.system.music_stop()
        # A NEW statement inside the program clears memory and returns to
        # the command level (manual NEW); drop the stored source too.
        if getattr(self.interpreter, '_new_cleared', False):
            self.interpreter._new_cleared = False
            self.source.clear()
            self._type_block = None
            self._if_buffer = None
        self.update_interpreter()

    def cont_command(self):
        # CONT (manual CONT): resume a stopped program (after STOP, a break,
        # or a trace stop).  No-op with a message if nothing is stopped.
        if not (self.interpreter._stopped and self.interpreter.pc is not None):
            self._emit("CONT is only valid after a STOP, break, or trace stop")
            return
        self.update_interpreter()
        # See run(): terminated programs must leave no files open.
        terminated = False
        try:
            try:
                self.interpreter.cont()
                # The resumed program finished on its own (ran off the end,
                # or END/SYSTEM, which already closed the files): close
                # anything still open, as run() does.
                terminated = True
            except Break:
                self._emit("")
            except TraceStop:
                pass  # "Break in line nnnnn" was already printed
            except BasicError as e:
                if self.interpreter.pc is not None:
                    self._emit("Error in line %d: %s" % (self.interpreter.pc, e))
                    self.current_line = self.interpreter.pc
                else:
                    self._emit("Error: %s" % e)
                # An untrapped error terminates the resumed program: close
                # its files, as run() does.
                terminated = True
            except KeyboardInterrupt:
                # Ctrl+C / ESC / X: stop the resumed program and return to
                # the prompt without exiting the interpreter.  Same window
                # rules as BasicREPL.run: the graphics window is closed
                # here, at a clean point outside any window event dispatch.
                self.interpreter.screen.close()
                self._emit("Break")
                # Ctrl+C/ESC/X terminates the program (not CONT-resumable):
                # close its files like any finished run.
                terminated = True
        finally:
            if terminated:
                # Stopped programs (Break, TraceStop) keep their files open
                # AND keep any sound running (the world is frozen at the
                # stop, not torn down - see BasicREPL.run); a terminated run
                # closes its files and stops all sound here, as run() does
                # (music also stops when the graphics window closes - see
                # Screen.close).
                self.interpreter.files.close()
                self.interpreter.system.stop_speaker()
                self.interpreter.system.music_stop()
        if getattr(self.interpreter, '_new_cleared', False):
            self.interpreter._new_cleared = False
            self.source.clear()
            self._type_block = None
            self._if_buffer = None
        self.update_interpreter()

    def trace_command(self, argstr=''):
        # TRACE ON [lines per second] [PAUSE] / TRACE OFF (manual TRACE): display
        # the line being executed at the given rate, pacing the program
        # to that rate (default 3 lines per second, range 1 to 100).  The
        # optional PAUSE holds at the Ok prompt after each traced line so the
        # user can CONT to continue.  Bare TRACE reports the current state.
        argstr = argstr.strip()
        up = argstr.upper()
        if up == 'ON' or up.startswith('ON '):
            pause = False
            rate_str = ''
            if up != 'ON':
                rest = argstr.split(None, 1)[1].split()
                # Drop a trailing PAUSE token (case-insensitive); the
                # remainder is the rate.
                if rest and rest[-1].upper() == 'PAUSE':
                    pause = True
                    rest = rest[:-1]
                rate_str = ' '.join(rest)
            if rate_str == '':
                rate = 3
            else:
                try:
                    rate = float(rate_str)
                except ValueError:
                    self._emit("Error: lines per second must be a number (1 to 100)")
                    return
                if not rate.is_integer():
                    self._emit("Error: lines per second must be a whole number (1 to 100)")
                    return
                rate = int(rate)
            if rate < 1 or rate > 100:
                self._emit("Error: lines per second must be between 1 and 100")
                return
            self.interpreter.trace = True
            self.interpreter.trace_rate = 1.0 / rate
            self.interpreter.trace_lps = rate
            self.interpreter.trace_pause = pause
            self.interpreter._trace_pause_count = rate if pause else 0
            self.interpreter._trace_last = None
            if pause:
                self._emit("Trace on: %d lines per second (press ENTER or SPACE after every %d lines)" % (rate, rate))
            else:
                self._emit("Trace on: %d lines per second" % rate)
        elif up == 'OFF':
            self.interpreter.trace = False
            self.interpreter.trace_rate = None
            self.interpreter.trace_lps = None
            self.interpreter.trace_pause = False
            self.interpreter._trace_pause_count = 0
            self._emit("Trace off")
        else:
            if self.interpreter.trace and self.interpreter.trace_rate is not None:
                rate_txt = "%d lines per second" % int(round(1.0 / self.interpreter.trace_rate))
                if self.interpreter.trace_pause:
                    rate_txt += " (press ENTER or SPACE after every %d lines)" % int(round(1.0 / self.interpreter.trace_rate))
                self._emit("Trace on: %s" % rate_txt)
            else:
                self._emit("Trace off")

    def show_tokens(self):
        """TOKEN command: display every program line and its tokens.

        For each line in the program the original line is shown, followed
        by the line's token stream on the next line.  The line number is
        not part of the token stream; only the statement text is
        tokenized.
        """
        if not self.program:
            self._emit("No program lines")
            return
        for line in sorted(self.program.keys()):
            self._emit("%d %s" % (line, self.source[line]))
            try:
                tokens = tokenize(self.source[line])
            except BasicError as e:
                self._emit("Syntax error in line %d: %s" % (line, e))
                continue
            self._emit(format_tokens(tokens))

    def list_program(self, start=None, end=None):
        for line in sorted(self.program.keys()):
            if start is not None and line < start:
                continue
            if end is not None and line > end:
                break
            self._emit("%d %s" % (line, self.source[line]))

    def _list_line_num(self, text):
        """Resolve a LIST/DELETE/EDIT line reference ('.' = current line)."""
        text = text.strip()
        if text == '.':
            if self.current_line is None:
                lines = sorted(self.program.keys())
                self.current_line = lines[0] if lines else None
            return self.current_line
        if not text.isdigit():
            raise BasicError("Illegal function call")
        return int(text)

    def list_command(self, argstr=''):
        """LIST [line number][-line number][,filename] (manual LIST).

        Hyphen ranges: "10-20", "20-" (to end), "-20" (from beginning).
        A period (.) substitutes for the current line.  An optional
        filename lists to a file instead of the screen.
        """
        argstr = argstr.strip()
        filename = None
        if ',' in argstr:
            argstr, fn = argstr.split(',', 1)
            filename = fn.strip().strip('"')
        argstr = argstr.strip()
        start, end = None, None
        if argstr:
            if '-' in argstr:
                a, b = argstr.split('-', 1)
                start = self._list_line_num(a) if a.strip() else None
                end = self._list_line_num(b) if b.strip() else None
            else:
                start = end = self._list_line_num(argstr)
        lines = []
        for line in sorted(self.program.keys()):
            if start is not None and line < start:
                continue
            if end is not None and line > end:
                break
            lines.append(line)
        if start is not None and not lines:
            # A specific line (or range) that does not exist.
            if start == end and start not in self.program:
                raise BasicError("Undefined line number")
        text_lines = ["%d %s" % (line, self.source[line]) for line in lines]
        if filename:
            with open(filename, 'w') as f:
                for t in text_lines:
                    f.write(t + "\n")
        else:
            for t in text_lines:
                self._emit(t)
        if lines:
            self.current_line = lines[-1]

    def delete_lines(self, argstr=''):
        """DELETE [line number1][-line number2] (manual DELETE).

        "DELETE 40-" deletes from line 40 to the end; "DELETE -40" deletes
        through line 40; "." is the current line.  A bare DELETE is an
        "Illegal function call".
        """
        argstr = argstr.strip()
        if not argstr:
            raise BasicError("Illegal function call")
        if '-' in argstr:
            a, b = argstr.split('-', 1)
            start = self._list_line_num(a) if a.strip() else None
            end = self._list_line_num(b) if b.strip() else None
        else:
            start = end = self._list_line_num(argstr)
        removed = [line for line in sorted(self.program.keys())
                   if (start is None or line >= start)
                   and (end is None or line <= end)]
        if not removed:
            raise BasicError("Undefined line number")
        for line in removed:
            del self.program[line]
            self.source.pop(line, None)
        self.dirty = True
        self.update_interpreter()

    def edit_line(self, argstr=''):
        """EDIT line number | EDIT . (manual EDIT).

        Displays the line (positioning for editing) and makes it the
        current line; a nonexistent line is "Undefined line number".
        """
        argstr = argstr.strip()
        if not argstr:
            raise BasicError("Illegal function call")
        line = self._list_line_num(argstr)
        if line not in self.program:
            raise BasicError("Undefined line number")
        self.current_line = line
        self._emit("%d %s" % (line, self.source[line]))

    def ledit_line(self, argstr=''):
        """LEDIT line number (manual LEDIT).

        Displays the referenced line for in-place editing, with the cursor
        positioned after the last character of the line.  The LEFT and
        RIGHT arrow keys move the cursor; BACKSPACE and DELETE remove
        characters; typed characters are inserted at the cursor (they do
        not overwrite existing text).  ENTER stores the edited line;
        ESC or CTRL+C cancels and leaves the line unchanged.  A
        nonexistent line is "Undefined line number".
        """
        argstr = argstr.strip()
        if not argstr:
            raise BasicError("Illegal function call")
        line = self._list_line_num(argstr)
        if line not in self.program:
            raise BasicError("Undefined line number")
        self.current_line = line

        if not sys.stdin.isatty():
            # Not an interactive console: fall back to a plain display.
            self._emit("%d %s" % (line, self.source[line]))
            return

        original = self.source[line]
        buf = list(original)
        pos = len(buf)  # cursor starts after the last character
        prefix = "%d " % line

        _enable_vt_processing()
        out = sys.stdout.write
        flush = sys.stdout.flush
        # Anchor of the editor line on the monitor (captured once when the
        # first window draw happens; see _monitor_line_redraw).
        anchor = [None, None]

        def emit_nl():
            # A fresh line, on the monitor while the window is open and on
            # the console once it is closed.
            if self.io.window_live():
                self.io.write('\n', newline=False)
            else:
                out('\n')
                flush()

        def draw():
            if self.io.window_live() and not self.io._stopped():
                if anchor[0] is None:
                    screen = self.interpreter.screen
                    if screen.is_text():
                        pc, pr = screen.cols, screen.rows
                    else:
                        pc, pr = screen._gfx_text_page()
                    anchor[0] = min(screen.cursor_row, pr - 1)
                    anchor[1] = min(screen.cursor_col, pc - 1)
                _monitor_line_redraw(self.interpreter.screen, anchor[0],
                                     anchor[1], prefix, buf, pos)
                return
            # Clear the line, write the prefix + buffer, then reposition
            # the cursor to `pos`.
            text = prefix + ''.join(buf)
            cursor_text = prefix + ''.join(buf[:pos])
            out('\x1b[2K\x1b[G' + text + '\x1b[G' + cursor_text)
            flush()

        draw()
        committed = False
        while True:
            try:
                # Keys come through the I/O middle layer: the window's
                # keyboard while it is open, the console otherwise.
                key = self.io.read_key()
            except KeyboardInterrupt:
                # Ctrl+C: cancel the edit and return to the Ok prompt
                # (it must not exit the interpreter).
                break
            except Exception:
                key = 'escape'  # can't read keys: cancel the edit
            if key is None:
                continue
            if key == 'enter':
                committed = True
                break
            if key == 'escape' and self.io.window_live():
                # ESC with the window open closes the window (like the Ok
                # prompt); the edit is cancelled and the prompt follows on
                # the console.
                self.interpreter.screen._on_escape()
                self.interpreter.screen.pump()
                break
            if key in ('escape', 'ctrl_c'):
                break
            if key == 'left':
                if pos > 0:
                    pos -= 1
            elif key == 'right':
                if pos < len(buf):
                    pos += 1
            elif key == 'home':
                pos = 0
            elif key == 'end':
                pos = len(buf)
            elif key == 'backspace':
                if pos > 0:
                    del buf[pos - 1]
                    pos -= 1
            elif key == 'delete':
                if pos < len(buf):
                    del buf[pos]
            elif key == 'tab':
                buf.insert(pos, '\t')
                pos += 1
            elif len(key) == 1:
                # Printable character: insert at the cursor (insert mode).
                buf.insert(pos, key)
                pos += 1
            # Any other key (up/down/pageup/pagedown) is ignored.
            draw()

        if not committed:
            # Cancel: clear the editor line, leave the program unchanged,
            # and move to a fresh line (no "Ready" is printed for LEDIT).
            if self.io.window_live():
                self.io.write('\n', newline=False)
            else:
                out('\x1b[2K\x1b[G\n')
                flush()
            return

        new_text = ''.join(buf)
        try:
            stmts = parse_program_line(new_text)
        except BasicError as e:
            # Reject the edit; redraw the original line, report the error on
            # its own line, and move to a fresh line.
            buf = list(original)
            pos = len(buf)
            draw()
            emit_nl()
            self._emit("Syntax error in line %d: %s" % (line, e))
            return

        self.program[line] = stmts
        self.source[line] = new_text
        self.dirty = True
        self.update_interpreter()
        # Leave the edited line on screen, then move to a fresh line so the
        # next input starts cleanly (no "Ready" is printed for LEDIT).
        pos = len(buf)
        draw()
        emit_nl()

    def load_command(self, filename, keep_files=False, run_after=False):
        """LOAD filename[,r] / RUN filename[,r] (manual LOAD/RUN).

        Without keep_files: closes all open files and deletes all variables
        and program lines before loading.  With keep_files: open data files
        and variables are kept intact.  run_after controls whether the
        program runs after loading (LOAD runs only with the r option; RUN
        always runs).
        """
        filename = str(filename).strip().strip('"')
        if not os.path.exists(filename):
            # If the name has no extension, assume .BAS (manual LOAD).  The
            # extension may be stored on disk in either case, so try both.
            if not os.path.splitext(filename)[1]:
                for ext in ('.BAS', '.bas'):
                    if os.path.exists(filename + ext):
                        filename = filename + ext
                        break
                else:
                    raise BasicError("File not found (53)")
            else:
                # Named with an extension: be case-insensitive about the
                # extension (e.g. LOAD bounce.BAS finds bounce.bas).
                base, ext = os.path.splitext(filename)
                for cand in (base + ext.lower(), base + ext.upper()):
                    if os.path.exists(cand):
                        filename = cand
                        break
                else:
                    raise BasicError("File not found (53)")
        if keep_files:
            # r option: keep open files and variables intact.
            self.program.clear()
            self.source.clear()
            self._type_block = None
            self._if_buffer = None
        else:
            self.interpreter.files.close()
            self.program.clear()
            self.source.clear()
            self._type_block = None
            self._if_buffer = None
            self.interpreter.reset_state()
        # .BAS files store lines too long for one physical line with the
        # line number repeated on the following physical line(s) (manual
        # SAVE); _iter_logical_lines reassembles them before parsing.
        for ln, rest in _iter_logical_lines(filename):
            self.load_line('%d %s' % (ln, rest))
        self._check_open_if_buffer()
        # A LOAD replaces the whole program: delete any unsaved temp left by
        # a previous program, then start from a clean state (last file and
        # most recent file are both the file just loaded, nothing dirty).
        # Later edits set dirty again, at which point COMPILE builds a temp
        # instead of touching this file.
        self._cleanup_unsaved_temp()
        self.last_file = filename
        self.most_recent_file = filename
        self.dirty = False
        self._emit("Loaded %s" % filename)
        if run_after:
            self.run()

    # -- native compiler integration (COMPILE / CRUN) -----------------------
    def _compiler_dir(self):
        """Directory that holds the interpreter (and the compiler beside it).

        A frozen build (gwibasic.exe) has no meaningful __file__, so use the
        directory of the running executable; a source run (python gwibasic.py)
        uses the file's directory.
        """
        if getattr(sys, 'frozen', False):
            return os.path.dirname(os.path.abspath(sys.executable))
        return os.path.dirname(os.path.abspath(__file__))

    def _find_gwcbasic(self):
        """Return the argv prefix that launches the gwcbasic compiler, or None.

        Prefers the standalone gwcbasic.exe (works even when gwibasic itself is
        frozen); falls back to running gwcbasic.py with the current
        interpreter.  The compiler must sit next to the interpreter.
        """
        here = self._compiler_dir()
        exe = os.path.join(here, 'gwcbasic.exe')
        if os.path.exists(exe):
            return [exe]
        py = os.path.join(here, 'gwcbasic.py')
        if os.path.exists(py) and not getattr(sys, 'frozen', False):
            return [sys.executable, py]
        return None

    def _resolve_bas(self, name):
        """Resolve a .bas name to an existing path, or None.

        Assumes the .BAS extension when the name has none and is case-
        insensitive about the extension (mirrors manual LOAD).
        """
        name = str(name).strip().strip('"')
        if os.path.exists(name):
            return name
        if not os.path.splitext(name)[1]:
            for ext in ('.BAS', '.bas'):
                if os.path.exists(name + ext):
                    return name + ext
            return None
        base, ext = os.path.splitext(name)
        for cand in (base + ext.lower(), base + ext.upper()):
            if os.path.exists(cand):
                return cand
        return None

    def _write_program(self, path):
        """Write the in-memory program to `path` in the standard
        "line number text" format (the format LOAD and SAVE read back)."""
        with open(path, 'w') as f:
            for line in sorted(self.program.keys()):
                f.write("%d %s\n" % (line, self.source.get(line, '')))

    def _temp_filename(self):
        """A fresh timestamped temp .bas name in the working folder
        (MMDDYYYYHHMM.bas, e.g. 090220261826.bas).  A collision falls back
        to seconds precision, then to a trailing counter."""
        cand = time.strftime('%m%d%Y%H%M') + '.bas'
        if not os.path.exists(cand):
            return cand
        cand = time.strftime('%m%d%Y%H%M%S') + '.bas'
        i = 1
        while os.path.exists(cand):
            cand = time.strftime('%m%d%Y%H%M%S') + '_%d.bas' % i
            i += 1
        return cand

    def _cleanup_unsaved_temp(self):
        """Delete a temp .bas (and its .exe) left over from a COMPILE of a
        program that was never saved, and forget it.  Called by LOAD and NEW:
        an unsaved temp belongs to the program being replaced, so it goes
        away with it.  Quiet on failure (the file may have been moved or
        deleted by hand already)."""
        if self.most_recent_file and self._temp_unsaved:
            stem = self.most_recent_file
            for path in (stem, os.path.splitext(stem)[0] + '.exe'):
                if os.path.exists(path):
                    try:
                        os.remove(path)
                    except OSError:
                        pass
        self.most_recent_file = None
        self._temp_unsaved = False

    def compile_command(self, argstr=''):
        """COMPILE (native compiler integration).

        Builds the current program into a native .exe with the gwcbasic
        compiler.  COMPILE always compiles the file the program currently
        lives in: the loaded/saved file as-is while nothing has changed
        since the last LOAD or SAVE; otherwise a timestamped temp .bas in
        the working folder.  The first such compile creates the temp and
        tells the user its name; later compiles without a SAVE in between
        rewrite and reuse the same temp, never a new one.  COMPILE takes no
        file name, never changes the last file, and never clears the dirty
        state, so it can neither commit experimental edits to a real .bas
        nor compile stale code.  The compilation runs invisibly (no
        cl/compiler output is shown); on success a one-line compile summary
        is printed, then the standard "Ready" prompt follows (printed by the
        command loop after this returns).  A concise error is shown only if
        the compile fails.
        """
        if argstr.strip():
            self._emit("COMPILE takes no argument")
            return
        if not self.program:
            self._emit("Compile failed: no program (LOAD a file or enter lines first)")
            return
        # Choose the file to compile (creating the temp when needed).  While
        # the program is dirty and no temp exists yet, make the temp copy;
        # while a temp exists it is rewritten and reused; otherwise the
        # program matches its file on disk and is compiled as-is.
        if self.dirty and self.most_recent_file == self.last_file:
            temp = self._temp_filename()
            self._write_program(temp)
            self.most_recent_file = temp
            self._temp_unsaved = True
            if self.last_file is None:
                self._emit("Program not saved - compiling as temporary file %s"
                           % temp)
            else:
                self._emit("Edits not saved - compiling as temporary file %s"
                           % temp)
        elif self.dirty:
            # Existing temp (most_recent_file differs from last_file):
            # rewrite it with the current program before compiling it.
            self._write_program(self.most_recent_file)
        src = self.most_recent_file
        if not src or not os.path.exists(src):
            self._emit("Compile failed: %s not found"
                       % (os.path.basename(src) if src else 'program'))
            return
        exe = os.path.splitext(src)[0] + '.exe'
        if os.path.exists(exe):
            try:
                os.remove(exe)
            except OSError:
                pass
        prefix = self._find_gwcbasic()
        if prefix is None:
            self._emit("Compile failed: gwcbasic not found next to gwibasic")
            return
        try:
            # Capture both streams: the process is invisible to the user, but
            # the compiler writes its diagnostics to stdout, which we need to
            # report if the build fails.
            r = subprocess.run(prefix + [src], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
        except OSError as e:
            self._emit("Compile failed: %s" % e)
            return
        if r.returncode == 0 and os.path.exists(exe):
            self._compile_exe = os.path.abspath(exe)
            # A concise compile summary, printed before the command loop's
            # standard "Ready" prompt (no cl/compiler output is shown).
            self._emit("Compiled %s -> %s (%s bytes)"
                       % (os.path.basename(src), os.path.basename(exe),
                          format(os.path.getsize(exe), ",")))
            return
        out = (r.stdout or b'').decode('utf-8', 'replace')
        err = (r.stderr or b'').decode('utf-8', 'replace')
        lines = [l for l in (out + '\n' + err).splitlines() if l.strip()]
        tail = lines[-1].strip() if lines else 'unknown error (code %d)' % r.returncode
        self._emit("Compile failed: %s" % tail)

    def _program_uses_window(self):
        """Heuristic: does the loaded program open a graphics window?  True if
        any statement begins with SCREEN / SCREENSIZE / WINDOW (the statements
        that create a windowed display).  Used to pick the CRUN launch flags
        (a windowed program is launched detached so its window can take the
        foreground; a console program keeps its own console)."""
        for line in self.program:
            for part in self.source.get(line, '').split(':'):
                tok = part.strip().split(None, 1)
                if tok and tok[0].upper() in ('SCREEN', 'SCREENSIZE', 'WINDOW'):
                    return True
        return False

    def _focus_child_window(self, pid, timeout=3.0):
        """Bring a spawned GUI child's window to the foreground (Windows).

        A process launched by a user click gets the Windows foreground lock;
        a process SPAWNED by another does not, so the child's own
        SetForegroundWindow is ignored and its window opens unfocused.  The
        interpreter's console just received input (the user typed CRUN), so it
        holds the lock and can take it via AttachThreadInput and force the
        child's window to the front.
        """
        if os.name != 'nt':
            return
        u32 = ctypes.windll.user32
        k32 = ctypes.windll.kernel32
        WNDENUMPROC = ctypes.WINFUNCTYPE(
            ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)

        def find():
            res = []

            def cb(h, _):
                cpid = ctypes.c_ulong()
                u32.GetWindowThreadProcessId(h, ctypes.byref(cpid))
                if cpid.value == pid:
                    res.append(h)
                return True

            u32.EnumWindows(WNDENUMPROC(cb), 0)
            for h in res:                       # prefer a visible window
                if u32.IsWindowVisible(h):
                    return h
            return res[0] if res else None

        deadline = time.time() + timeout
        hwnd = None
        while True:
            hwnd = find()
            if hwnd:
                break
            if time.time() >= deadline:         # window never appeared
                return
            time.sleep(0.05)
        fore = u32.GetForegroundWindow()
        fore_tid = u32.GetWindowThreadProcessId(fore, None)
        cur_tid = k32.GetCurrentThreadId()
        attached = bool(fore_tid and fore_tid != cur_tid)
        if attached:
            u32.AttachThreadInput(cur_tid, fore_tid, True)
        try:
            u32.ShowWindow(hwnd, 1)             # SW_SHOWNORMAL
            u32.BringWindowToTop(hwnd)
            u32.SetForegroundWindow(hwnd)
            u32.SetActiveWindow(hwnd)
        finally:
            if attached:
                u32.AttachThreadInput(cur_tid, fore_tid, False)

    def crun_command(self, argstr=''):
        """CRUN [filename] (native compiler integration).

        Runs the .exe produced by COMPILE as an independent process, outside
        this console (its own console/window).  The interpreter returns to
        the Ready prompt while the compiled program runs on its own.
        """
        exe = argstr.strip().strip('"') if argstr.strip() else ''
        if not exe or not os.path.exists(exe):
            exe = self._compile_exe or ''
        if not exe or not os.path.exists(exe):
            # Fall back to the .exe that would sit beside the loaded file.
            if self.last_file and os.path.exists(self.last_file):
                cand = os.path.splitext(self.last_file)[0] + '.exe'
                if os.path.exists(cand):
                    exe = cand
        if not exe or not os.path.exists(exe):
            self._emit("Nothing to run (COMPILE first)")
            return
        # Every compiled program is launched with its OWN console
        # (CREATE_NEW_CONSOLE): pre-window output ("starting" etc.) shows
        # there, and the compiled runtime closes it at first window
        # creation (FreeConsole in gwgui.c) -- the console lives until the
        # window opens, then the window is the monitor.  A program that
        # never opens a window keeps its console until it exits.  This is
        # identical to a manual double-click (/SUBSYSTEM:CONSOLE).  When
        # the program is windowed, the interpreter additionally forces the
        # child's window to the front (a spawned process is denied the
        # foreground lock).
        gui = self._program_uses_window() if self.program else True
        if os.name == 'nt':
            proc = subprocess.Popen([exe],
                                    creationflags=subprocess.CREATE_NEW_CONSOLE)
        else:
            proc = subprocess.Popen([exe], start_new_session=True)
        if gui:
            self._focus_child_window(proc.pid)
        self._compile_exe = os.path.abspath(exe)

    def run_command(self, argstr=''):
        """RUN | RUN line number (manual RUN).

        RUN executes the program currently loaded in memory.  With no
        argument it starts at the first line; with a line number argument it
        starts at that line (which must be in the loaded program).  RUN does
        not load a file from disk: to load one first use LOAD (or RUN with a
        line number on already-loaded code).  If no program is loaded, an
        error is reported.
        """
        argstr = argstr.strip()
        # RUN with no argument: run the loaded program from its first line.
        if not argstr:
            if not self.program:
                raise BasicError("No loaded program")
            self.run()
            return
        # RUN line number: start the loaded program at that line.
        if argstr.isdigit():
            if not self.program:
                raise BasicError("No loaded program")
            line = int(argstr)
            if line not in self.program:
                raise BasicError("Undefined line number")
            self.current_line = line
            self.run(line)
            return
        # Anything else (e.g. a filename) is not accepted: RUN only runs
        # already-loaded code.  Use LOAD to bring a file in first.
        raise BasicError("RUN takes no filename. LOAD the program first, then RUN")

    def new(self):
        # NEW (manual NEW): delete the program in memory and clear all
        # variables; data files are closed as well.  The Interpreter (and
        # its graphics window, if one is open) is about to be replaced, so
        # close the window first — with windows now surviving a Ctrl+C
        # stop, NEW would otherwise orphan it.
        self.interpreter.screen.close()
        self.interpreter.files.close()
        self.program.clear()
        self.source.clear()
        self._type_block = None
        self._if_buffer = None
        self.current_line = None
        self.auto = None
        self.interpreter = Interpreter(self.program, self.output_func, self.input_func, self.gui)
        self.interpreter.screen._interp = self.interpreter
        # Point the I/O middle layer at the new screen (the old one was just
        # closed above) so routing keeps working with the fresh interpreter.
        self.io.screen = self.interpreter.screen
        self.interpreter._io = self.io
        # NEW (manual NEW): the fresh interpreter starts from a fresh
        # dynamic RGB color table too; the module-level palette state
        # would otherwise carry the previous program's RGB() allocations
        # across NEW (the next RUN would clear it anyway, but immediate
        # mode between NEW and RUN sees it too).
        _reset_dynamic_rgb()
        # NEW starts a fresh program: forget the previous file and delete
        # any unsaved temp left by a previous program (and its exe), so a
        # later SAVE or COMPILE deals only with this program.
        self._cleanup_unsaved_temp()
        self.last_file = None
        self.dirty = False

    def auto_command(self, argstr=''):
        # AUTO [line number][,[increment]] | AUTO . [,increment] (manual
        # AUTO): start (or restart) automatic line numbering.  The period
        # uses the current line; a missing increment keeps the last one
        # (default 10).  AUTO ends with CTRL-C (see the REPL loop).
        argstr = argstr.strip()
        prev_inc = self.auto[1] if self.auto is not None else 10
        start = 10
        inc = prev_inc
        if argstr:
            parts = argstr.split(',', 1)
            first = parts[0].strip()
            if first == '.':
                # "." is the current line (manual AUTO).
                if self.current_line is None:
                    raise BasicError("Illegal function call")
                start = self.current_line
            elif first:
                if not first.isdigit():
                    raise BasicError("Illegal function call")
                start = int(first)
            if len(parts) > 1 and parts[1].strip():
                if not parts[1].strip().isdigit():
                    raise BasicError("Illegal function call")
                inc = int(parts[1].strip())
            if start < 1 or start > 65529 or inc < 1:
                raise BasicError("Illegal function call")
        self.auto = (start, inc)

    def clear_command(self, argstr=''):
        # CLEAR (no options): zero all numeric variables, null all string
        # variables, and close all open files.  The command also resets array
        # elements, turns off any sound, and disables ON ERROR trapping.
        # CLEAR takes no arguments here; anything on the command line after
        # the command name is a syntax error.
        interp = self.interpreter
        if argstr and argstr.strip():
            raise BasicError("Syntax error in CLEAR")
        # Close all files.
        interp.files.close()
        # Zero all numeric variables and null all string variables; the
        # declared array sizes are kept, only the elements are reset.
        for name in list(interp.vars.keys()):
            if isinstance(interp.vars[name], str):
                interp.vars[name] = ''
            else:
                interp.vars[name] = 0
        for arr in interp.arrays.values():
            for idx in list(arr.keys()):
                if isinstance(arr[idx], str):
                    arr[idx] = ''
                else:
                    arr[idx] = 0
        # Disable ON ERROR trapping.
        interp.error_handler = None
        interp.error_line = None
        interp._in_error_handler = False
        interp._trapped_error = None
        # Turn off any sound.
        interp.system.stop_speaker()
        interp.system.sound_freq = None
        interp.system.sound_end = None

    def load_file(self, filename):
        # If no extension is given, assume .BAS (manual command-line usage),
        # matching the LOAD command's behavior.
        if not os.path.splitext(filename)[1] and not os.path.exists(filename):
            for ext in ('.BAS', '.bas'):
                if os.path.exists(filename + ext):
                    filename = filename + ext
                    break
        try:
            for ln, rest in _iter_logical_lines(filename):
                self.load_line('%d %s' % (ln, rest))
            self._check_open_if_buffer()
            # Command-line run path (python gwibasic.py prog.bas): the same
            # clean state as a LOAD.
            self._cleanup_unsaved_temp()
            self.last_file = filename
            self.most_recent_file = filename
            self.dirty = False
            self._emit("Loaded %s" % filename)
        except FileNotFoundError:
            self._emit("File not found: %s" % filename)

    def save_file(self, filename):
        # Kept as a thin wrapper for SAVE handling, which now lives in
        # save_command (the NEW/LOAD/SAVE/COMPILE state machine).
        self.save_command(filename)

    def save_command(self, name, prompt_func=None):
        """SAVE [filename] (manual SAVE, state machine).

        Writes the program currently in memory to disk.  With a file name
        the program is saved under that name; with no file name it is saved
        back to the last file, or - when there is none (a NEW program that
        was never saved) - the user is asked for a file name.  No options
        are accepted after the file name; the plain "line number text"
        format is always written.

        When a previous COMPILE parked unsaved changes in a temp .bas, the
        current program is written into that temp and the temp (and its
        .exe) is renamed onto the destination, after deleting any existing
        destination .bas/.exe (Windows renames cannot replace).  Otherwise
        the current program is written straight to the destination.  Either
        way, when the save completes the state is exactly the state after a
        LOAD of the saved file: last file and most recent file are both the
        saved name, and nothing is dirty.
        """
        # Resolve the destination name.
        if name is not None and str(name).strip().strip('"'):
            dest = str(name).strip().strip('"')
        elif self.last_file is not None:
            # Bare SAVE with a last file: save back to it.
            self._emit("(saving to %s)" % self.last_file)
            dest = self.last_file
        else:
            # Bare SAVE with no last file: ask for a name.
            if prompt_func is None:
                self._emit("Usage: SAVE [filename]")
                return
            while True:
                try:
                    answer = prompt_func().strip().strip('"')
                except EOFError:
                    # Ctrl+Z/EOF at the prompt: cancel quietly; the
                    # interpreter exits on its next readline.
                    return
                if answer:
                    dest = answer
                    break
        if not os.path.splitext(dest)[1]:
            dest = dest + '.bas'
        try:
            if (self.most_recent_file is not None
                    and self.most_recent_file != dest
                    and self._temp_unsaved):
                # Unsaved changes are parked in a temp: commit them by
                # moving the temp (and its exe) onto the destination.
                # Delete the destination first - on Windows a rename cannot
                # replace an existing file.
                stem_exe = os.path.splitext(dest)[0] + '.exe'
                for path in (dest, stem_exe):
                    if os.path.exists(path):
                        try:
                            os.remove(path)
                        except OSError:
                            pass
                self._write_program(self.most_recent_file)
                temp = self.most_recent_file
                os.rename(temp, dest)
                temp_exe = os.path.splitext(temp)[0] + '.exe'
                if os.path.exists(temp_exe):
                    os.rename(temp_exe, stem_exe)
            else:
                # No temp parked (or the destination is the temp itself):
                # write the current program straight to the destination.
                self._write_program(dest)
        except (IOError, OSError) as e:
            self._emit("Error: %s" % e)
            return
        # The save is done: the state is now exactly the state after a
        # LOAD of the saved file.
        self.last_file = dest
        self.most_recent_file = dest
        self.dirty = False
        self._temp_unsaved = False
        self._emit("Saved %s" % dest)

    def renum(self, argstr=''):
        """RENUM command: renumber program lines and update all references.

        Syntax (per the GW-BASIC manual): RENUM [new number],[old number][,increment]
          new number - first line number of the new sequence (default 10)
          old number - the line where renumbering begins (default: first line)
          increment  - increment of the new sequence (default 10)

        The renumbered lines (in ascending order) are assigned new numbers
        new, new+increment, new+2*increment, ...  By default (plain RENUM)
        every line is renumbered to 10, 20, 30, ....  Every line-number
        reference in the program (GOTO, GOSUB, ON ... GOTO/GOSUB, ON
        ERROR/KEY/TIMER GOTO, and IF ... THEN/ELSE line numbers) is updated
        to point at the renumbered line, in both the parsed statements and
        the stored source text (so LIST and SAVE show the new numbers).

        As in GW-BASIC, RENUM refuses to reorder the lines or to create a
        line number greater than 65529 ("Illegal function call").
        """
        if self._type_block is not None:
            self._emit("Cannot RENUM while a TYPE...END TYPE block is open.")
            return
        if not self.program:
            self._emit("No program lines")
            return
        try:
            new, old, inc = _parse_renum_args(argstr)
        except ValueError as e:
            self._emit("Error: %s" % e)
            return
        if inc <= 0:
            self._emit("Error: increment must be a positive number")
            return
        lines = sorted(self.program.keys())
        # Target lines: from `old` up, or all lines when old is None.
        if old is None:
            target = list(lines)
        else:
            target = [ln for ln in lines if ln >= old]
        if not target:
            self._emit("No lines in range to renumber")
            return
        # Map each target line to its new number.
        mapping = {}
        for i, oln in enumerate(target):
            mapping[oln] = new + i * inc
        # GW-BASIC constraints: no reordering, no line number above 65529.
        if new > 65529 or mapping[target[-1]] > 65529:
            self._emit("Illegal function call")
            return
        if old is not None:
            before = [ln for ln in lines if ln < old]
            if before and new <= before[-1]:
                self._emit("Illegal function call")
                return
        # Rebuild the program: remap line keys and remap AST references.
        new_program = {}
        for oln, stmts in self.program.items():
            newln = mapping.get(oln, oln)
            new_program[newln] = [_renum_stmt(s, mapping) for s in stmts]
        # Rebuild the source text: remap line keys and rewrite references.
        new_source = {}
        for oln, text in self.source.items():
            newln = mapping.get(oln, oln)
            new_source[newln] = _renum_source(text, mapping)
        self.program = new_program
        self.source = new_source
        self.dirty = True
        # Refresh the interpreter's view of the program and clear any stale
        # runtime line state (nothing is running at the Ok prompt, but a
        # previous run may have left an error handler / pc behind).
        self.update_interpreter()
        interp = self.interpreter
        interp.pc = None
        interp.pc_stmt = 0
        interp.cur_line = []
        interp.cur_stmt_idx = 0
        interp.gosub_stack = []
        interp._resume_actions = None
        interp.for_stack = []
        interp.while_stack = []
        interp.do_stack = []
        interp.skip_else_stack = []
        interp.error_handler = None
        interp.error_line = None


# #############################################################################
# Help (data)
# #############################################################################
# Text for the instruction entries is taken from the GW-BASIC User's Guide
# pages in the manual/ subfolder. Entries for statements and functions that
# the manual does not cover (SLEEP, SEEK, REDIM, TYPE, INK, CURSOR,
# DO, LOOP, LPRINT, LSET, RSET, TAB, SPC, PEER, UCASE$, LCASE$,
# TRIM$, ROUNDDOWN, ROUNDFRAC, ROUNDUP, and the DAY/HOUR/MINUTE/MONTH/
# SECOND/YEAR and TIME$ functions) are written to match the behavior of this
# interpreter. HELP_FUNCTIONS holds the built-in function entries.
# HELP_OPERATORS holds the logical operator entries (manual Chapter 6,
# Table 6.2).
#
# Each entry has:
#   title    - heading shown at the top of the detailed help
#   brief    - one-line description used in the HELP list
#   syntax   - the statement/command syntax
#   details  - list of (kind, text); kind is 'p' (paragraph), 'pre' (code),
#              'table' (text table), or 'h' (sub-heading)
#   examples - list of example programs (code blocks)
#   note     - extra note about this implementation, or None
#
# GRAPHICS_TOPICS lists the entry names (across all four tables) that are
# about graphics.  print_help pulls them out of the flat Commands/
# Instructions/Functions lists and shows them under a dedicated
# "Graphics" section so they are easy to find in one place.

HELP_COMMANDS = {
 "BYE": {
  "title": "BYE Command",
  "brief": "Exit the interpreter.",
  "syntax": "BYE",
  "details": [
   [
    "p",
    "BYE quits the GW-BASIC interpreter and returns to the operating system. EXIT and QUIT are synonyms."
   ]
  ],
  "examples": [
   "BYE"
  ],
  "note": None
 },
 "AUTO": {
  "title": "AUTO Command",
  "brief": "Generate and increment line numbers automatically each time you press RETURN.",
  "syntax": "AUTO [line number][,[increment]]\nAUTO .[,[increment]]",
  "details": [
   [
    "p",
    "AUTO is useful for program entry because it makes typing line numbers unnecessary: the next line number is printed as the prompt, and pressing RETURN stores the line you typed under it and advances the number."
   ],
   [
    "p",
    "AUTO begins numbering at line number and increments each subsequent line number by increment; the default for both is 10. The period (.) can be used as a substitute for line number to indicate the current line. If line number is followed by a comma and increment is not specified, the last increment specified in an AUTO command is assumed."
   ],
   [
    "p",
    "If AUTO generates a line number that is already being used, an asterisk appears after the number to warn that any input will replace the existing line."
   ],
   [
    "p",
    "In AUTO mode a line that begins with a line number overrides the auto number, and a bare line number stores a blank line at that number; in both cases the counter continues from the number just stored."
   ],
   [
    "p",
    "AUTO is terminated by entering CTRL-BREAK or CTRL-C, after which the interpreter returns to the command level. As in GW-BASIC, the line in which CTRL-BREAK or CTRL-C is entered is not saved; to be sure that you save all desired text, use them only on lines by themselves."
   ],
   [
    "p",
    "In this interpreter AUTO can also be terminated by pressing RETURN with no text at the line-number prompt: the mode ends and the interpreter returns to the command level, and the line number that was on display is not stored. (In GW-BASIC that action stores a blank line at the displayed number instead.)"
   ]
  ],
  "examples": [
   "AUTO 100, 50\nGenerates line numbers 100, 150, 200, and so on.",
   "AUTO\nGenerates line numbers 10, 20, 30, 40, and so on."
  ],
  "note": None
 },
 "CLEAR": {
  "title": "CLEAR Command",
  "brief": "Set all numeric variables to zero, all string variables to null, and close all open files.",
  "syntax": "CLEAR",
  "details": [
   [
    "p",
    "The CLEAR command sets all numeric variables to zero, sets all string variables to the null string, and closes all open files. It also releases disk buffers, turns off any sound, and disables ON ERROR trapping. Array dimensions declared with DIM are kept; only the elements are reset."
   ],
   [
    "p",
    "CLEAR takes no arguments; any expression or comma following the command is a syntax error."
   ]
  ],
  "examples": [
   "CLEAR\nZeroes variables and nulls all strings."
  ],
  "note": "CLEAR accepts no options in this interpreter."
 },
 "COMPILE": {
  "title": "COMPILE Command",
  "brief": "Build the current program into a native .exe.",
  "syntax": "COMPILE",
  "details": [
   [
    "p",
    "COMPILE builds the current program into a native Windows .exe with the native compiler. The build runs quietly; on success a one-line summary (source file, .exe, and size) is printed, after which CRUN runs the .exe."
   ],
   [
    "p",
    "COMPILE always compiles the file the program currently lives in, and it never writes to a .bas file you have. While nothing has changed since the last LOAD or SAVE it compiles that file as-is. When the program has unsaved changes (a NEW program that was never saved, or edits after a LOAD), the changes are first written to a timestamped temporary file in the working folder (for example 090220261826.bas) and that temporary file is compiled; the temporary file's name is told to you. Compiling again without a SAVE in between rewrites and reuses the same temporary file; a second one is never created. A SAVE then renames the temporary file (and its .exe) onto the saved name, committing the changes."
   ],
   [
    "p",
    "COMPILE takes no file name. It never changes the file a bare SAVE targets, and it never commits experimental edits to a loaded or saved file: the file on disk is left exactly as it was until you SAVE."
   ]
  ],
  "examples": [
   "LOAD CHECKERS.BAS\nREM ... edit a few lines ...\nCOMPILE\nEdits not saved - compiling as temporary file 090220261826.bas\nCRUN\nSAVE CHECKERS.BAS\nSaved CHECKERS.BAS\n(the temporary file is renamed onto CHECKERS.BAS)"
  ],
  "note": "A temporary file left by an unsaved program is deleted by the next LOAD or NEW. A temporary file from a session that ended without a SAVE stays on disk and must be removed by hand."
 },
 "HELP": {
  "title": "HELP Command",
  "brief": "Show help. Use HELP <topic> for details and examples.",
  "syntax": "HELP [command or instruction]",
  "details": [
   [
    "p",
    "Type HELP by itself to list all commands and instructions with a brief description of each."
   ],
   [
    "p",
    "Type HELP followed by a command or instruction name to see a detailed description and examples, taken from the GW-BASIC User Guide."
   ]
  ],
  "examples": [
   "HELP",
   "HELP PRINT",
   "HELP GOTO",
   "HELP BYE"
  ],
  "note": None
 },
 "LIST": {
  "title": "LIST Command",
  "brief": "List program lines (LIST [start] [END stop]).",
  "syntax": "LIST [line number [END line number]]",
  "details": [
   [
    "p",
    "LIST displays the program currently in memory, with line numbers."
   ],
   [
    "p",
    "LIST n lists from line n to the end of the program. LIST n END m lists lines n through m."
   ]
  ],
  "examples": [
   "LIST",
   "LIST 100",
   "LIST 100 END 200"
  ],
  "note": None
 },
 "LOAD": {
  "title": "LOAD Command",
  "brief": "Load a program from a .bas file.",
  "syntax": "LOAD filename[,r]",
  "details": [
   [
    "p",
    "LOAD reads a BASIC program from the given file and replaces the program currently in memory. The file name may be enclosed in quotation marks."
   ],
   [
    "p",
    "The optional ,r keeps any data files open and runs the program immediately after loading it."
   ],
   [
    "p",
    "A LOAD replaces the program in memory: any temporary file left by an earlier COMPILE of an unsaved program is deleted (with its .exe), and the loaded file becomes the file a bare SAVE writes back to."
   ]
  ],
  "examples": [
   "LOAD HELLO.BAS",
   "LOAD \"A:MYPROG.BAS\""
  ],
  "note": "Edits after a LOAD do not touch the file on disk: COMPILE builds a temporary file until a SAVE commits the changes to the loaded name."
 },
 "NEW": {
  "title": "NEW Command",
  "brief": "Erase the program and all data.",
  "syntax": "NEW",
  "details": [
   [
    "p",
    "NEW clears the program, all variables, and all arrays, returning the interpreter to a fresh state."
   ],
   [
    "p",
    "NEW also forgets the current file: a later bare SAVE asks for a file name, and any temporary file left by an earlier COMPILE of an unsaved program is deleted (with its .exe)."
   ]
  ],
  "examples": [
   "NEW"
  ],
  "note": None
 },
 "RENUM": {
  "title": "RENUM Command",
  "brief": "Renumber program lines (RENUM [new],[old][,increment]).",
  "syntax": "RENUM [new number],[old number][,increment]",
  "details": [
   [
    "p",
    "RENUM renumbers program lines. new number is the first line number of the new sequence (default 10), old number is the line where renumbering begins (default: the first line), and increment is the step between new line numbers (default 10). Any field may be left empty, e.g. RENUM 300,,50."
   ],
   [
    "p",
    "Every line-number reference in the program is updated automatically so it still points at the same line: GOTO, GOSUB, ON ... GOTO/GOSUB, ON ERROR/KEY/TIMER GOTO, and IF ... THEN/ELSE line numbers. Numbers that are not line references (expressions, DATA items, file numbers, and text inside strings or REM comments) are left unchanged."
   ],
   [
    "p",
    "As in GW-BASIC, RENUM cannot reorder the lines or create a line number greater than 65529; an \"Illegal function call\" error results. It also cannot be used while a TYPE...END TYPE block is open."
   ]
  ],
  "examples": [
   "10 GOTO 30",
   "20 PRINT \"A\"",
   "30 PRINT \"B\"",
   "RENUM",
   "RENUM 300,,50",
   "RENUM 1000,900,20",
   "LIST"
  ],
  "note": None
 },
 "RUN": {
  "title": "RUN Command",
  "brief": "Run the program (optionally from a line: RUN n).",
  "syntax": "RUN [line number]",
  "details": [
   [
    "p",
    "RUN executes the program currently in memory, starting at the lowest line number (or at line n if given). All variables and arrays are re-initialized first."
   ],
   [
    "p",
    "While a program is running, press CTRL-C (Break) to stop it and return to the Ok prompt."
   ]
  ],
  "examples": [
   "RUN",
   "RUN 200"
  ],
  "note": None
 },
 "SAVE": {
  "title": "SAVE Command",
  "brief": "Save the program to a .bas file (or back to the file it was loaded from).",
  "syntax": "SAVE [filename]",
  "details": [
   [
    "p",
    "SAVE writes the program currently in memory to the given file, which can later be read back with LOAD. The file name may be enclosed in quotation marks."
   ],
   [
    "p",
    "The file name is optional. If you type SAVE with no file name, the program is saved back to the file it was last loaded or saved to; the interpreter tells you which file it is saving to. If there is no such file (a NEW program that was never saved), SAVE with no name asks for a file name."
   ],
   [
    "p",
    "When a previous COMPILE parked unsaved changes in a temporary file, SAVE commits them: the current program is written into the temporary file and the temporary file (and its .exe) is renamed onto the saved name, after deleting any existing file with that name. After any SAVE the state is exactly the state after a LOAD of the saved file."
   ],
   [
    "p",
    "No options are accepted after the file name: the plain-text .BAS format is always written (the .BAS extension is added if the file name has none)."
   ]
  ],
  "examples": [
   "LOAD BOUNCE.BAS\nREM ... edit the program ...\nSAVE\n(remembers BOUNCE.BAS and overwrites it)\nSAVE NEWNAME.BAS",
   "SAVE HELLO.BAS",
   "SAVE \"A:MYPROG.BAS\""
  ],
  "note": "A SAVE never saves stale code: the program currently in memory is always what is written. With no file name, SAVE targets the file last read by LOAD or last saved; with no such file it asks for a name."
 },
 "TOKEN": {
  "title": "TOKEN Command",
  "brief": "Show each line with its token form.",
  "syntax": "TOKEN",
  "details": [
   [
    "p",
    "TOKEN displays every line of the program together with the token form the interpreter stores, which is useful for debugging the tokenizer."
   ]
  ],
  "examples": [
   "TOKEN"
  ],
  "note": None
 }
}

GRAPHICS_TOPICS = {
  # Screen modes
  "SCREEN",
  "SCREENSIZE",
  "TEXTSIZE",
  "TEXTFONT",
  "TEXTROTATE",
  "WCLOSE",
  # Drawing primitives
  "LINE",
  "CIRCLE",
  "DRAW",
  "PAINT",
  "PSET",
  "PRESET",
  "INK",
  "CURSOR",
  # Colors
  "COLOR",
  "PALETTE",
  # Viewports and windows
  "VIEW",
  "WINDOW",
  # Graphics functions
  "POINT",
  "XSZ",
  "YSZ",
}

COMMAND_ALIASES = {
 "EXIT": "BYE",
 "QUIT": "BYE",
 # The instruction is spelled "DEF SEG" (two words); let users look it up
 # as one word too (manual DEFSEG Note: DEFSEG without a space is just a
 # variable name, so there is no keyword to alias in the parser itself).
 "DEFSEG": "DEF SEG",
 # The ON ERROR statement is documented inside the ON entry (manual
 # ONERROR); let users look it up by the statement name too.
 "ON ERROR": "ON",
 "ONERROR": "ON",
 # The ON KEY(n) statement is documented inside the ON entry (manual
 # ONCOMN); let users look it up by the statement name too.
 "ON KEY": "ON",
 "ONKEY": "ON",
 # The manual's PRINT# page is named PRINTF.html (the '#' cannot be used
 # in a file name); let users look up the entry that way too.
 "PRINTF": "PRINT#",
 # Same for INPUT# (manual page INPUTF.html).
 "INPUTF": "INPUT#",
 # The manual's function pages are named without the dollar sign; let
 # users look up the function entries by those names too.
 "CHRS": "CHR$",
 "LEFTS": "LEFT$",
 "MIDSF": "MID$",
 "MIDSS": "MID$",
 "RIGHTS": "RIGHT$",
 "STRS": "STR$",
 "STRIG": "STR$",
 "STRINGS": "STRING$",
 "SPACES": "SPACE$",
 "HEXS": "HEX$",
 "OCTS": "OCT$",
 "BINS": "BIN$",
 "INKEYS": "INKEY$",
 "INPUTS": "INPUT$",
 "VARPTRS": "VARPTR$",
 "LPRINT USING": "LPRINT",
 # XSIZE/YSIZE are the longer names for the XSZ/YSZ window-size functions.
 "XSIZE": "XSZ",
 "YSIZE": "YSZ"
}

HELP_FUNCTIONS = {
 "ABS": {
  "title": "ABS Function",
  "brief": "To return the absolute value of the expression n.",
  "syntax": "ABS(n)",
  "details": [
   [
    "p",
    "n must be a numeric expression."
   ]
  ],
  "examples": [
   "PRINT ABS(7*(-5))\n 35\nPrints 35 as the result of the action."
  ],
  "note": None
 },
 "ACOS": {
  "title": "ACOS Function",
  "brief": "To return the arccosine of x, expressed in radians.",
  "syntax": "ACOS(x)",
  "details": [
   [
    "p",
    "The result is within the range of 0 to pi/2."
   ],
   [
    "p",
    "x must be within the range of -1 to 1; values outside the range cause an \"Illegal function call\" error."
   ]
  ],
  "examples": [
   "10 PRINT ACOS(1)\n20 PRINT ACOS(0)\nRUN\n 0\n 1.570796"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "ASC": {
  "title": "ASC Function",
  "brief": "To return a numeric value that is the ASCII code for the first character of the string x$.",
  "syntax": "ASC(x$)",
  "details": [
   [
    "p",
    "If x$ is null, an Illegal Function Call error is returned."
   ],
   [
    "p",
    "If x$ begins with an uppercase letter, the value returned will be within the range of 65 to 90."
   ],
   [
    "p",
    "If x$ begins with a lowercase letter, the range is 97 to 122."
   ],
   [
    "p",
    "Numbers 0 to 9 return 48 to 57, sequentially."
   ],
   [
    "p",
    "See the CHR$ function for ASCII-to-string conversion."
   ],
   [
    "p",
    "See Appendix C in the GW-BASIC User's Guide for ASCII codes."
   ]
  ],
  "examples": [
   "10 X$=\"TEN\"\n20 PRINT ASC(X$)\nRUN\n 84\n84 is the ASCII code for the letter T."
  ],
  "note": None
 },
 "ASIN": {
  "title": "ASIN Function",
  "brief": "To return the arcsine of x, expressed in radians.",
  "syntax": "ASIN(x)",
  "details": [
   [
    "p",
    "The result is within the range of -pi/2 to pi/2."
   ],
   [
    "p",
    "x must be within the range of -1 to 1; values outside the range cause an \"Illegal function call\" error."
   ]
  ],
  "examples": [
   "10 PRINT ASIN(1)\nRUN\n 1.570796"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "ATN": {
  "title": "ATN Function",
  "brief": "To return the arctangent of x, when x is expressed in radians.",
  "syntax": "ATN(x)",
  "details": [
   [
    "p",
    "The result is within the range of -pi/2 to pi/2."
   ],
   [
    "p",
    "The expression x may be any numeric type. The evaluation of ATN is performed in single precision."
   ],
   [
    "p",
    "To convert from degrees to radians, multiply by pi/180."
   ]
  ],
  "examples": [
   "10 INPUT X\n20 PRINT ATN(X)\nRUN\n ? 3\n 1.249046\nPrints the arctangent of 3 radians (1.249046)."
  ],
  "note": None
 },
 "CDBL": {
  "title": "CDBL Function",
  "brief": "To convert x to a double-precision number.",
  "syntax": "CDBL(x)",
  "details": [
   [
    "p",
    "x must be a numeric expression."
   ],
   [
    "p",
    "See the CINT and CSNG functions for converting numbers to integer and single precision, respectively."
   ]
  ],
  "examples": [
   "10 A=454.67\n20 PRINT A; CDBL(A)\nRUN\n 454.67 454.6700134277344\nPrints a double-precision version of the single-precision value stored in the variable named A."
  ],
  "note": "GW-BASIC numbers are single precision in this interpreter; CDBL converts a value to a full double-precision floating-point number."
 },
 "CHR$": {
  "title": "CHR$ Function",
  "brief": "To convert an ASCII code to its equivalent character.",
  "syntax": "CHR$(n)",
  "details": [
   [
    "p",
    "n is a value from 0 to 255."
   ],
   [
    "p",
    "CHR$ is commonly used to send a special character to the terminal or printer. For example, you could send CHR$(7) to sound a beep through the speaker as a preface to an error message, or you could send a form feed, CHR$(12), to the printer."
   ],
   [
    "p",
    "See the ASC function for ASCII-to-numeric conversion."
   ],
   [
    "p",
    "ASCII codes are listed in Appendix C of the GW-BASIC User's Guide."
   ]
  ],
  "examples": [
   "PRINT CHR$(66);\n B\nThis prints the ASCII character code 66, which is the uppercase letter B.",
   "PRINT CHR$(13);\nThis command prints a carriage return."
  ],
  "note": None
 },
 "CINT": {
  "title": "CINT Function",
  "brief": "To round numbers with fractional portions to the next whole number or integer.",
  "syntax": "CINT(x)",
  "details": [
   [
    "p",
    "If x is not within the range of -32768 to 32767, an \"Overflow\" error occurs."
   ],
   [
    "p",
    "CINT rounds half away from zero: positive values are rounded up at .5, negative values are rounded down at .5."
   ],
   [
    "p",
    "See the FIX and INT functions, both of which return integers."
   ],
   [
    "p",
    "See the CDBL and CSNG functions for converting numbers to the double-precision and single-precision data types, respectively."
   ]
  ],
  "examples": [
   "PRINT CINT(45.67)\n 46\n45.67 is rounded up to 46."
  ],
  "note": None
 },
 "COS": {
  "title": "COS Function",
  "brief": "To return the cosine of the range of x.",
  "syntax": "COS(x)",
  "details": [
   [
    "p",
    "x must be in radians. COS is the trigonometric cosine function. To convert from degrees to radians, multiply by pi/180."
   ],
   [
    "p",
    "COS(x) is calculated in single precision."
   ]
  ],
  "examples": [
   "10 X=2*COS(.4)\n20 PRINT X\nRUN\n 1.842122",
   "10 PI=3.141593\n20 PRINT COS(PI)\n30 DEGREES=180\n40 RADIANS=DEGREES*PI/180\n50 PRINT COS(RADIANS)\nRUN\n -1\n -1"
  ],
  "note": None
 },
 "CSNG": {
  "title": "CSNG Function",
  "brief": "To convert x to a single-precision number.",
  "syntax": "CSNG(x)",
  "details": [
   [
    "p",
    "x must be a numeric expression (see the CINT and CDBL functions)."
   ]
  ],
  "examples": [
   "10 A#=975.3421222#\n20 PRINT A#; CSNG(A#)\nRUN\n 975.3421222 975.3421"
  ],
  "note": None
 },
 "CSRLIN": {
  "title": "CSRLIN Variable",
  "brief": "To return the current line (row) position of the cursor.",
  "syntax": "y = CSRLIN",
  "details": [
   [
    "p",
    "y is a numeric variable receiving the value returned. The value returned is within the range of 1 to 25."
   ],
   [
    "p",
    "The CSRLIN variable returns the vertical coordinate of the cursor on the active page (see the SCREEN statement)."
   ],
   [
    "p",
    "CSRLIN is used without parentheses."
   ]
  ],
  "examples": [
   "10 Y=CSRLIN\n20 LOCATE 24, 1\n30 PRINT \"HELLO\"\n40 LOCATE Y, 1\nRUN\nHELLO\nThe CSRLIN variable in line 10 records the current line."
  ],
  "note": None
 },
 "CVI": {
  "title": "CVI, CVS, CVD Functions",
  "brief": "To convert string values to numeric values.",
  "syntax": "CVI(2-byte string)",
  "details": [
   [
    "p",
    "Numeric values read in from a random-access disk file must be converted from strings back into numbers if they are to be arithmetically manipulated."
   ],
   [
    "p",
    "CVI converts a 2-byte string to an integer. MKI$ is its complement (see also the CVS and CVD functions)."
   ]
  ],
  "examples": [
  ],
  "note": "MKI$, MKS$, and MKD$ (the complementary conversions) are implemented; see the MKI$ function."
 },
 "CVS": {
  "title": "CVI, CVS, CVD Functions",
  "brief": "To convert string values to numeric values.",
  "syntax": "CVS(4-byte string)",
  "details": [
   [
    "p",
    "Numeric values read in from a random-access disk file must be converted from strings back into numbers if they are to be arithmetically manipulated."
   ],
   [
    "p",
    "CVS converts a 4-byte string to a single-precision number. MKS$ is its complement (see also the CVI and CVD functions)."
   ]
  ],
  "examples": [
   "70 FIELD #1, 4 AS N$, 12 AS B$...\n80 GET #1\n90 Y=CVS(N$)\nLine 80 reads a field from file #1 (the field read is defined in line 70), and converts the first four bytes (N$) into a single-precision number assigned to the variable Y."
  ],
  "note": "MKI$, MKS$, and MKD$ (the complementary conversions) are implemented; see the MKI$ function."
 },
 "CVD": {
  "title": "CVI, CVS, CVD Functions",
  "brief": "To convert string values to numeric values.",
  "syntax": "CVD(8-byte string)",
  "details": [
   [
    "p",
    "Numeric values read in from a random-access disk file must be converted from strings back into numbers if they are to be arithmetically manipulated."
   ],
   [
    "p",
    "CVD converts an 8-byte string to a double-precision number. MKD$ is its complement (see also the CVI and CVS functions)."
   ]
  ],
  "examples": [
  ],
  "note": "MKI$, MKS$, and MKD$ (the complementary conversions) are implemented; see the MKI$ function."
 },
 "MKI$": {
  "title": "MKI$ Function",
  "brief": "To convert an integer to a 2-byte string.",
  "syntax": "MKI$(integer expression)",
  "details": [
   [
    "p",
    "MKI$ converts an integer to a 2-byte string. The value is truncated to an integer and must be within the range of -32768 to 32767; otherwise an \"Overflow\" error results."
   ],
   [
    "p",
    "Any numeric value placed in a random file buffer with an LSET or an RSET statement must be converted to a string (see the CVI, CVS, and CVD functions for the complementary conversions). These functions differ from STR$ because they change the interpretations of the bytes, not the bytes themselves."
   ]
  ],
  "examples": [
   "10 A$=MKI$(123)\n20 PRINT LEN(A$), CVI(A$)\nRUN\n 2  123\nThe integer is converted to a 2-byte string and back to a number."
  ],
  "note": "See the MKS$ and MKD$ functions."
 },
 "MKS$": {
  "title": "MKS$ Function",
  "brief": "To convert a single-precision number to a 4-byte string.",
  "syntax": "MKS$(single-precision expression)",
  "details": [
   [
    "p",
    "MKS$ converts a single-precision number to a 4-byte string. It is the complement of the CVS function (see also the CVI and CVD functions)."
   ],
   [
    "p",
    "Any numeric value placed in a random file buffer with an LSET or an RSET statement must be converted to a string. These functions differ from STR$ because they change the interpretations of the bytes, not the bytes themselves."
   ]
  ],
  "examples": [
   "90 AMT=(K+T)\n100 FIELD #1, 8 AS D$, 20 AS N$\n110 LSET D$=MKS$(AMT)\n120 LSET N$=A$\n130 PUT #1"
  ],
  "note": "See the MKI$ and MKD$ functions."
 },
 "MKD$": {
  "title": "MKD$ Function",
  "brief": "To convert a double-precision number to an 8-byte string.",
  "syntax": "MKD$(double-precision expression)",
  "details": [
   [
    "p",
    "MKD$ converts a double-precision number to an 8-byte string. It is the complement of the CVD function (see also the CVI and CVS functions)."
   ],
   [
    "p",
    "Any numeric value placed in a random file buffer with an LSET or an RSET statement must be converted to a string. These functions differ from STR$ because they change the interpretations of the bytes, not the bytes themselves."
   ]
  ],
  "examples": [
   "PRINT LEN(MKD$(1.5)), CVD(MKD$(1.5))\n 8  1.5"
  ],
  "note": "See the MKI$ and MKS$ functions."
 },
 "DATE$": {
  "title": "DATE$ Variable",
  "brief": "To set or retrieve the current date.",
  "syntax": "v$ = DATE$\nDATE$ = v$",
  "details": [
   [
    "p",
    "v$ is a valid string literal or variable."
   ],
   [
    "p",
    "When DATE$ is the expression in a LET or PRINT statement, the current date is fetched and assigned to the string variable. The date is returned as a 10-character string in the form mm-dd-yyyy: mm is the month (01 to 12), dd is the day (01 to 31), and yyyy is the year (1980 to 2099)."
   ],
   [
    "p",
    "When DATE$ is the target of a string assignment, the current date is set. v$ may be in the form mm-dd-yy, mm/dd/yy, mm-dd-yyyy, or mm/dd/yyyy."
   ],
   [
    "p",
    "If v$ is not a valid string, a \"Type Mismatch\" error results. If any of the values are out of range or missing, an \"Illegal Function Call\" error is issued. In both cases any previous date is retained."
   ]
  ],
  "examples": [
   "10 V$=DATE$\n20 PRINT V$\nRUN\n 01-01-1985"
  ],
  "note": "In this interpreter the current date is initialized from the system clock when the interpreter starts and after each RUN."
 },
 "DAY": {
  "title": "DAY Function",
  "brief": "To return the day of the current date.",
  "syntax": "DAY",
  "details": [
   [
    "p",
    "DAY returns the day of the month (1 to 31) of the current date. DAY is used without parentheses: x = DAY."
   ],
   [
    "p",
    "See the MONTH, YEAR, HOUR, MINUTE, and SECOND functions, and the DATE$ variable."
   ]
  ],
  "examples": [
   "PRINT DAY"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "DIR$": {
  "title": "DIR$ Function",
  "brief": "To return a list of the file names in the current directory that match a pattern.",
  "syntax": "DIR$(pattern$)",
  "details": [
   [
    "p",
    "pattern$ is a file name pattern. A question mark (?) matches any single character and an asterisk (*) matches any number of characters, as in the FILES command."
   ],
   [
    "p",
    "The matching file names are returned as a single string with one name per line. If no files match, the null string is returned."
   ],
   [
    "p",
    "DIR$ lists the directory of the interpreter's current working directory."
   ]
  ],
  "examples": [
   "PRINT DIR$(\"*.BAS\")"
  ],
  "note": "The FILES command page in the manual describes the same pattern syntax; DIR$ is the function form implemented here."
 },
 "ENVIRON$": {
  "title": "ENVIRON$ Function",
  "brief": "To allow the user to retrieve the specified environment string from the environment table.",
  "syntax": "v$ = ENVIRON$(parmid)\nv$ = ENVIRON$(nthparm)",
  "details": [
   [
    "p",
    "parmid is a valid string expression containing the parameter to search for."
   ],
   [
    "p",
    "nthparm is an integer expression in the range of 1 to 255."
   ],
   [
    "p",
    "If a string argument is used, ENVIRON$ returns a string containing the text following parmid= from the environment string table. If parmid is not found, then a null string is returned."
   ],
   [
    "p",
    "If a numeric argument is used, ENVIRON$ returns a string containing the nth parameter from the environment string table. If there is no nth parameter, then a null string is returned."
   ],
   [
    "p",
    "The ENVIRON$ function distinguishes between upper- and lowercase."
   ],
   [
    "p",
    "See the ENVIRON statement to modify the environment string table."
   ]
  ],
  "examples": [
   "ENVIRON \"PATH=A:\\SALES; A:\\ACOUNTING; B:\\MKT:\"\nPRINT ENVIRON$(\"PATH\")\nA:\\SALES; A:\\ACCOUNTING; B:\\MKT",
   "PRINT ENVIRON$(1)\n' Prints the first string in the environment."
  ],
  "note": "In this interpreter the environment string table is initialized from the host operating system's environment."
 },
 "EXP": {
  "title": "EXP Function",
  "brief": "To return e (the base of natural logarithms) to the power of x.",
  "syntax": "EXP(x)",
  "details": [
   [
    "p",
    "x must be less than 88.02969."
   ],
   [
    "p",
    "EXP(x) is calculated in single precision."
   ]
  ],
  "examples": [
   "10 X = 5\n20 PRINT EXP(X-1)\nRUN\n 54.59815\nPrints the value of e to the 4th power."
  ],
  "note": "In this interpreter an \"Overflow\" error is raised when x is 88.02969 or greater, instead of returning machine infinity."
 },
 "FIX": {
  "title": "FIX Function",
  "brief": "To truncate x to a whole number.",
  "syntax": "FIX(x)",
  "details": [
   [
    "p",
    "FIX does not round off numbers, it simply eliminates the decimal point and all characters to the right of the decimal point."
   ],
   [
    "p",
    "FIX(x) is equivalent to SGN(x)*INT(ABS(x)). The major difference between FIX and INT is that FIX does not return the next lower number for negative x."
   ],
   [
    "p",
    "FIX is useful in modulus arithmetic."
   ]
  ],
  "examples": [
   "PRINT FIX(58.75)\n 58",
   "PRINT FIX(-58.75)\n -58"
  ],
  "note": None
 },
 "FRE": {
  "title": "FRE Function",
  "brief": "To return the number of available bytes in allocated string memory.",
  "syntax": "FRE(x$)\nFRE(x)",
  "details": [
   [
    "p",
    "Arguments (x$) and (x) are dummy arguments."
   ],
   [
    "p",
    "Before FRE returns the amount of space available in allocated string memory, GW-BASIC initiates a \"garbage collection\" activity. Data in string memory space is collected and reorganized, and unused portions of fragmented strings are discarded to make room for new input."
   ],
   [
    "p",
    "FRE(\"\") or any string forces a garbage collection before returning the number of free bytes. Therefore, using FRE(\"\") periodically will result in shorter delays for each garbage collection."
   ]
  ],
  "examples": [
  ],
  "note": "In this interpreter FRE may be used without an argument and returns a simulated constant value (60000); no garbage collection is performed."
 },
 "HEX$": {
  "title": "HEX$ Function",
  "brief": "To return a string which represents the hexadecimal value of the numeric argument.",
  "syntax": "v$ = HEX$(x)",
  "details": [
   [
    "p",
    "HEX$ converts decimal values within the range of -2147483648 to +4294967295 into a hexadecimal string expression within the range of 0 to FFFFFFFF."
   ],
   [
    "p",
    "Hexadecimal numbers are numbers to the base 16, rather than base 10 (decimal numbers)."
   ],
   [
    "p",
    "x is rounded to an integer before HEX$(x) is evaluated. See the OCT$ function for octal conversions."
   ],
   [
    "p",
    "If x is negative, 2's (binary) complement form is used."
   ]
  ],
  "examples": [
   "10 CLS: INPUT \"INPUT DECIMAL NUMBER\";X\n20 A$=HEX$(X)\n30 PRINT X \"DECIMAL IS \"A$\" HEXADECIMAL\"\nRUN\n INPUT DECIMAL NUMBER? 32\n 32 DECIMAL IS 20 HEXADECIMAL"
  ],
  "note": None
 },
 "BIN$": {
  "title": "BIN$ Function",
  "brief": "To return a string which represents the binary value of the numeric argument.",
  "syntax": "v$ = BIN$(x)",
  "details": [
   [
    "p",
    "BIN$ converts decimal values within the range of -2147483648 to +4294967295 into a binary string expression using 1 to 32 binary digits."
   ],
   [
    "p",
    "Binary numbers are numbers to the base 2, rather than base 10 (decimal numbers)."
   ],
   [
    "p",
    "x is rounded to an integer before BIN$(x) is evaluated. See the HEX$ function for hexadecimal conversion and the OCT$ function for octal conversion."
   ],
   [
    "p",
    "If x is negative, 2's (binary) complement form is used."
   ]
  ],
  "examples": [
   "10 CLS: INPUT \"INPUT DECIMAL NUMBER\";X\n20 A$=BIN$(X)\n30 PRINT X \"DECIMAL IS \"A$\" BINARY\"\nRUN\n INPUT DECIMAL NUMBER? 5\n 5 DECIMAL IS 101 BINARY"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "HOUR": {
  "title": "HOUR Function",
  "brief": "To return the hour of the current time.",
  "syntax": "HOUR",
  "details": [
   [
    "p",
    "HOUR returns the hour (0 to 23) of the current time. HOUR is used without parentheses: x = HOUR."
   ],
   [
    "p",
    "See the MINUTE, SECOND, DAY, MONTH, and YEAR functions, and the TIME$ variable."
   ]
  ],
  "examples": [
   "PRINT HOUR"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "MINUTE": {
  "title": "MINUTE Function",
  "brief": "To return the minute of the current time.",
  "syntax": "MINUTE",
  "details": [
   [
    "p",
    "MINUTE returns the minute (0 to 59) of the current time. MINUTE is used without parentheses: x = MINUTE."
   ],
   [
    "p",
    "See the HOUR, SECOND, DAY, MONTH, and YEAR functions, and the TIME$ variable."
   ]
  ],
  "examples": [
   "PRINT MINUTE"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "INKEY$": {
  "title": "INKEY$ Variable",
  "brief": "To return one character read from the keyboard.",
  "syntax": "v$ = INKEY$",
  "details": [
   [
    "p",
    "If no character is pending in the keyboard buffer, a null string (length zero) is returned."
   ],
   [
    "p",
    "If several characters are pending, only the first is returned. The string will be one or two characters in length."
   ],
   [
    "p",
    "Two character strings are used to return the extended codes described in Appendix C of the GW-BASIC User's Guide. The first character of a two character code is zero."
   ],
   [
    "p",
    "No characters are displayed on the screen. INKEY$ is used without parentheses and scans the keyboard only once, so place INKEY$ statements within loops to provide adequate response times for the operator."
   ]
  ],
  "examples": [
   "1010 RESPONSE$=\"\"\n1020 FOR N%=1 TO 1000\n1030 A$=INKEY$: IF LEN(A$)=0 THEN 1060\n1040 IF ASC(A$)=13 THEN RETURN\n1050 RESPONSE$=RESPONSE$+A$\n1060 NEXT N%\nA timed-input subroutine: INKEY$ is polled in a loop until the RETURN key is pressed."
  ],
  "note": "In this interpreter INKEY$ reads from the console's keyboard buffer; characters typed are not echoed to the screen."
 },
 "INPUT$": {
  "title": "INPUT$ Function",
  "brief": "To return a string of x characters read from the keyboard, or from file number.",
  "syntax": "INPUT$(x[,[#]file number])",
  "details": [
   [
    "p",
    "If the keyboard is used for input, no characters will appear on the screen. All control characters (except CTRL-BREAK) are passed through."
   ],
   [
    "p",
    "The INPUT$ function is preferred over INPUT and LINE INPUT statements for reading communications files, because all ASCII characters may be significant in communications. INPUT is the least desirable because input stops when a comma or carriage return is seen. LINE INPUT terminates when a carriage return is seen."
   ],
   [
    "p",
    "INPUT$ allows all characters read to be assigned to a string. INPUT$ will return x characters from the file number or keyboard."
   ]
  ],
  "examples": [
   "10 OPEN \"I\", 1, \"DATA\"\n20 IF EOF(1) THEN 50\n30 PRINT HEX$(ASC(INPUT$(1, #1)));\n40 GOTO 20\n50 PRINT\n60 END\nThis example lists the contents of a sequential file in hexadecimal.",
   "100 PRINT \"TYPE P TO PROCEED OR S TO STOP\"\n110 X$=INPUT$(1)\n120 IF X$=\"P\" THEN 500\n130 IF X$=\"S\" THEN 700 ELSE 100"
  ],
  "note": None
 },
 "INSTR": {
  "title": "INSTR Function",
  "brief": "To search for the first occurrence of string y$ in x$, and return the position it's found.",
  "syntax": "INSTR([n,]x$,y$)",
  "details": [
   [
    "p",
    "Optional offset n sets the position for starting the search. The default value for n is 1. If n equals zero, the error message \"Illegal argument in line number\" is returned. n must be within the range of 1 to 255. If n is out of this range, an \"Illegal Function Call\" error is returned."
   ],
   [
    "p",
    "INSTR returns 0 if:"
   ],
   [
    "pre",
    "n > LEN(x$)\nx$ is null\ny$ cannot be found"
   ],
   [
    "p",
    "If y$ is null, INSTR returns n. x$ and y$ may be string variables, string expressions, or string literals."
   ]
  ],
  "examples": [
   "10 X$=\"ABCDEBXYZ\"\n20 Y$=\"B\"\n30 PRINT INSTR(X$, Y$); INSTR(4, X$, Y$)\nRUN\n 2 6\nThe interpreter searches the string \"ABCDEBXYZ\" and finds the first occurrence of the character B at position 2 in the string. It then starts another search at position 4 (D) and finds the second match at position 6 (B). The last three characters are ignored, since all conditions set out in line 30 were satisfied."
  ],
  "note": None
 },
 "INT": {
  "title": "INT Function",
  "brief": "To truncate an expression to a whole number.",
  "syntax": "INT(x)",
  "details": [
   [
    "p",
    "Negative numbers return the next lowest number."
   ],
   [
    "p",
    "The FIX and CINT functions also return integer values."
   ]
  ],
  "examples": [
   "PRINT INT(98.89)\n 98",
   "PRINT INT(-12.11)\n -13"
  ],
  "note": None
 },
 "LCASE$": {
  "title": "LCASE$ Function",
  "brief": "To convert the characters in x$ to lowercase.",
  "syntax": "LCASE$(x$)",
  "details": [
   [
    "p",
    "LCASE$ converts all uppercase letters in x$ to their lowercase equivalents; all other characters are unchanged."
   ]
  ],
  "examples": [
   "PRINT LCASE$(\"Hello, World\")\n hello, world"
  ],
  "note": "Extension: not covered in the manual folder. See the UCASE$ function for the opposite conversion."
 },
 "LEFT$": {
  "title": "LEFT$ Function",
  "brief": "To return a string that comprises the left-most n characters of x$.",
  "syntax": "LEFT$(x$,n)",
  "details": [
   [
    "p",
    "n must be within the range of 0 to 255. If n is greater than LEN(x$), the entire string (x$) will be returned. If n equals zero, the null string (length zero) is returned (see the MID$ and RIGHT$ substring functions)."
   ]
  ],
  "examples": [
   "10 A$=\"BASIC\"\n20 B$=LEFT$(A$, 3)\n30 PRINT B$\nRUN\n BAS\nThe left-most three letters of the string \"BASIC\" are printed on the screen."
  ],
  "note": None
 },
 "LEN": {
  "title": "LEN Function",
  "brief": "To return the number of characters in x$.",
  "syntax": "LEN(x$)",
  "details": [
   [
    "p",
    "x$ is any string expression."
   ],
   [
    "p",
    "Nonprinting characters and blanks are counted."
   ]
  ],
  "examples": [
   "10 X$=\"PORTLAND, OREGON\"\n20 PRINT LEN(X$)\nRUN\n 16\nNote that the comma and space are included in the character count of 16."
  ],
  "note": "In this interpreter LEN also accepts a numeric expression; it returns the length of the string representation of the number."
 },
 "EOF": {
  "title": "EOF Function",
  "brief": "To return -1 (true) when the end of a sequential or a communications file has been reached or 0 otherwise.",
  "syntax": "v=EOF(file number)",
  "details": [
   [
    "p",
    "If a GET is done past the end of the file, EOF returns -1. This may be used to find the size of a file using a binary search or other algorithm. With communications files, a -1 indicates that the buffer is empty."
   ],
   [
    "p",
    "Use EOF to test for end of file while inputting to avoid \"Input Past End\" errors."
   ]
  ],
  "examples": [
   "10 OPEN \"I\", 1, \"DATA\"\n20 C=0\n30 IF EOF(1) THEN 100\n40 INPUT #1, M(C)\n50 C=C+1: GOTO 30\n100 END\nThe file named DATA is read into the M array until the end of the file is reached, then the program branches to line 100."
  ],
  "note": None
 },
 "LOC": {
  "title": "LOC Function",
  "brief": "To return the current position in the file.",
  "syntax": "LOC(file number)",
  "details": [
   [
    "p",
    "file number is the file number used when the file was opened."
   ],
   [
    "p",
    "With random disk files, LOC returns the record number just read from, or written to, with a GET or PUT statement."
   ],
   [
    "p",
    "With sequential files, LOC returns the number of 128-byte blocks read from, or written to, the file since it was opened. When the sequential file is opened for input, GW-BASIC initially reads the first sector of the file; in this case the LOC function returns the character 1 before any input is allowed."
   ],
   [
    "p",
    "If the file was opened but no disk input/output was performed, LOC returns a zero."
   ]
  ],
  "examples": [
   "200 IF LOC(1)>50 THEN STOP\nThe program stops after 51 records are read or written."
  ],
  "note": None
 },
 "LOF": {
  "title": "LOF Function",
  "brief": "To return the length (number of bytes) allocated to the file.",
  "syntax": "LOF(file number)",
  "details": [
   [
    "p",
    "file number is the number of the file that the file was opened under."
   ]
  ],
  "examples": [
   "10 OPEN \"R\",1,\"FILE.BIG\"\n20 GET #1,LOF(1)/128\nThis sequence gets the last record of the random-access file file.big, and assumes that the file was created with a default record length of 128 bytes."
  ],
  "note": None
 },
 "LOG": {
  "title": "LOG Function",
  "brief": "To return the natural logarithm of x.",
  "syntax": "LOG(x)",
  "details": [
   [
    "p",
    "x must be a number greater than zero."
   ],
   [
    "p",
    "LOG(x) is calculated in single precision."
   ]
  ],
  "examples": [
   "PRINT LOG(2)\n .6931471",
   "PRINT LOG(1)\n 0"
  ],
  "note": None
 },
 "MID$": {
  "title": "MID$ Function",
  "brief": "To return a string of m characters from x$ beginning with the nth character.",
  "syntax": "MID$(x$,n[,m])",
  "details": [
   [
    "p",
    "n must be within the range of 1 to 255."
   ],
   [
    "p",
    "m must be within the range of 0 to 255."
   ],
   [
    "p",
    "If m is omitted, or if there are fewer than m characters to the right of n, all rightmost characters beginning with n are returned."
   ],
   [
    "p",
    "If n > LEN(x$), MID$ function returns a null string."
   ],
   [
    "p",
    "If m equals 0, the MID$ function returns a null string."
   ],
   [
    "p",
    "If either n or m is out of range, an \"Illegal function call\" error is returned."
   ],
   [
    "p",
    "For more information and examples, see the LEFT$ and RIGHT$ functions."
   ]
  ],
  "examples": [
   "10 A$=\"GOOD\"\n20 B$=\"MORNING EVENING AFTERNOON\"\n30 PRINT A$; MID$(B$, 8, 8)\nRUN\n GOOD EVENING\nLine 30 concatenates (joins) the A$ string to another string with a length of eight characters, beginning at position 8 within the B$ string."
  ],
  "note": None
 },
 "MONTH": {
  "title": "MONTH Function",
  "brief": "To return the month of the current date.",
  "syntax": "MONTH",
  "details": [
   [
    "p",
    "MONTH returns the month (1 to 12) of the current date. MONTH is used without parentheses: x = MONTH."
   ],
   [
    "p",
    "See the DAY, YEAR, HOUR, MINUTE, and SECOND functions, and the DATE$ variable."
   ]
  ],
  "examples": [
   "PRINT MONTH"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "OCT$": {
  "title": "OCT$ Function",
  "brief": "To convert a decimal value to an octal value.",
  "syntax": "OCT$(x)",
  "details": [
   [
    "p",
    "x is rounded to an integer before OCT$(x) is evaluated."
   ],
   [
    "p",
    "This statement converts a decimal value within the range of -2147483648 to +4294967295 to an octal string expression."
   ],
   [
    "p",
    "Octal numbers are numbers to the base 8 rather than base 10 (decimal numbers)."
   ],
   [
    "p",
    "See the HEX$ function for hexadecimal conversion."
   ]
  ],
  "examples": [
   "10 PRINT OCT$(18)\nRUN\n 22\nDecimal 18 equals octal 22."
  ],
  "note": None
 },
 "PEEK": {
  "title": "PEEK Function",
  "brief": "To read from a specified memory location.",
  "syntax": "PEEK(a)",
  "details": [
   [
    "p",
    "Returns the byte (decimal integer within the range of 0 to 255) read from the specified memory location a. a must be within the range of 0 to 65535; values outside the range cause an \"Illegal function call\" error."
   ],
   [
    "p",
    "The DEF SEG statement last executed determines the segment (absolute address) that will be peeked into."
   ],
   [
    "p",
    "PEEK is the complementary function to the POKE statement."
   ]
  ],
  "examples": [
   "10 A=PEEK(&H5A00)\nThe value of the byte stored in hex offset memory location 5A00 (23040 decimal) will be stored in the variable A."
  ],
  "note": "In this interpreter the poked/peeked memory is simulated: it starts zero-filled and is lost when the interpreter exits."
 },
 "POINT": {
  "title": "POINT Function",
  "brief": "To read the color or attribute value of a pixel from the screen.",
  "syntax": "POINT(x,y)\nPOINT(n)",
  "details": [
   [
    "p",
    "In the first syntax, x and y are the coordinates of the point to be examined. POINT returns the color of the pixel at that point; if the point given is out of range (or no graphics screen is active) the value -1 is returned. See the COLOR and PALETTE statements for valid color and attribute values."
   ],
   [
    "p",
    "POINT with one argument allows you to retrieve the current graphics coordinates (the last point referenced by a graphics statement such as PSET, LINE, or CIRCLE): n = 0 returns the current physical x coordinate, n = 1 the current physical y coordinate, n = 2 the current logical x coordinate if a VIEW rectangle is active (otherwise the physical x coordinate as in 0), and n = 3 the current logical y coordinate if a VIEW rectangle is active (otherwise the physical y coordinate as in 1). An n outside the range of 0 to 3 is an \"Illegal function call\" error."
   ]
  ],
  "examples": [
   "10 SCREEN 1\n20 FOR C=0 TO 3\n30 PSET (10, 10),C\n40 IF POINT(10, 10)<>C THEN PRINT \"BROKEN BASIC=\"\n50 NEXT C",
   "10 SCREEN 2\n20 IF POINT(I, I)<>0 THEN PRESET(I, I) ELSE PSET(I, I)\nLine 20 inverts the current state of the point."
  ],
  "note": None
 },
 "POS": {
  "title": "POS Function",
  "brief": "To return the current cursor position.",
  "syntax": "POS(c)",
  "details": [
   [
    "p",
    "The leftmost position is 1."
   ],
   [
    "p",
    "c is a dummy argument."
   ],
   [
    "p",
    "POS(c) returns the column location of the cursor, 1 to 40 or 1 to 80 depending on the current screen width."
   ]
  ],
  "examples": [
   "10 CLS\n20 A$=INKEY$:IF A$=\"\"THEN GOTO 20 ELSE PRINT A$;\n30 IF POS(X)>10 THEN PRINT CHR$(13);\n40 GOTO 20\nCauses a carriage return after the 10th character is printed on each line of the screen."
  ],
  "note": None
 },
 "PEER": {
  "title": "PEER Function",
  "brief": "To read a 16-bit word from a specified simulated memory location.",
  "syntax": "PEER(a)",
  "details": [
   [
    "p",
    "Returns the signed 16-bit word (range -32768 to 32767) read from the simulated memory locations a and a+1, with the byte at a as the low order byte (little-endian, as on the 8086), and the segment determined by the last DEF SEG statement. a must be within the range of 0 to 65535; values outside the range cause an \"Illegal function call\" error. PEEK is the byte-sized counterpart (0 to 255)."
   ]
  ],
  "examples": [
   "10 X = 65536\n20 P = VARPTR(X)\n30 PRINT PEER(P + 2)\nRUN\n 18304\nX is stored as the little-endian bytes 00 00 80 47, so the word at P+2 is 47 80 hex = 18304 decimal."
  ],
  "note": "Extension: PEER is not part of standard GW-BASIC and is not covered in the manual folder."
 },
 "RIGHT$": {
  "title": "RIGHT$ Function",
  "brief": "To return the rightmost n characters of string x$.",
  "syntax": "RIGHT$(x$,n)",
  "details": [
   [
    "p",
    "If n is equal to or greater than LEN(x$), RIGHT$ returns x$. If n equals zero, the null string (length zero) is returned (see the MID$ and LEFT$ functions)."
   ]
  ],
  "examples": [
   "10 A$=\"DISK BASIC\"\n20 PRINT RIGHT$(A$, 5)\nRUN\n BASIC\nPrints the rightmost five characters in the A$ string."
  ],
  "note": None
 },
 "RND": {
  "title": "RND Function",
  "brief": "To return a random number between 0 and 1.",
  "syntax": "RND[(x)]",
  "details": [
   [
    "p",
    "The same sequence of random numbers is generated each time the program is run unless the random number generator is reseeded (see the RANDOMIZE statement). If x is equal to zero, then the last number is repeated."
   ],
   [
    "p",
    "If x is greater than 0, or if x is omitted, the next random number in the sequence is generated."
   ],
   [
    "p",
    "To get a random number within the range of zero through n, use the following formula:"
   ],
   [
    "pre",
    "INT(RND*(n+1))"
   ],
   [
    "p",
    "The random number generator may be seeded by using a negative value for x."
   ]
  ],
  "examples": [
   "10 FOR I=1 TO 5\n20 PRINT INT(RND*101);\n30 NEXT\nRUN\n 53 30 31 51 5\nGenerates five pseudo-random numbers within the range of 0-100."
  ],
  "note": "In this interpreter RND(-1) re-seeds the generator with the system timer."
 },
 "RGB": {
  "title": "RGB Function",
  "brief": "To create a full-precision color (any red/green/blue value) for graphics.",
  "syntax": "RGB(r,g,b)",
  "details": [
   [
    "p",
    "r, g and b are numeric expressions, each within 0-255, giving the red, green and blue components of the color. A component outside the range causes an \"Illegal function call\" error, and a string argument is a \"Type mismatch\" error."
   ],
   [
    "p",
    "RGB returns the COLOR VALUE of the exact color: the first call to a given (r,g,b) allocates the next free dynamic color (index 16, then 17, 18, ...), and every later call with the same arguments returns the same index. Colors 0-15 remain the fixed CGA/VGA palette and are unaffected."
   ],
   [
    "p",
    "Because the result is an ordinary color value, it works wherever a color is expected in a graphics mode: PSET/PRESET, LINE, CIRCLE, PAINT (paint, border and bckgrnd attributes), PUT, the DRAW C and P commands, and the COLOR and INK statements. For example: LINE (0,0)-(99,99),RGB(255,0,0) BF, or COLOR RGB(200,16,24)."
   ],
   [
    "p",
    "Any number of distinct colors may coexist on screen (the old 16-color limit applies only to the fixed palette). POINT returns the index stored in the pixel - a 16+ value for a dynamic color - and the display maps the index back to the real RGB color."
   ],
   [
    "p",
    "RGB() colors are available in graphics modes only (SCREENSIZE, SCREEN 1, 7-10). Text-mode (SCREEN 0) colors keep their classic attribute values (fg 0-31, bg 0-7)."
   ]
  ],
  "examples": [
   "10 SCREENSIZE 400,300\n20 C=RGB(200, 16, 24)\n30 LINE (20,20)-(380,280),C BF\n40 CIRCLE (200, 150), 100, RGB(255, 230, 0)\n50 PRINT POINT(200, 150)\nRUN\n 17\nDraws a dark-red filled box with a golden circle; POINT reports the circle color's dynamic index."
  ],
  "note": "Extension: RGB is not part of standard GW-BASIC, whose hardware palettes are limited to 16 colors. This interpreter stores dynamic colors as palette indexes (16+) so POINT and GET stay fast."
 },
 "ROUND": {
  "title": "ROUND Function",
  "brief": "To round x to the nearest whole number.",
  "syntax": "ROUND(x)",
  "details": [
   [
    "p",
    "Values exactly halfway between two integers are rounded away from zero, the same rule CINT uses: ROUND(2.5) = 3 and ROUND(-2.5) = -3."
   ]
  ],
  "examples": [
   "PRINT ROUND(4.5)\n 5\nPRINT ROUND(5.5)\n 6"
  ],
  "note": "Extension: not covered in the manual folder. See the ROUNDDOWN, ROUNDFRAC, and ROUNDUP functions."
 },
 "ROUNDDOWN": {
  "title": "ROUNDDOWN Function",
  "brief": "To return the largest integer less than or equal to x.",
  "syntax": "ROUNDDOWN(x)",
  "details": [
   [
    "p",
    "ROUNDDOWN rounds toward negative infinity; for negative values it returns the next lower integer."
   ]
  ],
  "examples": [
   "PRINT ROUNDDOWN(4.9)\n 4\nPRINT ROUNDDOWN(-4.1)\n -5"
  ],
  "note": "Extension: not covered in the manual folder."
 },
 "ROUNDFRAC": {
  "title": "ROUNDFRAC Function",
  "brief": "To remove the fractional part of x without rounding.",
  "syntax": "ROUNDFRAC(x)",
  "details": [
   [
    "p",
    "ROUNDFRAC truncates toward zero, like the FIX function."
   ]
  ],
  "examples": [
   "PRINT ROUNDFRAC(4.9)\n 4\nPRINT ROUNDFRAC(-4.9)\n -4"
  ],
  "note": "Extension: not covered in the manual folder."
 },
 "ROUNDUP": {
  "title": "ROUNDUP Function",
  "brief": "To return the smallest integer greater than or equal to x.",
  "syntax": "ROUNDUP(x)",
  "details": [
   [
    "p",
    "ROUNDUP rounds toward positive infinity; for negative values it returns the next higher integer."
   ]
  ],
  "examples": [
   "PRINT ROUNDUP(4.1)\n 5\nPRINT ROUNDUP(-4.9)\n -4"
  ],
  "note": "Extension: not covered in the manual folder."
 },
 "SGN": {
  "title": "SGN Function",
  "brief": "To return the sign of x.",
  "syntax": "SGN(x)",
  "details": [
   [
    "p",
    "x is any numeric expression."
   ],
   [
    "p",
    "If x is positive, SGN(x) returns 1."
   ],
   [
    "p",
    "If x is 0, SGN(x) returns 0."
   ],
   [
    "p",
    "If x is negative, SGN(x) returns -1."
   ]
  ],
  "examples": [
   "10 INPUT \"Enter value\", x\n20 ON SGN(X)+2 GOTO 100, 200, 300\nGW-BASIC branches to 100 if X is negative, 200 if X is 0, and 300 if X is positive."
  ],
  "note": None
 },
 "SECOND": {
  "title": "SECOND Function",
  "brief": "To return the second of the current time.",
  "syntax": "SECOND",
  "details": [
   [
    "p",
    "SECOND returns the second (0 to 59) of the current time. SECOND is used without parentheses: x = SECOND."
   ],
   [
    "p",
    "See the HOUR, MINUTE, DAY, MONTH, and YEAR functions, and the TIME$ variable."
   ]
  ],
  "examples": [
   "PRINT SECOND"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 },
 "SIN": {
  "title": "SIN Function",
  "brief": "To calculate the trigonometric sine of x, in radians.",
  "syntax": "SIN(x)",
  "details": [
   [
    "p",
    "SIN(x) is calculated in single-precision."
   ],
   [
    "p",
    "To obtain SIN(x) when x is in degrees, use SIN(x*pi/180)."
   ]
  ],
  "examples": [
   "PRINT SIN(1.5)\n .9974951\nThe sine of 1.5 radians is .9974951 (single-precision)."
  ],
  "note": None
 },
 "SPC": {
  "title": "SPC Function",
  "brief": "To skip a specified number of spaces in a PRINT or an LPRINT statement.",
  "syntax": "SPC(n)",
  "details": [
   [
    "p",
    "n must be within the range of 0 to 255."
   ],
   [
    "p",
    "If n is greater than the defined width of the printer or the screen, the value used will be n MOD width."
   ],
   [
    "p",
    "A semicolon is assumed to follow the SPC(n) function."
   ],
   [
    "p",
    "SPC may only be used with PRINT, LPRINT and PRINT# statements (see the SPACE$ function)."
   ]
  ],
  "examples": [
   "PRINT \"OVER\" SPC(15) \"THERE\"\nOVER               THERE"
  ],
  "note": None
 },
 "SPACE$": {
  "title": "SPACE$ Function",
  "brief": "To return a string of x spaces.",
  "syntax": "SPACE$(x)",
  "details": [
   [
    "p",
    "x is rounded to an integer and must be within the range of 0 to 255 (see the SPC function)."
   ]
  ],
  "examples": [
   "10 FOR N=1 TO 5\n20 X$=SPACE$(N)\n30 PRINT X$; N\n40 NEXT N\nRUN\n 1\n  2\n   3\n    4\n     5\nLine 20 adds one space for each loop execution."
  ],
  "note": None
 },
 "SQR": {
  "title": "SQR Function",
  "brief": "Returns the square root of x.",
  "syntax": "SQR(x)",
  "details": [
   [
    "p",
    "x must be greater than or equal to 0."
   ],
   [
    "p",
    "SQR(x) is computed in single-precision."
   ]
  ],
  "examples": [
   "10 FOR X=10 TO 25 STEP 5\n20 PRINT X; SQR(X)\n30 NEXT\nRUN\n 10 3.162278\n 15 3.872984\n 20 4.472136\n 25 5"
  ],
  "note": None
 },
 "STR$": {
  "title": "STR$ Function",
  "brief": "To return a string representation of the value of x.",
  "syntax": "STR$(x)",
  "details": [
   [
    "p",
    "STR$(x) is the complementary function to VAL(x$) (see the VAL function)."
   ],
   [
    "p",
    "The returned string is right-justified: a leading space precedes positive values and a minus sign precedes negative values."
   ]
  ],
  "examples": [
   "5 REM ARITHMETIC FOR KIDS\n10 INPUT \"TYPE A NUMBER\"; N\n20 ON LEN(STR$(N)) GOSUB 30, 40, 50\nThis program branches to various subroutines, depending on the number of characters typed before the RETURN key is pressed."
  ],
  "note": None
 },
 "STRING$": {
  "title": "STRING$ Function",
  "brief": "To return a string of n copies of a character.",
  "syntax": "STRING$(n,j)\nSTRING$(n,x$)",
  "details": [
   [
    "p",
    "STRING$(n,j) returns a string of length n whose characters all have ASCII code j."
   ],
   [
    "p",
    "STRING$(n,x$) returns a string of length n consisting of the first character of x$."
   ],
   [
    "p",
    "n and j are integer expressions in the range 0 to 255."
   ],
   [
    "p",
    "STRING$ is also useful for printing top and bottom borders on the screen or the printer."
   ],
   [
    "p",
    "Appendix C in the GW-BASIC User's Guide lists ASCII character codes."
   ]
  ],
  "examples": [
   "10 X$ = STRING$(10, 45)\n20 PRINT X$ \"MONTHLY REPORT\" X$\nRUN\n----------MONTHLY REPORT----------\n45 is the decimal equivalent of the ASCII symbol for the minus (-) sign."
  ],
  "note": None
 },
 "TAB": {
  "title": "TAB Function",
  "brief": "Spaces to position n on the screen.",
  "syntax": "TAB(n)",
  "details": [
   [
    "p",
    "If the current print position is already beyond space n, TAB goes to that position on the next line."
   ],
   [
    "p",
    "Space 1 is the leftmost position. The rightmost position is the screen width."
   ],
   [
    "p",
    "n must be within the range of 1 to 255."
   ],
   [
    "p",
    "If the TAB function is at the end of a list of data items, GW-BASIC will not return the cursor to the next line. It is as though the TAB function has an implied semicolon after it."
   ],
   [
    "p",
    "TAB may be used only in PRINT, LPRINT, or PRINT# statements (see the SPC function)."
   ]
  ],
  "examples": [
   "10 PRINT \"NAME\" TAB(25) \"AMOUNT\": PRINT\n20 READ A$,B$\n30 PRINT A$ TAB(25) B$\n40 DATA \"G. T. JONES\",\"$25.00\"\nRUN\n NAME                AMOUNT\n G. T. JONES     $25.00"
  ],
  "note": None
 },
 "TAN": {
  "title": "TAN Function",
  "brief": "To calculate the trigonometric tangent of x, in radians.",
  "syntax": "TAN(x)",
  "details": [
   [
    "p",
    "TAN(x) is calculated in single-precision."
   ],
   [
    "p",
    "To obtain TAN(x) when x is in degrees, use TAN(x*pi/180)."
   ],
   [
    "p",
    "If TAN overflows, the \"Overflow\" error message is displayed."
   ]
  ],
  "examples": [
   "10 Y = TAN(X)\nWhen executed, Y will contain the value of the tangent of X radians."
  ],
  "note": None
 },
 "TIME$": {
  "title": "TIME$ Variable",
  "brief": "To set or retrieve the current time.",
  "syntax": "v$ = TIME$\nTIME$ = v$",
  "details": [
   [
    "p",
    "When TIME$ is used in an expression, it returns the current time as a string in the form hh:mm:ss (24-hour clock)."
   ],
   [
    "p",
    "When TIME$ is the target of a string assignment, the current time is set. v$ must contain a valid hh:mm:ss value (or hh, or hh:mm); seconds default to 0."
   ],
   [
    "p",
    "If the value is not a valid time string, an \"Illegal Function Call\" error is issued and the previous time is retained."
   ]
  ],
  "examples": [
   "PRINT TIME$\nTIME$ = \"12:34:56\"\nPRINT TIME$"
  ],
  "note": "In this interpreter the current time is initialized from the system clock when the interpreter starts and after each RUN."
 },
 "TIMER": {
  "title": "TIMER Function",
  "brief": "To return single-precision floating-point numbers of the elapsed number of seconds since midnigh.",
  "syntax": "v = TIMER",
  "details": [
   [
    "p",
    "Fractions of seconds are calculated to the nearest degree possible. TIMER is read-only and is used without parentheses."
   ]
  ],
  "examples": [
   "PRINT TIMER"
  ],
  "note": None
 },
 "XSZ": {
  "title": "XSZ Function",
  "brief": "To return the current graphics window width in pixels.",
  "syntax": "v = XSZ()",
  "details": [
  [
   "p",
   "XSZ() returns the width, in pixels, of the current graphics drawing surface. XSIZE() is a longer name for the same function.",
  ],
  [
   "p",
   "The drawing surface is the area your graphics statements can draw into. It is set to the size you pass to SCREEN or SCREENSIZE, and it follows the window when you resize the window: drag the window larger and the drawing surface grows to fill it (the newly exposed area is the background color); drag it smaller and the excess is cropped.",
  ],
  [
   "p",
   "Use XSZ() to find out the current window size, for example to reposition or re-draw a figure after the user resizes the window. It returns 0 in text mode (there is no pixel surface).",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 W = XSZ()\n30 PRINT \"WINDOW IS\"; W; \"PIXELS WIDE\""
  ],
  "note": "The longer name XSIZE() works identically. The size changes live when the window is resized."
},
 "YSZ": {
  "title": "YSZ Function",
  "brief": "To return the current graphics window height in pixels.",
  "syntax": "v = YSZ()",
  "details": [
  [
   "p",
   "YSZ() returns the height, in pixels, of the current graphics drawing surface. YSIZE() is a longer name for the same function.",
  ],
  [
   "p",
   "Like XSZ(), the drawing surface follows the window when you resize it, so YSZ() reports the new height. Use YSZ() together with XSZ() to reposition or re-draw a figure after the user resizes the window. It returns 0 in text mode.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 W = XSZ(): H = YSZ()\n30 PRINT \"WINDOW IS\"; W; \"X\"; H\n40 CIRCLE (W/2,H/2),20"
  ],
  "note": "The longer name YSIZE() works identically. The size changes live when the window is resized."
},
 "TRIM$": {
  "title": "TRIM$ Function",
  "brief": "To remove leading and trailing spaces from x$.",
  "syntax": "TRIM$(x$)",
  "details": [
   [
    "p",
    "TRIM$ removes all leading and trailing space characters from x$; interior spaces are unchanged."
   ]
  ],
  "examples": [
   "PRINT TRIM$(\"  HELLO  \") + \"?\"\n HELLO?"
  ],
  "note": "Extension: not covered in the manual folder."
 },
 "UCASE$": {
  "title": "UCASE$ Function",
  "brief": "To convert the characters in x$ to uppercase.",
  "syntax": "UCASE$(x$)",
  "details": [
   [
    "p",
    "UCASE$ converts all lowercase letters in x$ to their uppercase equivalents; all other characters are unchanged."
   ]
  ],
  "examples": [
   "PRINT UCASE$(\"hello, world\")\n HELLO, WORLD"
  ],
  "note": "Extension: not covered in the manual folder. See the LCASE$ function for the opposite conversion."
 },
 "VAL": {
  "title": "VAL Function",
  "brief": "Returns the numerical value of string x$.",
  "syntax": "VAL(x$)",
  "details": [
   [
    "p",
    "The VAL function also strips leading blanks, tabs, and line feeds from the argument string. For example, the following line returns -3: VAL(\" -3\")"
   ],
   [
    "p",
    "The STR$ function (for numeric to string conversion) is the complement to the VAL(x$) function."
   ],
   [
    "p",
    "If the first character of x$ is not numeric, the VAL(x$) will return zero."
   ]
  ],
  "examples": [
   "10 READ NAME$, CITY$, STATE$, ZIP$\n20 IF VAL(ZIP$)<90000 OR VAL(ZIP$)>96699 THEN PRINT NAME$ TAB(25) \"OUT OF STATE\"\n30 IF VAL(ZIP$)>=90801 AND VAL(ZIP$)<=90815 THEN PRINT NAME$ TAB(25) \"LONG BEACH\""
  ],
  "note": None
 },
 "VARPTR": {
  "title": "VARPTR Function",
  "brief": "To return the address in memory of the variable or file control block (FCB).",
  "syntax": "VARPTR(variable name)\nVARPTR(#file number)",
  "details": [
   [
    "p",
    "VARPTR is usually used to obtain the address of a variable or array so it can be passed to an assembly language subroutine."
   ],
   [
    "p",
    "VARPTR(#file number) returns the starting address of the File Control Block assigned to file number. The file must be open, otherwise a \"Bad file number (52)\" error results."
   ],
   [
    "p",
    "VARPTR(variable name) returns the address of the first byte of data identified with the variable name. A value must have been assigned to the variable before VARPTR is executed; otherwise an \"Illegal function call\" error results."
   ],
   [
    "p",
    "All simple variables should be assigned before calling VARPTR for an array, because the addresses of the arrays change whenever a new simple variable is assigned."
   ]
  ],
  "examples": [
   "A = 123\nPRINT VARPTR(A)\n' A must have a value assigned before VARPTR runs"
  ],
  "note": "In this interpreter VARPTR addresses refer to simulated memory (the same memory used by PEEK and POKE), not real MS-DOS addresses."
 },
 "VARPTR$": {
  "title": "VARPTR$ Function",
  "brief": "To return a character form of the offset of a variable in memory.",
  "syntax": "VARPTR$(variable)",
  "details": [
   [
    "p",
    "variable is the name of a variable that exists in the program."
   ],
   [
    "p",
    "Assign all simple variables before calling VARPTR$ for an array element, because the array addresses change when a new simple variable is assigned."
   ],
   [
    "p",
    "VARPTR$ returns a three-byte string of the following form: | Byte 0 | Byte 1 | Byte 2 |. Byte 0 contains one of the following variable types: 2 integer, 3 string, 4 single-precision, 8 double precision. Byte 1 contains the 8086 address format, and is the least significant byte. Byte 2 contains the 8086 address format, and is the most significant byte."
   ]
  ],
  "examples": [
   "100 X = USR(VARPTR$(Y))"
  ],
  "note": "In this interpreter VARPTR$ addresses refer to simulated memory (the same memory used by PEEK and POKE), not real MS-DOS addresses."
 },
 "YEAR": {
  "title": "YEAR Function",
  "brief": "To return the year of the current date.",
  "syntax": "YEAR",
  "details": [
   [
    "p",
    "YEAR returns the year of the current date. YEAR is used without parentheses: x = YEAR."
   ],
   [
    "p",
    "See the MONTH, DAY, HOUR, MINUTE, and SECOND functions, and the DATE$ variable."
   ]
  ],
  "examples": [
   "PRINT YEAR"
  ],
  "note": "Not covered in the manual folder; behavior matches this interpreter."
 }
}


HELP_INSTRUCTIONS = {
 "PRINT": {
  "title": "PRINT Statement",
  "brief": "To output a display to the screen.",
  "syntax": "PRINT [list of expressions][;]\n?[list of expressions][;]",
  "details": [
   [
    "p",
    "If list of expressions is omitted, a blank line is displayed."
   ],
   [
    "p",
    "If list of expressions is included, the values of the expressions are displayed. Expressions in the list may be numeric and/or string expressions, separated by commas, spaces, or semicolons. String constants in the list must be enclosed in double quotation marks."
   ],
   [
    "p",
    "For more information about strings, see the STRING$ function."
   ],
   [
    "p",
    "A question mark (?) may be used in place of the word PRINT when using the GW-BASIC program editor."
   ],
   [
    "h",
    "Print Positions"
   ],
   [
    "p",
    "GW-BASIC divides the line into print zones of 14 spaces. The position of each item printed is determined by the punctuation used to separate the items in the list:"
   ],
   [
    "table",
    "Separator     Print Position\n,             Beginning of next zone\n;             Immediately after last value\nspace(s)      Immediately after last value"
   ],
   [
    "p",
    "If a comma, semicolon, or SPC or TAB function ends an expression list, the next PRINT statement begins printing on the same line, accordingly spaced. If the expression list ends without a comma, semicolon, or SPC or TAB function, a carriage return is placed at the end of the lines (GW-BASIC places the cursor at the beginning of the next line)."
   ],
   [
    "p",
    "A carriage return/line feed is automatically inserted after printing width characters, where width is 40 or 80. This results in two lines being skipped when you print exactly 40 (or 80) characters, unless the PRINT statement ends in a semicolon."
   ],
   [
    "p",
    "When numbers are printed on the screen, the numbers are always followed by a space. Positive number are preceded by a space. Negative numbers are preceded by a minus (-) sign. Single-precision numbers are represented with seven or fewer digits in a fixed-point or integer format."
   ],
   [
    "p",
    "See the LPRINT and LPRINT USING statements for information on sending data to be printed on a printer."
   ]
  ],
  "examples": [
   "10 X$= STRING$(10,45)\n20 PRINT X$\"MONTHLY REPORT\" X$\nRUN\n----------MONTHLY REPORT----------\n45 is the decimal equivalent of the ASCII symbol for the minus (-) sign."
  ],
  "note": None
 },
 "PRINT#": {
  "title": "PRINT# and PRINT# USING Statements",
  "brief": "To write data to a sequential disk file.",
  "syntax": "PRINT #file number ,[ USING string expressions ;] list of expressions",
  "details": [
   [
    "p",
    "file number is the number used when the file was opened for output."
   ],
   [
    "p",
    "string expressions consists of the formatting characters described in the PRINT USING statement."
   ],
   [
    "p",
    "list of expressions consists of the numeric and/or string expressions to be written to the file."
   ],
   [
    "p",
    "Double quotation marks are used as delimiters for numeric and/or string expressions. The first double quotation mark opens the line for input; the second double quotation mark closes it."
   ],
   [
    "p",
    "If numeric or string expressions are to be printed as they are input, they must be surrounded by double quotation marks. If the double quotation marks are omitted, the value assigned to the numeric or string expression is printed. If no value has been assigned, 0 is assumed. The double quotation marks do not appear on the screen."
   ],
   [
    "p",
    "If double quotation marks are required within a string, use CHR$(34) (the ASCII character for double quotation mark)."
   ],
   [
    "p",
    "If the strings contain commas, semicolons, or significant leading blanks, surround them with double quotation marks."
   ],
   [
    "p",
    "The comma after file number is a syntax separator; it does not advance the print position, so the first item of the list is written at the start of the line. Print zones of 14 spaces are created only by commas inside list of expressions, and the extra blanks they insert are also written to the diskette (commas have no effect, however, if used with the exponential format)."
   ],
   [
    "p",
    "The PRINT# statement may also be used with the USING option to control the format of the disk file."
   ],
   [
    "p",
    "In list of expressions, numeric expressions must be delimited by semicolons."
   ],
   [
    "p",
    "String expressions must be separated by semicolons in the list. To format the string expressions correctly on the diskette, use explicit delimiters in list of expressions."
   ],
   [
    "p",
    "PRINT# does not compress data on the diskette. An image of the data is written to the diskette, just as it would be displayed on the terminal screen with a PRINT statement. For this reason, be sure to delimit the data on the diskette so that it is input correctly from the diskette."
   ]
  ],
  "examples": [
   "10 PRINT #1, A\n 0\n(A is unassigned, so 0 is written)",
   "10 A=26\n20 PRINT #1, A\n 26",
   "10 A=26\n20 PRINT #1, \"A\"\n A",
   "100 PRINT #1,\"He said,\"Hello\", I think\"\nHe said, 0, I think",
   "100 PRINT #1, \"He said, \"CHR$(34) \"Hello,\"CHR$(34) \" I think.\"\nHe said, \"Hello,\" I think",
   "PRINT #1, USING\"$$###.##.\"; J; K; L",
   "10 A$=\"CAMERA\": B$=\"93604-1\"\n20 PRINT #1, A$; B$\nCAMERA93604-1",
   "30 PRINT #1, A$; \",\"; B$\nCAMERA, 93604-1"
  ],
  "note": None
 },
 "INPUT": {
  "title": "INPUT Statement",
  "brief": "To prepare the program for input from the terminal during program execution.",
  "syntax": "INPUT[;][prompt string;] list of variables\n INPUT[;][prompt string,] list of variables",
  "details": [
   [
    "p",
    "prompt string is a request for data to be supplied during program execution."
   ],
   [
    "p",
    "list of variables contains the variable(s) that stores the data in the prompt string."
   ],
   [
    "p",
    "Each data item in the prompt string must be surrounded by double quotation marks, followed by a semicolon or comma and the name of the variable to which it will be assigned. If more than one variable is given, data items must be separated by commas."
   ],
   [
    "p",
    "The data entered is assigned to the variable list. The number of data items supplied must be the same as the number of variables in the list."
   ],
   [
    "p",
    "The variable names in the list may be numeric or string variable names (including subscripted variables). The type of each data item input must agree with the type specified by the variable name."
   ],
   [
    "p",
    "Too many or too few data items, or the wrong type of values (for example, numeric instead of string), causes the message \"?Redo from start\" to be printed. No assignment of input values is made until an acceptable response is given."
   ],
   [
    "p",
    "A comma may be used instead of a semicolon after prompt string to suppress the question mark. For example, the following line prints the prompt with no question mark:"
   ],
   [
    "pre",
    "INPUT \"ENTER BIRTHDATE\",B$"
   ],
   [
    "p",
    "If the prompt string is preceded by a semicolon, the RETURN key pressed by the operator is suppressed. During program execution, data on that line is displayed, and data from the next PRINT statement is added to the line."
   ],
   [
    "p",
    "When an INPUT statement is encountered during program execution, the program halts, the prompt string is displayed, and the operator types in the requested data. Strings that input to an INPUT statement need not be surrounded by quotation marks unless they contain commas or leading or trailing blanks."
   ],
   [
    "p",
    "When the operator presses the RETURN key, program execution continues."
   ],
   [
    "p",
    "INPUT and LINE INPUT statements have built-in PRINT statements. When an INPUT statement with a quoted string is encountered during program execution, the quoted string is printed automatically (see the PRINT statement)."
   ],
   [
    "p",
    "The principal difference between the INPUT and LINE INPUT statements is that LINE INPUT accepts special characters (such as commas) within a string, without requiring double quotation marks, while the INPUT statement requires double quotation marks."
   ]
  ],
  "examples": [
   "10 INPUT X\n20 PRINT X \"SQUARED IS\" X^2\n30 END\nRUN\n ?",
   " 5 SQUARED IS 25",
   "10 PI=3.14\n20 INPUT \"WHAT IS THE RADIUS\"; R\n30 A=PI*R^2\n40 PRINT \"THE AREA OF THE CIRCLE IS\"; A\n50 PRINT\n60 GOTO 20\nRUN\n WHAT IS THE RADIUS? 7.4\n THE AREA OF THE CIRCLE IS 171.9464"
  ],
  "note": None
 },
 "INPUT#": {
  "title": "INPUT# Statement",
  "brief": "To read data items from a sequential file and assign them to program variables.",
  "syntax": "INPUT #file number, variable list",
  "details": [
   [
    "p",
    "file number is the number used when the file was opened for input."
   ],
   [
    "p",
    "variable list contains the variable names to be assigned to the items in the file."
   ],
   [
    "p",
    "The data items in the file appear just as they would if data were being typed on the keyboard in response to an INPUT statement."
   ],
   [
    "p",
    "The variable type must match the type specified by the variable name."
   ],
   [
    "p",
    "With INPUT#, no question mark is printed, as it is with INPUT."
   ],
   [
    "h",
    "Numeric Values"
   ],
   [
    "p",
    "For numeric values, leading spaces and line feeds are ignored. The first character encountered (not a space or line feed) is assumed to be the start of a number. The number terminates on a space, carriage return, line feed, or comma."
   ],
   [
    "h",
    "Strings"
   ],
   [
    "p",
    "If GW-BASIC is scanning the sequential data file for a string, leading spaces and line feeds are ignored."
   ],
   [
    "p",
    "If the first character is a double quotation mark (\"), the string will consist of all characters read between the first double quotation mark and the second. A quoted string may not contain a double quotation mark as a character. The second double quotation mark always terminates the string."
   ],
   [
    "p",
    "If the first character of the string is not a double quotation mark, the string terminates on a comma, carriage return, line feed, or after 255 characters have been read."
   ],
   [
    "p",
    "If end of the file is reached when a numeric or string item is being INPUT, the item is terminated."
   ],
   [
    "p",
    "INPUT# can also be used with random files."
   ]
  ],
  "examples": [],
  "note": None
 },
 "LET": {
  "title": "LET Statement",
  "brief": "To assign the value of an expression to a variable.",
  "syntax": "[LET] variable=expression",
  "details": [
   [
    "p",
    "The word LET is optional; that is, the equal sign is sufficient when assigning an expression to a variable name."
   ],
   [
    "p",
    "The LET statement is seldom used. It is included here to ensure compatibility with previous versions of BASIC that require it."
   ],
   [
    "p",
    "When using LET, remember that the type of the variable and the type of the expression must match. If they don't, a \"Type mismatch\" error occurs."
   ]
  ],
  "examples": [
   "110 LET D=12\n120 LET E=12^2\n130 LET F=12^4\n140 LET SUM=D+E+F\n.\n.\n.",
   "110 D=12\n120 E=12^2\n130 F=12^4\n140 SUM=D+E+F\n.\n.\n."
  ],
  "note": None
 },
 "IF": {
  "title": "IF ... THEN ... ELSE Statement",
  "brief": "To make a decision regarding program flow based on the result returned by an expression.",
  "syntax": "IF expression[,] THEN statement(s)[,][ELSE statement(s)]\n IF expression[,] GOTO line number[[,] ELSE statement(s)]",
  "details": [
   [
    "p",
    "If the result of expression is nonzero (logical true), the THEN or GOTO line number is executed."
   ],
   [
    "p",
    "If the result of expression is zero (false), the THEN or GOTO line number is ignored and the ELSE line number, if present, is executed. Otherwise, execution continues with the next executable statement. A comma is allowed before THEN and ELSE."
   ],
   [
    "p",
    "THEN and ELSE may be followed by either a line number for branching, or one or more statements to be executed."
   ],
   [
    "p",
    "GOTO is always followed by a line number."
   ],
   [
    "p",
    "If the statement does not contain the same number of ELSE's and THEN's line number, each ELSE is matched with the closest unmatched THEN. For example:"
   ],
   [
    "pre",
    "IF A=B THEN IF B=C THEN PRINT \"A=C\" ELSE PRINT \"A < > C\""
   ],
   [
    "p",
    "will not print \"A < > C\" when A < > B."
   ],
   [
    "p",
    "If an IF...THEN statement is followed by a line number in the direct mode, an \"Undefined line number\" error results, unless a statement with the specified line number was previously entered in the indirect mode."
   ],
   [
    "p",
    "Because IF ..THEN...ELSE is all one statement, the ELSE clause cannot be on a separate line. It must be all on one line."
   ]
  ],
  "examples": [
   "200 IF N THEN GET #1, N",
   "100 IF(N<20) and (N>10) THEN DB=1979-1: GOTO 300\n110 PRINT \"OUT OF RANGE\"",
   "210 IF IOFLAG THEN PRINT A$ ELSE LPRINT A$"
  ],
  "note": None
 },
 "GOTO": {
  "title": "GOTO Statement",
  "brief": "To branch unconditionally out of the normal program sequence to a specified line number.",
  "syntax": "GOTO line number",
  "details": [
   [
    "p",
    "line number is any valid line number within the program."
   ],
   [
    "p",
    "If line number is an executable statement, that statement and those following are executed. If it is a non-executable statement, execution proceeds at the first executable statement encountered after line number."
   ]
  ],
  "examples": [
   "10 READ R\n20 PRINT \"R =\"; R;\n30 A = 3.14*R^2\n40 PRINT \"AREA =\"; A\n50 GOTO 10\n60 DATA 5, 7, 12\nRUN\n R = 5 AREA = 78.5\n R = 7 AREA = 153.86\n R = 12 AREA = 452.16\n Out of data in 10"
  ],
  "note": None
 },
 "GOSUB": {
  "title": "GOSUB Statement",
  "brief": "To branch to, and return from, a subroutine.",
  "syntax": "GOSUB line number\n.\n.\n.\nRETURN [line number]",
  "details": [
   [
    "p",
    "line number is the first line number of the subroutine."
   ],
   [
    "p",
    "A subroutine may be called any number of times in a program, and a subroutine may be called from within another subroutine. Such nesting of subroutines is limited only by available memory."
   ],
   [
    "p",
    "A RETURN statement in a subroutine causes GW-BASIC to return to the statement following the most recent GOSUB statement. A subroutine can contain more than one RETURN statement, should logic dictate a RETURN at different points in the subroutine."
   ],
   [
    "p",
    "Subroutines can appear anywhere in the program, but must be readily distinguishable from the main program."
   ],
   [
    "p",
    "To prevent inadvertent entry, precede the subroutine by a STOP, END, or GOTO statement to direct program control around the subroutine."
   ]
  ],
  "examples": [
   "10 GOSUB 40\n20 PRINT \"BACK FROM SUBROUTINE\"\n30 END\n40 PRINT \"SUBROUTINE\";\n50 PRINT \" IN\";\n60 PRINT \" PROGRESS\"\n70 RETURN\nRUN\n SUBROUTINE IN PROGRESS\n BACK FROM SUBROUTINE"
  ],
  "note": None
 },
 "RETURN": {
  "title": "RETURN Statement",
  "brief": "To return from a subroutine.",
  "syntax": "RETURN [line number]",
  "details": [
   [
    "p",
    "The RETURN statement causes GW-BASIC to branch back to the statement following the most recent GOSUB statement. A subroutine may contain more than one RETURN statement to return from different points in the subroutine. Subroutines may appear anywhere in the program."
   ],
   [
    "p",
    "RETURN line number is primarily intended for use with event trapping. It sends the event-trapping routine back into the GW-BASIC program at a fixed line number while still eliminating the GOSUB entry that the trap created."
   ],
   [
    "p",
    "When a trap is made for a particular event, the trap automatically causes a STOP on that event so that recursive traps can never take place. The RETURN from the trap routine automatically does an ON unless an explicit OFF has been performed inside the trap routine."
   ],
   [
    "p",
    "The non-local RETURN must be used with care. Any GOSUB, WHILE, or FOR statement active at the time of the trap remains active."
   ]
  ],
  "examples": [],
  "note": None
 },
 "RESUME": {
  "title": "RESUME Statement",
  "brief": "To continue program execution after an error-recovery procedure has been performed.",
  "syntax": "RESUME\nRESUME 0\nRESUME NEXT\nRESUME line number",
  "details": [
   [
    "p",
    "Any one of the four formats shown above may be used, depending upon where execution is to resume:"
   ],
   [
    "table",
    "Syntax | Result\nRESUME or RESUME 0 | Execution resumes at the statement that caused an error.\nRESUME NEXT | Execution resumes at the statement immediately following the one that caused an error.\nRESUME line number | Execution resumes at the specified line number."
   ],
   [
    "p",
    "A RESUME statement that is not in an error trapping routine causes a \"RESUME without error\" message to be printed."
   ]
  ],
  "examples": [
   "10 ON ERROR GOTO 900\n.\n.\n.\n900 IF (ERR=230) AND (ERL=90) THEN PRINT \"TRY AGAIN\": RESUME 80\n.\n.\n."
  ],
  "note": None
 },
 "REM": {
  "title": "REM Statement",
  "brief": "To allow explanatory remarks to be inserted in a program.",
  "syntax": "REM[comment]\n'[comment]",
  "details": [
   [
    "p",
    "REM statements are not executed, but are output exactly as entered when the program is listed."
   ],
   [
    "p",
    "Once a REM or its abbreviation, an apostrophe ('), is encountered, the program ignores everything else until the next line number or program end is encountered."
   ],
   [
    "p",
    "REM statements may be branched into from a GOTO or GOSUB statement, and execution continues with the first executable statement after the REM statement. However, the program runs faster if the branch is made to the first statement."
   ],
   [
    "p",
    "Remarks may be added to the end of a line by preceding the remark with an apostrophe (') instead of REM."
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "Do not use REM in a DATA statement because it will be considered to be legal data."
   ]
  ],
  "examples": [
   ".\n.\n.\n120 REM CALCULATE AVERAGE VELOCITY\n130 FOR I=1 TO 20\n440 SUM=SUM+V(I)\n450 NEXT I\n.\n.\n.",
   ".\n.\n.\n129 FOR I=1 TO 20 'CALCULATED AVERAGE VELOCITY\n130 SUM=SUM+V(I)\n140 NEXT I\n.\n.\n."
  ],
  "note": None
 },
 "DATA": {
  "title": "DATA Statement",
  "brief": "To store the numeric and string constants that are accessed by the program READ statement(s).",
  "syntax": "DATA constants",
  "details": [
   [
    "p",
    "constants are numeric constants in any format (fixed point, floating-point, or integer), separated by commas. No expressions are allowed in the list."
   ],
   [
    "p",
    "String constants in DATA statements must be surrounded by double quotation marks only if they contain commas, colons, or significant leading or trailing spaces. Otherwise, quotation marks are not needed."
   ],
   [
    "p",
    "DATA statements are not executable and may be placed anywhere in the program. A DATA statement can contain as many constants that will fit on a line (separated by commas), and any number of DATA statements may be used in a program."
   ],
   [
    "p",
    "READ statements access the DATA statements in order (by line number). The data contained therein may be thought of as one continuous list of items, regardless of how many items are on a line or where the lines are placed in the program. The variable type (numeric or string) given in the READ statement must agree with the corresponding constant in the DATA statement, or a \"Type Mismatch\" error occurs."
   ],
   [
    "p",
    "DATA statements may be reread from the beginning by use of the RESTORE statement."
   ],
   [
    "p",
    "For further information and examples, see the RESTORE statement and the READ statement."
   ],
   [
    "p",
    "Example 1:"
   ],
   [
    "pre",
    ".\n.\n.\n80 FOR I=1 TO 10\n90 READ A(I)\n100 NEXT I\n110 DATA 3.08,5.19,3.12,3.98,4.24\n120 DATA 5.08,5.55,4.00,3.16,3.37\n.\n.\n."
   ],
   [
    "p",
    "This program segment reads the values from the DATA statements into array A. After execution, the value of A(1) is 3.08, and so on. The DATA statements (lines 110-120) may be placed anywhere in the program; they may even be placed ahead of the READ statement."
   ],
   [
    "p",
    "Example 2:"
   ],
   [
    "pre",
    "5 PRINT\n10 PRINT \"CITY\",\"STATE\",\"ZIP\"\n20 READ C$,S$,Z\n30 DATA \"DENVER,\",\"COLORADO\",80211\n40 PRINT C$,S$,Z\nRUN\n CITY STATE ZIP\n DENVER, COLORADO 80211"
   ],
   [
    "p",
    "This program reads string and numeric data from the DATA statement in line 30."
   ]
  ],
  "examples": [],
  "note": None
 },
 "READ": {
  "title": "READ Statement",
  "brief": "To read values from a DATA statement and assign them to variables.",
  "syntax": "READ list of variables",
  "details": [
   [
    "p",
    "A READ statement must always be used with a DATA statement."
   ],
   [
    "p",
    "READ statements assign variables to DATA statement values on a one-to-one basis."
   ],
   [
    "p",
    "READ statement variables may be numeric or string, and the values read must agree with the variable types specified. If they do not agree, a \"Syntax error\" results."
   ],
   [
    "p",
    "A single READ statement may access one or more DATA statements. They are accessed in order. Several READ statements may access the same DATA statement."
   ],
   [
    "p",
    "If the number of variables in list of variables exceeds the number of elements in the DATA statement(s), an \"Out of data\" message is printed."
   ],
   [
    "p",
    "If the number of variables specified is fewer than the number of elements in the DATA statement(s), subsequent READ statements begin reading data at the first unread element. If there are no subsequent READ statements, the extra data is ignored."
   ],
   [
    "p",
    "To reread DATA statements from the start, use the RESTORE statement."
   ]
  ],
  "examples": [
   ".\n.\n.\n80 FOR I=1 TO 10\n90 READ A(I)\n100 NEXT I\n110 DATA 3.08, 5.19, 3.12, 3.98, 4.24\n120 DATA 5.08, 5.55, 4.00, 3.16, 3.37\n.\n.\n.",
   "5 PRINT\n10 PRINT \"CITY\", \"STATE\", \"ZIP\"\n20 READ C$, S$, Z\n30 DATA \"DENVER,\", \"COLORADO\", 80211\n40 PRINT C$, S$, Z\nRUN\n CITY STATE ZIP\n DENVER, COLORADO 80211"
  ],
  "note": None
 },
 "RESTORE": {
  "title": "RESTORE Statement",
  "brief": "To allow DATA statements to be reread from a specified line.",
  "syntax": "RESTORE[line number]",
  "details": [
   [
    "p",
    "If line number is specified, the next READ statement accesses the first item in the specified DATA statement."
   ],
   [
    "p",
    "If line number is omitted, the next READ statement accesses the first item in the first DATA statement."
   ]
  ],
  "examples": [
   "10 READ A, B, C,\n20 RESTORE 30\n30 READ D, E, F\n40 DATA 57, 68, 79\n.\n.\n."
  ],
  "note": "Assigns the value 57 to both A and D variables, 68 to B and E, and so on."
 },
 "END": {
  "title": "END Statement",
  "brief": "To terminate program execution, close all files, and return to command level.",
  "syntax": "END",
  "details": [
   [
    "p",
    "END statements may be placed anywhere in the program to terminate execution."
   ],
   [
    "p",
    "Unlike the STOP statement, END does not cause a \"Break in line xxxx\" message to be printed."
   ],
   [
    "p",
    "An END statement at the end of a program is optional. GW-BASIC always returns to command level after an END is executed."
   ],
   [
    "p",
    "END closes all files."
   ]
  ],
  "examples": [
   "520 IF K>1000 THEN END ELSE GOTO 20"
  ],
  "note": None
 },
 "STOP": {
  "title": "STOP Statement",
  "brief": "To terminate program execution and return to command level.",
  "syntax": "STOP",
  "details": [
   [
    "p",
    "STOP statements may be used anywhere in a program to terminate execution. When a STOP is encountered, the following message is printed:"
   ],
   [
    "pre",
    "Break in line nnnnn"
   ],
   [
    "p",
    "Unlike the END statement, the STOP statement does not close files."
   ],
   [
    "p",
    "GW-BASIC always returns to command level after a STOP is executed. Execution is resumed by issuing a CONT command."
   ]
  ],
  "examples": [
   "10 INPUT A, B, C\n20 K=A^2*5.3: L=B^3/.26\n30 STOP\n40 M=C*K+100: PRINT M\nRUN\n ? 1, 2, 3\nBREAK IN 30\nPRINT L\n 30.76923\nCONT\n 115.9"
  ],
  "note": None
 },
 "DIM": {
  "title": "DIM Statement",
  "brief": "To specify the maximum values for array variable subscripts and allocate storage accordingly.",
  "syntax": "DIM variable(subscripts)[,variable(subscripts)]...",
  "details": [
   [
    "p",
    "If an array variable name is used without a DIM statement, the maximum value of its subscript(s) is assumed to be 10. If a subscript greater than the maximum specified is used, a \"Subscript out of range\" error occurs."
   ],
   [
    "p",
    "The maximum number of dimensions for an array is 255."
   ],
   [
    "p",
    "The minimum value for a subscript is always 0, unless otherwise specified with the OPTION BASE statement."
   ],
   [
    "p",
    "An array, once dimensioned, cannot be re-dimensioned within the program without first executing a CLEAR or ERASE statement."
   ],
   [
    "p",
    "The DIM statement sets all the elements of the specified arrays to an initial value of zero."
   ]
  ],
  "examples": [
   "10 DIM A(20)\n20 FOR I=0 TO 20\n30 READ A(I)\n40 NEXT I"
  ],
  "note": None
 },
 "ERASE": {
  "title": "ERASE Statement",
  "brief": "To eliminate arrays from a program.",
  "syntax": "ERASE list of array variables",
  "details": [
   [
    "p",
    "Arrays may be re-dimensioned after they are erased, or the memory space previously allocated to the array may be used for other purposes."
   ],
   [
    "p",
    "If an attempt is made to re-dimension an array without first erasing it, an error occurs."
   ]
  ],
  "examples": [
   "200 DIM B (250)\n.\n.\n.\n450 ERASE A, B\n460 DIM B(3, 4)"
  ],
  "note": None
 },
 "SWAP": {
  "title": "SWAP Statement",
  "brief": "To exchange the values of two variables.",
  "syntax": "SWAP variable1,variable2",
  "details": [
   [
    "p",
    "Any type variable may be swapped (integer, single-precision, double-precision, string), but the two variables must be of the same type or a \"Type mismatch\" error results."
   ]
  ],
  "examples": [
   "LIST\n10 A$=\"ONE \": B$=\"ALL \": C$=\"FOR \"\n20 PRINT A$ C$ B$\n30 SWAP A$, B$\n40 PRINT A$ C$ B$\nRUN\n ONE FOR ALL\n ALL FOR ONE"
  ],
  "note": None
 },
 "DEF": {
  "title": "DEF FN Statement",
  "brief": "To define and name a function written by the user.",
  "syntax": "DEF FNname[arguments] expression",
  "details": [
   [
    "p",
    "name must be a legal variable name. This name, preceded by FN, becomes the name of the function."
   ],
   [
    "p",
    "arguments consists of those variable names in the function definition that are to be replaced when the function is called. The items in the list are separated by commas."
   ],
   [
    "p",
    "expression is an expression that performs the operation of the function. It is limited to one statement."
   ],
   [
    "p",
    "In the DEF FN statement, arguments serve only to define the function; they do not affect program variables that have the same name. A variable name used in a function definition may or may not appear in the argument. If it does, the value of the parameter is supplied when the function is called. Otherwise, the current value of the variable is used."
   ],
   [
    "p",
    "The variables in the argument represent, on a one-to-one basis, the argument variables or values that are to be given in the function call."
   ],
   [
    "p",
    "User-defined functions may be numeric or string. If a type is specified in the function name, the value of the expression is forced to that type before it is returned to the calling statement. If a type is specified in the function name and the argument type does not match, a \"Type Mismatch\" error occurs."
   ],
   [
    "p",
    "A user-defined function may be defined more than once in a program by repeating the DEF FN statement."
   ],
   [
    "p",
    "A DEF FN statement must be executed before the function it defines may be called. If a function is called before it has been defined, an \"Undefined User Function\" error occurs."
   ],
   [
    "p",
    "DEF FN is illegal in the direct mode."
   ],
   [
    "p",
    "Recursive functions are not supported in the DEF FN statement."
   ]
  ],
  "examples": [
   ".\n.\n.\n400 R=1: S=2\n410 DEF FNAB(X, Y)=X^3/Y^2\n420 T=FNAB(R, S)\n.\n.\n."
  ],
  "note": None
 },
 "DEF SEG": {
  "title": "DEF SEG Statement",
  "brief": "To assign the current segment address referenced by a subsequent BLOAD, BSAVE, CALL, PEEK, POKE, or USR.",
  "syntax": "DEF SEG [=address]",
  "details": [
   [
    "p",
    "address is a numeric expression within the range of 0 to 65535."
   ],
   [
    "p",
    "The address specified is saved for use as the segment required by BLOAD, BSAVE, PEEK, POKE, and CALL statements."
   ],
   [
    "p",
    "Entry of any value outside the address range (0-65535) results in an \"Illegal Function Call\" error, and the previous value is retained."
   ],
   [
    "p",
    "If the address option is omitted, the segment to be used is set to GW-BASIC's data segment (DS). This is the initial default value."
   ],
   [
    "p",
    "If you specify the address option, base it on a 16-byte boundary."
   ],
   [
    "p",
    "Segment addresses are shifted 4 bits to the left; so to get the segment address, divide the memory location by 16."
   ],
   [
    "p",
    "For BLOAD, BSAVE, PEEK, POKE, or CALL statements, the value is shifted left four bits (this is done by the microprocessor, not by GW-BASIC) to form the code segment address for the subsequent call instruction (see the BLOAD, BSAVE, CALL, PEEK, and POKE statements)."
   ],
   [
    "p",
    "GW-BASIC does not perform additional checking to assure that the resultant segment address is valid."
   ]
  ],
  "examples": [
   "10 DEF SEG=&HB800",
   "20 DEF SEG"
  ],
  "note": "Example 1 sets the segment to the screen buffer; example 2 restores the segment to BASIC DS. DEF and SEG must be separated by a space. Otherwise, GW-BASIC will interpret the statement DEFSEG=100 to mean, \"assign the value 100 to the variable DEFSEG.\""
 },
 "CLS": {
  "title": "CLS Statement",
  "brief": "To clear the screen.",
  "syntax": "CLS [n]",
  "details": [
  [
   "p",
   "n is one of the following values:",
  ],
  [
   "pre",
   "Value of n | Effect\n0 | Clears the screen of all text and graphics\n1 | Clears only the graphics viewport\n2 | Clears only the text window",
  ],
  [
   "p",
   "CLS without an argument behaves like CLS 0: in text mode it clears the text window, and in graphics mode it clears the entire graphics window to the background color.",
  ],
  [
   "p",
   "If a VIEW viewport is active, CLS clears only the viewport (in graphics mode) or the text window (in text mode). To clear the whole graphics window while a viewport is active, first disable the viewport with a bare VIEW statement, then CLS.",
  ],
  [
   "p",
   "In text mode CLS returns the cursor to the upper-left corner. In graphics mode the last graphics point referenced is reset to the center of the window, so the relative forms of PSET and LINE start from there again.",
  ]
  ],
  "examples": [
"1 CLS",
"10 SCREENSIZE 320,200\n20 CLS"
  ]
},
 "BEEP": {
  "title": "BEEP Statement",
  "brief": "To sound the speaker at 800 Hz (800 cycles per second) for one-quarter of a second.",
  "syntax": "BEEP",
  "details": [
   [
    "p",
    "BEEP, CTRL-G, and PRINT CHR$(7) have the same effect."
   ]
  ],
  "examples": [
   "2340 IF X>20 THEN BEEP"
  ],
  "note": None
 },
 "RANDOMIZE": {
  "title": "RANDOMIZE Statement",
  "brief": "To reseed the random number generator.",
  "syntax": "RANDOMIZE [expression]\nRANDOMIZE TIMER",
  "details": [
   [
    "p",
    "If expression is omitted, GW-BASIC suspends program execution and asks for a value by displaying the following line:"
   ],
   [
    "pre",
    "Random number seed (-32768 to 32767)?"
   ],
   [
    "p",
    "If the random number generator is not reseeded, the RND function returns the same sequence of random numbers each time the program is run."
   ],
   [
    "p",
    "To change the sequence of random numbers every time the program is run, place a RANDOMIZE statement at the beginning of the program, and change the argument with each run (see RND function)."
   ],
   [
    "p",
    "RANDOMIZE with no arguments will prompt you for a new seed. RANDOMIZE [expression] will not force floating-point values to integer. expression may be any numeric formula."
   ],
   [
    "p",
    "To get a new random seed without prompting, use the new numeric TIMER function as follows:"
   ],
   [
    "pre",
    "RANDOMIZE TIMER"
   ]
  ],
  "examples": [
   "10 RANDOMIZE TIMER\n20 FOR I=1 to 5\n30 PRINT RND;\n40 NEXT I\nRUN\n .88598 .484668 .586328 .119426 .709225\nRUN\n .803506 .162462 .929364 .292443 .322921",
   "5 N=VAL(MID$(TIME$, 7, 2)) 'get seconds for seed\n10 RANDOMIZE N             'install number\n20 PRINT N                 'print seconds\n30 PRINT RND               'print random number generated\nRUN\n 36\n .2466638\nRUN\n 37\n .6530511\nRUN\n 38\n 5.943847E+02\nRUN\n 40\n .8722131"
  ],
  "note": None
 },
 "LOCATE": {
  "title": "LOCATE Statement",
  "brief": "To move the text cursor to the specified position.",
  "syntax": "LOCATE [row][,[col][,[cursor][,[start] [,stop]]]]",
  "details": [
   [
    "p",
    "row is the line number and col (below) the column number, both numeric expressions. What they address depends on whether a SCREENSIZE window exists yet:"
   ],
   [
    "p",
    "Before a window exists, row and col set the desktop pixel position where the next SCREENSIZE will place the window's top-left corner - row is the distance from the top of the desktop, col the distance from the left, in pixels. There is no range limit, so the window can be placed anywhere on the screen: LOCATE 10,10 followed by SCREENSIZE 200,200 opens the 200x200 window with its top-left corner at (10,10). Until a LOCATE runs, the default is the top-left corner of the screen."
   ],
   [
    "p",
    "Inside a window (after SCREENSIZE has run), row and col address the text page relative to the window's top-left corner: row is the text line and col the text column, in character cells (with the default TEXTSIZE 8 in a 320x200 window that is lines 1-25, columns 1-40)."
   ],
   [
    "p",
    "Because the position is counted in character cells, where the cursor actually lands in pixels depends on the current TEXTSIZE: cell (row, col) sits row*TEXTSIZE pixels below and col*TEXTSIZE pixels to the right of the window's top-left corner. The same LOCATE therefore points to a different pixel position when the text size changes - row 5 is 40 pixels down at TEXTSIZE 8 but only 20 pixels down at TEXTSIZE 4 - and the number of lines and columns that fit in the window changes with it."
   ],
   [
    "p",
    "row and col have no range limit; a value outside the page simply leaves the cursor off the surface and characters printed there are clipped."
   ],
   [
    "p",
    "cursor is a Boolean value indicating whether the cursor is visible; zero is off, nonzero is on."
   ],
   [
    "p",
    "start is the cursor start scan line, a numeric expression within the range of 0 to 31."
   ],
   [
    "p",
    "stop is the cursor stop scan line, a numeric expression within the range of 0 to 31."
   ],
   [
    "p",
    "When the cursor is moved to the specified position, subsequent PRINT statements begin placing characters at this location. Optionally, the LOCATE statement may be used to start the cursor blinking on or off, or change the size of the blinking cursor."
   ],
   [
    "p",
    "Values outside the range of start or stop (0-31) result in an \"Illegal function call\" error; the previous value is retained. Omitted parameters keep their previous values."
   ],
   [
    "p",
    "As you set up the parameters for the LOCATE statement, you may find that you do not wish to change one or more of the existing specifications. To omit a parameter from this LOCATE statement, insert a comma for the parameter that is being skipped. If the omitted parameter(s) occurs at the end of the statement, you do not have to type the comma."
   ],
   [
    "p",
    "If the start scan line parameter is given and the stop scan line parameter is omitted, stop assumes the start value."
   ]
  ],
  "examples": [
   "10 LOCATE 1,1",
   "20 LOCATE ,,1",
   "30 LOCATE ,,,7"
  ],
  "note": "Before a SCREENSIZE window exists, LOCATE records where the window's top-left corner will be placed; inside a window it moves the text cursor relative to the window."
 },
 "OPEN": {
  "title": "OPEN Statement",
  "brief": "To establish input/output (I/O) to a file or device.",
  "syntax": "OPEN mode,[#]file number,filename[,reclen]\nOPEN filename [FOR mode] AS [#]file number [LEN=reclen]",
  "details": [
   [
    "p",
    "filename is the name of the file."
   ],
   [
    "p",
    "mode (first syntax) is a string expression with one of the following characters:"
   ],
   [
    "table",
    "Expression | Specifies\nO | Sequential output mode\nI | Sequential input mode\nR | Random input/output mode\nA | Position to end of file"
   ],
   [
    "p",
    "mode (second syntax) determines the initial positioning within the file, and the action to be taken if the file does not exist. If the FOR mode clause is omitted, the initial position is at the beginning of the file. If the file is not found, one is created. This is the random I/O mode. That is, records may be read or written at any position within the file. The valid modes and actions taken are as follows:"
   ],
   [
    "table",
    "INPUT | Position to the beginning of the file. A \"File not found\" error is given if the file does not exist.\nOUTPUT | Position to the beginning of the file. If the file does not exist, one is created.\nAPPEND | Position to the end of the file. If the file does not exist, one is created.\nRANDOM | Specifies random input or output mode."
   ],
   [
    "p",
    "mode must be a string constant. Do not enclose mode in double quotation marks."
   ],
   [
    "p",
    "file number is a number between 1 and the maximum number of files allowed. The number associates an I/O buffer with a disk file or device. This association exists until a CLOSE or CLOSE file number statement is executed."
   ],
   [
    "p",
    "reclen is an integer expression within the range of 1-32767 that sets the record length to be used for random files. If omitted, the record length defaults to 128-byte records."
   ],
   [
    "p",
    "When reclen is used for sequential files, the default is 128 bytes, and reclen cannot exceed the value specified by the /s switch."
   ],
   [
    "p",
    "A disk file must be opened before any disk I/O operation can be performed on that file. OPEN allocates a buffer for I/O to the file and determines the mode of access that is used with the buffer."
   ],
   [
    "p",
    "More than one file can be opened for input or random access at one time with different file numbers. For example, the following statements are allowed:"
   ],
   [
    "pre",
    "OPEN \"B:TEMP\" FOR INPUT AS #1\nOPEN \"B:TEMP\" FOR INPUT AS #2"
   ],
   [
    "p",
    "However, a file may be opened only once for output or appending. For example, the following statements are illegal:"
   ],
   [
    "pre",
    "OPEN \"TEMP\" FOR OUTPUT AS #1\nOPEN \"TEMP\" FOR OUTPUT AS #2"
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "Be sure to close all files before removing diskettes from the disk drives (see CLOSE and RESET)."
   ],
   [
    "p",
    "A device may be one of the following:"
   ],
   [
    "table",
    "A:, B:, C:... | Disk Drive\nKYBD: | Keyboard (input only)\nSCRN: | Screen (output only)\nLPT1: | Line Printer 1\nLPT2: | Line Printer 2\nLPT3: | Line Printer 3\nCOM1: | RS-232 Communications 1\nCOM2: | RS-232 Communications 2"
   ],
   [
    "p",
    "For each device, the following OPEN modes are allowed:"
   ],
   [
    "table",
    "KYBD: | Input Only\nSCRN: | Output Only\nLPT1: | Output Only\nLPT2: | Output Only\nLPT3: | Output Only\nCOM1: | Input, Output, or Random Only\nCOM2: | Input, Output, or Random Only"
   ],
   [
    "p",
    "Disk files allow all modes."
   ],
   [
    "p",
    "When a disk file is opened for APPEND, the position is initially at the end of the file, and the record number is set to the last record of the file (LOF(x)/128). PRINT, WRITE, or PUT then extends the file. The program may position elsewhere in the file with a GET statement. If this is done, the mode is changed to random and the position moves to the record indicated."
   ],
   [
    "p",
    "Once the position is moved from the end of the file, additional records may be appended to the file by executing a GET #x, LOF(x)/reclen statement. This positions the file pointer at the end of the file in preparation for appending."
   ],
   [
    "p",
    "Any values entered outside of the ranges given result in \"Illegal function call\" errors. The files are not opened."
   ],
   [
    "p",
    "If the file is opened as INPUT, attempts to write to the file result in \"Bad file mode\" errors."
   ],
   [
    "p",
    "If the file is opened as OUTPUT, attempts to read the file result in \"Bad file mode\" errors."
   ],
   [
    "p",
    "Opening a file for OUTPUT or APPEND fails, if the file is already open in any mode."
   ],
   [
    "p",
    "Since it is possible to reference the same file in a subdirectory via different paths, it is nearly impossible for GW-BASIC to know that it is the same file simply by looking at the path. For this reason, GW-BASIC does not let you open the file for OUTPUT or APPEND if it is on the same disk, even if the path is different. For example if mary is your working directory, the following statements all refer to the same file:"
   ],
   [
    "pre",
    "OPEN \"REPORT\"\nOPEN \"\\SALES\\MARY\\REPORT\"\nOPEN \"..\\MARY\\REPORT\"\nOPEN \"..\\..\\MARY\\REPORT\""
   ],
   [
    "p",
    "At any one time, it is possible to have a particular diskette filename open under more than one file number. Each file number has a different buffer, so several records from the same file may be kept in memory for quick access. This allows different modes to be used for different purposes; or, for program clarity, different file numbers to be used for different modes of access."
   ],
   [
    "p",
    "If the LEN=reclen option is used, reclen may not exceed the value set by the /s:reclen switch option in the command line."
   ],
  ],
  "examples": [
   "10 OPEN \"I\",2,\"INVEN\""
  ],
  "note": None
 },
 "CLOSE": {
  "title": "CLOSE Statement",
  "brief": "To terminate input/output to a disk file or a device.",
  "syntax": "CLOSE [[#]filenumber[,[#]filenumber]...]",
  "details": [
   [
    "p",
    "filenumber is the number under which the file was opened. The association between a particular file or device and file number terminates upon execution of a CLOSE statement. The file or device may then be reopened using the same or a different file number. A CLOSE statement with no file number specified closes all open files and devices."
   ],
   [
    "p",
    "A CLOSE statement sent to a file or device opened for sequential output writes the final buffer of output to that file or device."
   ],
   [
    "p",
    "The END, NEW, RESET, SYSTEM, or RUN and LOAD (without r option) statements always close all files or devices automatically. STOP does not close files."
   ]
  ],
  "examples": [
   "250 CLOSE",
   "300 CLOSE 1, #2, #3"
  ],
  "note": None
 },
 "KILL": {
  "title": "KILL Command",
  "brief": "To delete a file from a disk.",
  "syntax": "KILL filename",
  "details": [
   [
    "p",
    "filename can be a program file, sequential file, or random-access data file."
   ],
   [
    "p",
    "KILL is used for all types of disk files, including program, random data, and sequential data files."
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "You must specify the filename's extension when using the KILL command. Remember that files saved in GW-BASIC are given the default extension .BAS."
   ],
   [
    "p",
    "If a KILL command is given for a file that is currently open, a \"File already open\" error occurs."
   ]
  ],
  "examples": [
   "200 KILL \"DATA1.BAS\"",
   "KILL \"CATS\\DOGS\\RAINING.BAS\""
  ],
  "note": "The quotation marks around the filename are optional: KILL DATA1.BAS and KILL \"DATA1.BAS\" are equivalent, as with LOAD."
 },
 "MOUSE": {
  "title": "MOUSE Statement",
  "brief": "To wait for a mouse click on the graphics window and store its location.",
  "syntax": "MOUSE x [, y [, button]]",
  "details": [
   [
    "p",
    "MOUSE suspends the program until a mouse button is pressed on the graphics window, then stores the click location in x and y and the button number in button. x and y are integer window coordinates matching the active WINDOW mapping (or plain screen pixels when no WINDOW is in effect); button is 1 for the left button, 2 for the middle, and 3 for the right. y and button are optional."
   ],
   [
    "p",
    "Closing the window (ESC or the close box) while MOUSE is waiting stops the program, like pressing ESC. If no graphics window exists (text mode, or the --nogui command line option), a \"Mouse not available\" error occurs. The variables must be simple numeric variables."
   ],
   [
    "p",
    "Only button presses are reported: button releases and cursor movement are not. Clicks made while the program is busy are queued and are read one per MOUSE statement."
   ]
  ],
  "examples": [
   "10 SCREEN 7\n20 CLS\n30 MOUSE X, Y\n40 PRINT \"clicked at\"; X; Y\n50 END"
  ],
  "note": "MOUSE is an extension of this interpreter; the original GW-BASIC had no mouse support."
 },
 "LINE": {
  "title": "LINE Statement",
  "brief": "To draw lines and boxes on the graphics window.",
  "syntax": "LINE [(x1,y1)]-(x2,y2) [,[attribute][,B[F]][,style]]",
  "details": [
  [
   "p",
   "x1,y1 and x2,y2 specify the end points of a line as expressions in pixels.",
  ],
  [
   "p",
   "If the first coordinate is omitted, the line starts at the last point referenced (by a previous LINE, PSET, or DRAW). After a LINE statement, the last referenced point is x2, y2.",
  ],
  [
   "p",
   "Coordinates can be given in absolute form (x1,y1), or in relative form: STEP(xoffset,yoffset), which is an offset from the last referenced point. In a LINE statement, if the relative form is used on the second coordinate, it is relative to the first coordinate.",
  ],
  [
   "p",
   "attribute is the color number (0-15) of the line, or in a graphics mode the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function). If attribute is not specified, the current default foreground color is used. If attribute is omitted but B or BF is used, two commas must be used before B or BF.",
  ],
  [
   "p",
   "B (box) draws a box with the points (x1,y1) and (x2,y2) at opposite corners. BF (filled box) draws a box (as ,B) and fills in the interior with points.",
  ],
  [
   "p",
   "LINE supports the additional argument style. style is a 16-bit integer mask used when putting down pixels on the screen; this is called line-styling. Each time LINE stores a point on the screen, it uses the current circulating bit in style: if that bit is 0, no store is done; if the bit is 1, a normal store is done. After each point, the next bit position in style is selected. Since a 0 bit in style does not clear out the old contents, you may wish to draw a background line before a styled line, in order to force a known background. style is used for normal lines and boxes, but is illegal for filled boxes: if the BF parameter is used with the style parameter, a \"Syntax\" error occurs.",
  ],
  [
   "p",
   "Coordinates that are out of range are clipped: only the part of the line inside the window is visible. This is called line-clipping.",
  ]
  ],
  "examples": [
"LINE (0,100)-(639,100)",
"LINE (160,0)-(160,199)",
"LINE (0,0)-(319,199)",
"10 SCREENSIZE 320,200\n20 CLS\n30 LINE (20,20)-(120,120), 6, BF"
  ]
},
 "CIRCLE": {
  "title": "CIRCLE Statement",
  "brief": "To draw a circle, ellipse, or arc on the graphics window.",
  "syntax": "CIRCLE (xcenter,ycenter),radius[,[color][,[start],[end][,aspect]]]",
  "details": [
  [
   "p",
   "xcenter and ycenter are expressions giving the coordinates of the center of the figure. The center can also be given in relative form: STEP(xoffset,yoffset) or a plain xcenter,ycenter pair, which are offsets from the last point referenced (see the LINE statement).",
  ],
  [
   "p",
   "radius is an expression giving the radius of the figure in pixels. With the default aspect ratio of 1, CIRCLE draws a true circle: a midpoint-circle algorithm plots the outline pixel by pixel, so no anti-aliasing is applied.",
  ],
  [
   "p",
   "color is the color number (0-15) of the outline, or in a graphics mode the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function). If color is omitted, the current default foreground color (set with the COLOR statement) is used. In a custom-size window opened with SCREENSIZE, all 16 colors are available; color 0 is black, the usual background color, so drawing with color 0 is the standard way to erase a figure.",
  ],
  [
   "p",
   "start and end are angle arguments in radians between -2*pi and 2*pi that select an arc instead of a full circle. The arc begins at start and ends at end, measured counter-clockwise from the positive x-axis (the positive direction is to the right; the y-axis points down the screen). If start is omitted it defaults to 0; if end is omitted it defaults to start + 2*pi. An arc whose start or end angle is negative is connected to the center point with a straight line, and that angle is treated as if it were positive (this is different from adding 2*pi to it).",
  ],
  [
   "p",
   "aspect is the ratio of the x radius to the y radius (x:y). The default is 1, which draws a circle. If aspect is less than 1, radius is the x radius and the y radius is radius / aspect; if aspect is greater than 1, radius is the y radius and the x radius is radius * aspect. Arcs and ellipses are drawn by sampling points around the figure, so they may look slightly less smooth than a plain circle of the same radius.",
  ],
  [
   "p",
   "Coordinates may lie outside the window; only the part of the figure that falls inside is visible (line-clipping).",
  ],
  [
   "p",
   "CIRCLE is valid only in graphics mode; in text mode it has no effect.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 CLS\n30 CIRCLE (100,100), 50",
"1 ' Concentric circles\n10 SCREENSIZE 320,200\n20 CLS\n30 FOR R = 160 TO 0 STEP -10\n40 CIRCLE (160,100), R\n50 NEXT",
"10 ' A pie slice: arc from 0 to pi/2; the negative end connects the arc to the center\n20 SCREENSIZE 320,200\n30 CLS\n40 CIRCLE (100,100), 60, 6, 0, -1.5708"
  ]
},
 "DRAW": {
  "title": "DRAW Statement",
  "brief": "To draw a figure with Graphics Macro Language (GML).",
  "syntax": "DRAW string expression",
  "details": [
  [
   "p",
   "The DRAW statement combines most of the capabilities of the other graphics statements in a drawing language called Graphics Macro Language (GML). A GML command is a single character within a string, optionally followed by one or more arguments. Commands are separated by semicolons. The string may be built up in a variable.",
  ],
  [
   "p",
   "DRAW is valid only in graphics mode; in text mode it has no effect.",
  ],
  [
   "h",
   "Movement Commands",
  ],
  [
   "p",
   "Each movement command begins at the current graphics position. This is normally the coordinate of the last point plotted by another GML command, LINE, or PSET. When a program starts (or after CLS), the current position defaults to the center of the window. Movement commands move for a distance of scale factor * n, where the default for n is 1; thus they move one point if n is omitted and the default scale factor is used.",
  ],
  [
   "pre",
   "Command | Moves\nUn | up\nDn | down\nLn | left\nRn | right\nEn | diagonally up and right\nFn | diagonally down and right\nGn | diagonally down and left\nHn | diagonally up and left",
  ],
  [
   "p",
   "The M command moves as specified by the following argument:",
  ],
  [
   "pre",
   "Mx, y | Move absolute or relative. If x is preceded by a + or -, x and y are added to the current graphics position, and connected to the current position by a line. Otherwise, a line is drawn to point x, y from the current position.",
  ],
  [
   "p",
   "The following prefix commands may precede any of the above movement commands:",
  ],
  [
   "pre",
   "B | Move, but plot no points.\nN | Move, but return to original position when done.",
  ],
  [
   "h",
   "Other Commands",
  ],
  [
   "pre",
   "An | Set angle n. n may range from 0 to 3, where 0 is 0 degrees, 1 is 90 degrees, 2 is 180 degrees, and 3 is 270 degrees. The angle rotates the U, D, L, and R movement commands.\nTAn | Turn angle n. n can be any value from negative 360 to positive 360. A positive value turns the angle counter-clockwise; a negative value turns it clockwise.\nCn | Set color n. See the COLOR and SCREEN statements for the valid color numbers; in a graphics mode n may also be the value of the RGB(r,g,b) function.\nSn | Set scale factor. n may range from 1 to 255. n is divided by 4 to derive the scale factor, which is multiplied by the distances given with U, D, L, R, E, F, G, H, or relative M commands. The default for S is 4.\nxstring; variable | Execute substring. This command executes a second substring from a string, much like GOSUB. One string executes another, which executes a third, and so on. string is a variable assigned to a string of movement commands.\nPpaint, boundary | Fill a figure. paint is the fill color and boundary is the border color (outline) of the figure to fill; in a graphics mode each may also be the value of the RGB(r,g,b) function. You must specify values for both paint and boundary when P is used. The fill starts from the current graphics position and spreads through every pixel that is not the boundary color. This command does not support color tiling.",
  ],
  [
   "p",
   "Because the screen's y-axis points downward, \"up\" (U) decreases the y coordinate.",
  ]
  ],
  "examples": [
"10 SCREEN 1\n20 A = 20\n30 DRAW \"U=A; R=A; D=A; L=A;\"",
"10 CLS\n20 SCREEN 1\n30 PSET (60, 125)\n40 DRAW \"E100; F100; L199\""
  ]
},
 "PAINT": {
  "title": "PAINT Statement",
  "brief": "To fill in a graphics figure with the selected color.",
  "syntax": "PAINT (x,y)[,color[,border[,bckgrnd]]]",
  "details": [
  [
   "p",
   "The PAINT statement fills an arbitrary graphics figure with the paint color, starting from the point (x,y). The starting point must be inside the figure (a non-border point); if the starting point is on the border, PAINT has no effect.",
  ],
  [
   "p",
   "If the paint color is not given, it defaults to the current foreground color. If the border color is not given, it defaults to the paint color. Filling stops when a pixel of the border color is reached: the border itself is left in place, and only the enclosed region is filled.",
  ],
  [
   "p",
   "In a graphics mode, each of the color, border and bckgrnd attributes may also be the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function).",
  ],
  [
   "p",
   "The optional bckgrnd attribute is the color to skip when checking for boundary termination: a pixel of that color is neither painted nor does it stop the fill, so the fill passes through it (a start point on that color fills nothing). It may be a color number, or a string in which case the low two bits of the first character give the color (the two-bits-per-pixel form used by the manual's tile patterns).",
  ],
  [
   "p",
   "Points that are specified outside the limits of the screen are ignored and no error occurs.",
  ],
  [
   "p",
   "Paint tiling (manual PAINT): a string paint attribute is a tile mask, 8 bits wide and 1 to 64 bytes long. Screen row y uses tile byte y MOD tile_length, with bit 7 (the MSB) at x MOD 8 = 0, so the pattern is replicated uniformly over the whole screen (as if PAINT (0,0).. had been used). In the 2-bits-per-pixel modes (SCREEN 1/10) every two bits of the byte are one of the four colors of the four pixels the byte describes; in all other graphics modes a set bit puts down a point in the current foreground color and a clear bit puts down nothing. More than two consecutive tile bytes equal to the bckgrnd attribute (default CHR$(0)) causes an Illegal function call error.",
  ],
  [
   "p",
   "A string paint attribute has no single border color, so with no explicit border attribute the fill has no border stop: it is confined to the connected region of the starting point's color (any other color, such as a figure outline, is naturally left in place). An explicit string border attribute is not defined by the manual and causes an Illegal function call error.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 CLS\n30 LINE (0, 0)-(100, 150), 2, B\n40 PAINT (50, 50), 1, 2",
"10 SCREENSIZE 320,200\n20 CLS\n30 CIRCLE (160,100),50,2\n40 PAINT (160,100),1,2",
"10 SCREENSIZE 320,200\n20 CLS\n30 PAINT (100,100),7\n40 LINE (0,100)-(319,100),4,BF\n50 PAINT (100,50),1,0,4\nLine 50 uses bckgrnd 4: the fill skips the brown line instead of stopping at it, so both sides of the line are painted.",
"10 SCREEN 7\n20 CLS\n30 LINE (50, 50)-(100, 80), 1, B\n40 COLOR 12\n50 PAINT (75, 65), CHR$(&H55)\nA checkerboard tile: where x MOD 8 is odd the tile bit is set, so those points are painted in the foreground color and the even points are left as they were.",
"10 SCREEN 2\n20 CLS\n30 PAINT (320, 100), CHR$(&H81)+CHR$(&H42)+CHR$(&H24)+CHR$(&H18)+CHR$(&H18)+CHR$(&H24)+CHR$(&H81)\nThe manual's tile example: SCREEN 2 is 1 bit per pixel, so each set tile bit puts down a point in the foreground, and the whole screen is painted with Xs in a 7-row pattern."
  ]
 },
 "POKE": {
  "title": "POKE Statement",
  "brief": "To write (poke) a byte of data into a memory location.",
  "syntax": "POKE a,b [,c,d ...]",
  "details": [
   [
    "p",
    "a and b are integer expressions. a is the offset address of the memory location to be poked and b is the data to be poked. b must be within the range of 0 to 255 and a within the range of 0 to 65535; a value outside its range is an \"Illegal function call\" error."
   ],
   [
    "p",
    "The DEF SEG statement last executed determines the segment (absolute address) that will be poked into. Several address,data pairs may be given on one statement, separated by commas."
   ],
   [
    "p",
    "The complementary function to POKE is PEEK, whose argument is an address from which a byte is to be read. POKE and PEEK are useful for efficient data storage, loading assembly language subroutines, and for passing arguments and results to and from assembly language subroutines."
   ]
  ],
  "examples": [
   "20 POKE &H5A00, &HFF\nPlaces the decimal value 255 (&HFF) into the hex offset location 5A00 (23040 decimal). See the PEEK function example."
  ],
  "note": "In this interpreter the poked/peeked memory is simulated: it starts zero-filled and is lost when the interpreter exits. Unlike GW-BASIC, which does not check the offsets specified, POKE here range-checks both a and b."
 },
 "PLAY": {
  "title": "PLAY Statement",
  "brief": "To play music by embedding a music macro language into the string data type.",
  "syntax": "PLAY string expression",
  "details": [
   [
    "p",
    "The single-character commands in PLAY are as follows. A-G are notes: a # or + following a note produces a sharp, and a - produces a flat; any note followed by #, +, or - must refer to a black key on a piano."
   ],
   [
    "p",
    "L(n) sets the length of each note: L4 is a quarter note, L1 is a whole note, and n may be from 1 to 64. A length may also follow the note to change the length for that note only (A16 is equivalent to L16A). T(n) sets the tempo, the number of L4s in a minute (n is 32 to 255, default 120). O(n) sets the current octave, 0 to 6 (default 4; middle C is at the beginning of octave 3). A greater-than or less-than symbol preceding a note plays the note in the next higher or lower octave."
   ],
   [
    "p",
    "N(n) plays note n, where n may range from 0 to 84 (n = 0 is a rest). P(n) is a pause (n is 1 to 64). MF (music foreground) and MB (music background) select foreground or background playback; in background mode as many as 32 notes (or rests) can be queued at one time, allowing the BASIC program to continue execution while the music plays. MN (music normal), ML (music legato), and MS (music staccato) make each note play seven-eighths, the full period, or three-quarters of the time determined by L, respectively."
   ],
   [
    "p",
    "A period after a note (or after a P pause) increases the playing time by 3/2 for each period: A. plays one and a half times the ascribed value, A.. plays 9/4 times it, A... 27/8, and so on. Xstring; executes a substring, where string is a variable assigned to a string of PLAY commands; the semicolon is required."
   ],
   [
    "p",
    "Numeric arguments follow the same syntax as under the DRAW statement: n may be a constant, or it may be a variable with = in front of it (=variable), in which case a semicolon is required after the variable (and also after the variable in Xstring)."
   ]
  ],
  "examples": [
   "PLAY \"L4CDEFGAB\"",
   "PLAY \"T120L8CDEFGA\"",
   "S$=\"T100CDEF\"\nPLAY \"XS$;\"   ' plays the music stored in S$"
  ],
  "note": "Unlike GW-BASIC, the PLAY statement is non-blocking in this interpreter: the music is queued on the background speaker (the same design the SOUND statement uses), so the program does not wait for the notes to finish in either MF or MB mode; in MB mode, notes beyond the 32-note buffer are dropped, as in GW-BASIC. Off Windows the playback is simulated (the terminal bell is sounded once per PLAY statement). The PLAY(n) function, which returns the number of notes left in the background queue, is not implemented."
 },
 "PALETTE": {
  "title": "PALETTE, PALETTE USING Statements",
  "brief": "Changes one or more of the colors in the palette.",
  "syntax": "PALETTE [attribute,color]\nPALETTE USING integer-array-name, arrayindex",
  "details": [
  [
   "p",
   "In this interpreter the 16 palette entries (colors 0-15) are fixed to the standard VGA colors (0 black, 1 blue, ... 15 white) and cannot be remapped. PALETTE and PALETTE USING are accepted for compatibility with legacy programs, but they have no visible effect: the statement runs, no error is issued, and the colors on screen are unchanged.",
  ],
  [
   "p",
   "PALETTE with no arguments is the compatibility form of \"reset the palette\"; it likewise does nothing. PALETTE attribute,color and PALETTE first,last,color are also accepted as no-ops. PALETTE USING array, index is accepted (index is an expression giving the first element of the array to use) and does nothing.",
  ],
  [
   "p",
   "If you need different colors, use the RGB(r,g,b) function to create any full-precision color, or pick colors per statement (the color argument of CIRCLE, LINE, PSET, PAINT, DRAW Cn, and PUT).",
  ]
  ],
  "examples": [
"PALETTE 0, 2         ' Accepted, but the palette is fixed",
"PALETTE USING A%(0)  ' Accepted, but has no effect"
  ],
  "note": "The 16 colors are the fixed VGA palette; they cannot be remapped in this interpreter."
},
 "COLOR": {
  "title": "COLOR Statement",
  "brief": "To select the display colors.",
  "syntax": "COLOR [foreground][,[background][,border]]",
  "details": [
  [
   "p",
   "COLOR selects the colors used for display. In text mode (SCREEN 0) it sets the default text foreground and background colors, and the border color of the window; in graphics mode it sets the default drawing color (foreground) and the window background color. The colors are numbers from the 16-color VGA palette: 0 black, 1 blue, 2 green, 3 cyan, 4 red, 5 magenta, 6 brown, 7 light gray, 8 dark gray, 9 light blue, 10 light green, 11 light cyan, 12 light red, 13 light magenta, 14 yellow, 15 white.",
  ],
  [
   "p",
   "In text mode the arguments are validated as follows: foreground is 0-31 (adding 16 to a color number 0-15 makes the text blink), background is 0-7, and border is 0-15 (blinking colors are not permitted for the background or border). A bare COLOR resets the background and border to black and the foreground to the default light gray.",
  ],
  [
   "p",
   "In graphics mode the foreground and background each take a color number in the range allowed by the current screen mode, or the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function); a border argument is not allowed (it causes an \"Illegal function call\" error). The default foreground is white (color 7) and the default background is black (color 0). In text mode RGB() colors are not accepted: the foreground range 0-31 uses +16 as the blink flag there.",
  ],
  [
   "p",
   "The foreground color may be the same as the background color, which makes displayed characters invisible.",
  ],
  [
   "p",
   "Arguments outside the valid ranges result in an \"Illegal function call\" error; the previous colors are retained.",
  ],
  [
   "p",
   "For more information, see CIRCLE, DRAW, INK, LINE, PAINT, PALETTE, PRESET, PSET, and SCREEN.",
  ]
  ],
  "examples": [
"SCREEN 0\nCOLOR 1, 2, 3   ' foreground=1, background=2, border=3",
"SCREEN 1\nCOLOR 1, 0      ' foreground=1, background=0",
"SCREEN 7\nCOLOR 3, 5      ' foreground=3, background=5",
"SCREENSIZE 320,200\nCOLOR 12, 0   ' yellow on black"
  ]
},
 "VIEW": {
  "title": "VIEW Statement",
  "brief": "To define a viewport limit from x1,y1 (upper-left) to x2,y2 (lower-right).",
  "syntax": "VIEW [[SCREEN][(x1,y1)-(x2,y2)]]",
  "details": [
  [
   "p",
   "VIEW with no arguments defines the entire screen as the viewport (it disables any viewport set by a previous VIEW).",
  ],
  [
   "p",
   "(x1,y1) are the upper-left coordinates of the viewport and (x2,y2) the lower-right coordinates, in pixels. The coordinate pairs are sorted, with the smallest values placed first, so you may give the corners in either order. The coordinates must be within the physical bounds of the window; otherwise an \"Illegal function call\" error occurs.",
  ],
  [
   "p",
   "If the SCREEN argument is omitted, points are plotted relative to the viewpoint: x1 and y1 are added to the x and y coordinates before the point is plotted. If the SCREEN argument is present, points are plotted absolutely and only points within the current viewport are plotted.",
  ],
  [
   "p",
   "When a viewport is active, the CLS statement clears only the viewport. To clear the entire screen, disable the viewport with a bare VIEW statement and then use CLS.",
  ],
  [
   "p",
   "The fill and border attributes from the original manual are not implemented; this interpreter accepts the coordinate forms above only.",
  ]
  ],
  "examples": [
"VIEW (10, 10)-(200, 100)",
"VIEW SCREEN (10, 10)-(200, 100)"
  ]
},
 "WINDOW": {
  "title": "WINDOW Statement",
  "brief": "To draw lines, graphics, and objects in space not bounded by the physical limits of the screen.",
  "syntax": "WINDOW [[SCREEN](x1,y1)-(x2,y2)]",
  "details": [
  [
   "p",
   "(x1,y1) and (x2,y2) are user-defined world coordinates; each may be any single-precision floating-point number. They define the world coordinate space that graphics statements map into the physical coordinate space set by the VIEW statement. WINDOW allows zoom and pan: it lets you draw in a space not bounded by the physical screen, and the coordinates are converted to physical coordinates for display.",
  ],
  [
   "p",
   "The x and y argument pairs are sorted into ascending order, so (x1,y1) is always the lower (x-min, y-min) corner. For example, WINDOW (50, 50)-(10, 10) becomes WINDOW (10, 10)-(50, 50), and WINDOW (-2, 2)-(2, -2) becomes WINDOW (-2, -2)-(2, 2).",
  ],
  [
   "p",
   "Without the SCREEN attribute, the y coordinate is inverted on subsequent graphics statements: (x1,y1) is the lower-left corner and (x2,y2) the upper-right, giving true Cartesian coordinates. With the SCREEN attribute the coordinates are not inverted: (x1,y1) is the upper-left corner and (x2,y2) the lower-right.",
  ],
  [
   "p",
   "All coordinate pairs are valid except that x1 cannot equal x2 and y1 cannot equal y2; an equal pair is an \"Illegal function call\" error.",
  ],
  [
   "p",
   "WINDOW with no arguments disables any previous window statement (the screen returns to normal physical coordinates).",
  ],
  [
   "p",
   "In this implementation the OS window is the monitor: giving coordinates resizes the graphics window to the work area's span (one world unit per pixel) and places the window so that world (0,0) sits at the center of the monitor. A SCREEN statement, a RUN, or a bare WINDOW statement disables the window definition (the screen returns to normal physical coordinates).",
  ]
  ],
  "examples": [
"10 SCREEN 2\n20 WINDOW (-100, -50)-(100, 50)\n30 CIRCLE (0, 0), 50",
"10 SCREEN 2\n20 WINDOW SCREEN (-1, -1)-(1, 1)"
  ],
  "note": None
 },
 "BLOAD": {
  "title": "BLOAD Command",
  "brief": "To load a file into simulated memory.",
  "syntax": "BLOAD filename[,offset]",
  "details": [
  [
   "p",
   "filename is a string expression naming the file to load. offset is a numeric expression (0 to 65535): the offset within the 64K simulated memory segment, set by the last DEF SEG statement, where loading starts. If offset is omitted it defaults to 256 (the original GW-BASIC default).",
  ],
  [
   "p",
   "The file's bytes are copied into simulated memory starting at the segment base plus offset. This interpreter simulates a 64K segment of memory; there is no real hardware memory, so BLOAD cannot load machine code into a real CPU. It is useful for saving and restoring image buffers or for exercising legacy code.",
  ],
  [
   "p",
   "BLOAD does not perform an address range check. The load wraps around the 64K segment boundary. You must not BLOAD over the area that holds a GW-BASIC program or its variables (this interpreter keeps those apart from the simulated segment, so ordinary use is safe).",
  ],
  [
   "p",
   "While BLOAD and BSAVE are useful for loading and saving machine language programs, they are not restricted to them. The DEF SEG statement lets you specify any segment as the source or target for BLOAD and BSAVE. For example, this allows the video screen buffer to be read from or written to the disk. BLOAD and BSAVE are useful in saving and displaying graphic images.",
  ]
  ],
  "examples": [
"10 DEF SEG = &HB800\n20 BLOAD \"PICTURE\", 0"
  ]
},
 "BSAVE": {
  "title": "BSAVE Command",
  "brief": "To save a portion of simulated memory to a file.",
  "syntax": "BSAVE filename,offset,length",
  "details": [
  [
   "p",
   "filename is a string expression naming the file to create. offset is a numeric expression (0 to 65535): the offset within the 64K simulated memory segment, set by the last DEF SEG statement, where saving starts. length is a numeric expression (0 to 65535): the number of bytes to save.",
  ],
  [
   "p",
   "If filename is less than one character, a \"Bad File Number\" error is issued and the save is aborted.",
  ],
  [
   "p",
   "Execute a DEF SEG statement before the BSAVE. The last known DEF SEG address is always used for the save.",
  ],
  [
   "p",
   "To save a graphics screen buffer, set DEF SEG to the screen buffer's simulated address and use an offset of 0 with a length covering the buffer (for example, 16384 bytes for a 320x200 window).",
  ]
  ],
  "examples": [
"10 DEF SEG = &HB800\n20 BSAVE \"PICTURE\", 0, 16384"
  ]
},
 "OUT": {
  "title": "OUT Statement",
  "brief": "To send a byte to a machine output port (simulated).",
  "syntax": "OUT h,j",
  "details": [
  [
   "p",
   "h and j are integer expressions. h may be within the range of 0 to 65535; j may be within the range of 0 to 255. h is a machine port number and j is the data to be transmitted.",
  ],
  [
   "p",
   "This interpreter has no physical hardware: OUT writes j to a simulated port register. A subsequent INP(h) reads back exactly the value last written to port h (0 if nothing has been written yet). Use OUT/INP to exercise legacy code paths, not to control real devices.",
  ],
  [
   "p",
   "OUT is the complementary statement to the INP function. Values outside their ranges cause an \"Illegal function call\" error.",
  ]
  ],
  "examples": [
"100 OUT 8254, 0\n110 V = INP(8254)"
  ]
},
 "KEY": {
  "title": "KEY Statement",
  "brief": "To allow rapid entry of as many as 15 characters into a program with one keystroke.",
  "syntax": "KEY key number,string expression\nKEY n,CHR$(hex code)+CHR$(scan code)\nKEY(n) ON\nKEY(n) OFF\nKEY(n) STOP\nKEY ON\nKEY OFF\nKEY LIST",
  "details": [
   [
    "p",
    "key number is the number of the key to be redefined. key number may range from 1-20."
   ],
   [
    "p",
    "string expression is the key assignment. Any valid string of 1 to 15 characters may be used. If a string is longer than 15 characters, only the first 15 will be assigned. Constants must be enclosed in double quotation marks."
   ],
   [
    "p",
    "scan code is the variable defining the key you want to trap. Appendix H in the GW-BASIC User's Guide lists the scan codes for the keyboard keys."
   ],
   [
    "p",
    "hex code is the hexadecimal code assigned to the key shown below:"
   ],
   [
    "table",
    "Key | Hex code\nEXTENDED | &H80\nCAPS LOCK | &H40\nNUM LOCK | &H20\nALT | &H08\nCTRL | &H04\nSHIFT | &H01, &H02, &H03"
   ],
   [
    "p",
    "Hex codes may be added together, such as &H03, which is both shift keys."
   ],
   [
    "p",
    "Initially, the function keys are assigned the following special functions:"
   ],
   [
    "table",
    "F1 | LIST |  | F2 | RUN¿\nF3 | LOAD\" |  | F4 | SAVE\"\nF5 | CONT¿ |  | F6 | ,\"LPT1:\" ¿\nF7 | TRON¿ |  | F8 | TROFF¿\nF9 | KEY |  | F10 | SCREEN 000¿"
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "¿ (arrow) means that you do not have to press RETURN after each of these keys has been pressed."
   ],
   [
    "p",
    "Any one or all of the 10 keys may be redefined. When the key is pressed, the data assigned to it will be input to the program."
   ],
   [
    "pre",
    "KEY key number, \"string expression\""
   ],
   [
    "p",
    "Assigns the string expression to the specified key."
   ],
   [
    "pre",
    "KEY LIST"
   ],
   [
    "p",
    "List all 10 key values on the screen. All 15 characters of each value are displayed."
   ],
   [
    "pre",
    "KEY ON"
   ],
   [
    "p",
    "Displays the first six characters of the key values on the 25th line of the screen. When the display width is set at 40, five of the 10 keys are displayed. When the width is set at 80, all 10 are displayed."
   ],
   [
    "pre",
    "KEY OFF"
   ],
   [
    "p",
    "Erases the key display from the 25th line, making that line available for program use. KEY OFF does not disable the function keys."
   ],
   [
    "p",
    "If the value for key number is not within the range of 1 to 10, or 15 to 20, an \"Illegal function call\" error occurs. The previous KEY assignment is retained."
   ],
   [
    "p",
    "Assigning a null string (length 0) disables the key as a function key."
   ],
   [
    "p",
    "When a function key is redefined, the INKEY$ function returns one character of the assigned string per invocation. If the function key is disabled, INKEY$ returns a string of two characters: the first is binary zero; the second is the key scan code."
   ],
   [
    "h",
    "KEY(n) ON | OFF | STOP"
   ],
   [
    "p",
    "KEY(n) ON activates event trapping for key n (the trap line is set with ON KEY(n) GOSUB/GOTO); if the key was pressed while the event was stopped, the trap fires immediately. KEY(n) OFF disables trapping and forgets any pending key press. KEY(n) STOP disables trapping, but a key press that occurs is remembered so the trap fires as soon as KEY(n) ON is executed. See the ON KEY statement for the full trapping rules."
   ]
  ],
  "examples": [
   "10 KEY 1, \"MENU\"+CHR$(13)",
   "1 KEY OFF",
   "10 DATA KEY1, KEY2, KEY3, KEY4, KEY5\n20 FOR N=1 TO 5: READ SOFTKEYS$(n)\n30 KEY N, SOFTKEYS$(I)\n40 NEXT N\n50 KEY ON",
   "10 KEY 15, CHR$(4)+CHR$(70)\n20 ON KEY(15) GOSUB 1000\n30 KEY(15) ON\n.\n.\n.\n1000 PRINT \"trapped\"\n1010 RETURN"
  ],
  "note": "In this interpreter, keys 1-10 (F1-F10) are trapped by their scan codes (59-68) and their KEY n strings are delivered one character per INKEY$ call in program mode; keys 11-14 are the cursor keys; keys 15-20 are defined with KEY n,CHR$(hex code)+CHR$(scan code) and matched on the console scan code and modifier state (Windows only for the modifier mask). Trapping happens in program mode only."
 },
 "ENVIRON": {
  "title": "ENVIRON Statement",
  "brief": "To allow the user to modify parameters in GW-BASIC's environment string table. This may be to change the path parameter for a child process, (see ENVIRON$ and the MS-DOS utilities PATH command), or to pass parameters to a child by inventing a new environment parameter.",
  "syntax": "ENVIRON string",
  "details": [
   [
    "p",
    "string is a valid string expression containing the new environment string parameter."
   ],
   [
    "p",
    "string must be of the following form"
   ],
   [
    "pre",
    "parmid=text"
   ],
   [
    "p",
    "where parmid is the name of the parameter such as PATH."
   ],
   [
    "p",
    "parmid must be separated from text by an equal sign or a blank. ENVIRON takes everything to the left of the first blank or equal sign as the parmid; everything following is taken as text."
   ],
   [
    "p",
    "text is the new parameter text. If text is a null string, or consists only of a single semicolon, then the parameter (including parmid=) is removed from the environment string table, and the table is compressed. text must not contain any embedded blanks."
   ],
   [
    "p",
    "If parmid does not exist, then string is added at the end of the environment string table."
   ],
   [
    "p",
    "If parmid does exist, it is deleted, the environment string table is compressed, and the new string is added at the end."
   ],
   [
    "h",
    "ENVIRON(n) and ENVIRON$ Functions"
   ],
   [
    "p",
    "ENVIRON(n) returns the nth parameter (n within 1 to 255) from the environment string table; the null string is returned if there is no nth parameter."
   ],
   [
    "p",
    "ENVIRON$(name) returns the text following name= from the environment string table. ENVIRON$ distinguishes between upper- and lowercase; the null string is returned if the parameter is not found. See the ENVIRON$ function entry for details."
   ]
  ],
  "examples": [
   "ENVIRON \"PATH=A:\\\"",
   "ENVIRON \"COMSPEC=A:\\COMMAND.COM\"",
   "PATH=A:\\; COMSPEC=A:\\COMMAND.COM",
   "ENVIRON \"PATH=A:\\SALES; B:\\MKT:\"\nPRINT ENVIRON$(\"PATH\")\nA:\\SALES; B:\\MKT"
  ],
  "note": None
 },
 "FIELD": {
  "title": "FIELD Statement",
  "brief": "To allocate space for variables in a random file buffer.",
  "syntax": "FIELD [#] filenum, width AS stringvar [,width AS stringvar]...",
  "details": [
   [
    "p",
    "filenum is the number under which the file was opened."
   ],
   [
    "p",
    "width is the number of characters to be allocated to the string variable."
   ],
   [
    "p",
    "string variable is a string variable which will be used for random file access."
   ],
   [
    "p",
    "A FIELD statement must have been executed before you can"
   ],
   [
    "p",
    "For example, the following line allocates the first 20 positions (bytes) in the random file buffer to the string variable N$, the next 10 positions to ID$, and the next 40 positions to ADD$:"
   ],
   [
    "pre",
    "FIELD 1, 20 AS N$, 10 AS ID$, 40 AS ADD$"
   ],
   [
    "p",
    "FIELD only allocates space; it does not place any data in the random file buffer."
   ],
   [
    "p",
    "The total number of bytes allocated in a FIELD statement must not exceed the record length specified when the file was opened. Otherwise, a \"Field overflow\" error occurs (the default record length is 128)."
   ],
   [
    "p",
    "Any number of FIELD statements may be executed for the same file, and all FIELD statements executed are in effect at the same time."
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "Do not use a fielded variable name in an INPUT or LET statement. Once a variable name is fielded, it points to the correct place in the random file buffer. If a subsequent INPUT or LET statement with that variable name is executed, the variable's pointer is moved to string space (see LSET/RSET and GET statements)."
   ]
  ],
  "examples": [],
  "note": None
 },
 "ERROR": {
  "title": "ERROR Statement",
  "brief": "To simulate the occurrence of an error, or to allow the user to define error codes.",
  "syntax": "ERROR integer expression",
  "details": [
   [
    "p",
    "The value of integer expression must be greater than 0 and less than 255."
   ],
   [
    "p",
    "If the value of integer expression equals an error code already in use by GW-BASIC, the ERROR statement simulates the occurrence of that error, and the corresponding error message is printed."
   ],
   [
    "p",
    "A user-defined error code must use a value greater than any used by the GW- BASIC error codes. There are 76 GW-BASIC error codes at present. It is preferable to use a code number high enough to remain valid when more error codes are added to GW-BASIC."
   ],
   [
    "p",
    "User-defined error codes may be used in an error-trapping routine."
   ],
   [
    "p",
    "If an ERROR statement specifies a code for which no error message has been defined, GW-BASIC responds with the message \"Unprintable Error\"."
   ],
   [
    "p",
    "Execution of an ERROR statement for which there is no error-trapping routine causes an error message to be printed and execution to halt."
   ],
   [
    "p",
    "For a complete list of the error codes and messages already defined in GW-BASIC, refer to Appendix A in the GW-BASIC User's Guide."
   ]
  ],
  "examples": [
   "10 S=10\n20 T=5\n30 ERROR S+T\n40 END\nRUN\n String too long in 30",
   "ERROR 15          (you type this line)\n String too long  (GW-BASIC types this line)",
   ".\n.\n.\n110 ON ERROR GOTO 400\n120 INPUT \"WHAT IS YOUR BET\";B\n130 IF B>5000 THEN ERROR 210\n.\n.\n.\n400 IF ERR=210 THEN PRINT \"HOUSE LIMIT IS $5000\"\n410 IF ERL=130 THEN RESUME 120\n.\n.\n."
  ],
  "note": None
 },
 "WRITE": {
  "title": "WRITE Statement",
  "brief": "To output data to the screen.",
  "syntax": "WRITE[list of expressions]",
  "details": [
   [
    "p",
    "If list of expressions is omitted, a blank line is output. If list of expressions is included, the values of the expressions are output at the terminal. The expressions in the list may be numeric and/or string expressions, and must be separated by commas or semicolons."
   ],
   [
    "p",
    "When printed items are output, each item will be separated from the last by a comma. Printed strings are delimited by double quotation marks. After the last item in the list is printed, GW-BASIC inserts a carriage return/line feed."
   ],
   [
    "p",
    "The difference between WRITE and PRINT is that WRITE inserts commas between displayed items and delimits strings with double quotation marks. Positive numbers are not preceded by blank spaces."
   ],
   [
    "p",
    "WRITE outputs numeric values using the same format as the PRINT statement."
   ]
  ],
  "examples": [
   "10 A=80: B=90: C$=\"THAT'S ALL\"\n20 WRITE A, B, C$\nRUN\n 80, 90, \"THAT'S ALL\""
  ],
  "note": None
 },
 "FOR": {
  "title": "FOR ... NEXT Statement",
  "brief": "To execute a series of instructions a specified number of times in a loop.",
  "syntax": "FOR variable=x TO y [STEP z]\n.\n.\n.\nNEXT [variable][,variable...]",
  "details": [
   [
    "p",
    "variable is used as a counter."
   ],
   [
    "p",
    "x,y, and z are numeric expressions."
   ],
   [
    "p",
    "STEP z specifies the counter increment for each loop."
   ],
   [
    "p",
    "The first numeric expression (x) is the initial value of the counter. The second numeric expression (y) is the final value of the counter."
   ],
   [
    "p",
    "Program lines following the FOR statement are executed until the NEXT statement is encountered. Then, the counter is incremented by the amount specified by STEP."
   ],
   [
    "p",
    "If STEP is not specified, the increment is assumed to be 1."
   ],
   [
    "p",
    "A check is performed to see if the value of the counter is now greater than the final value (y). If it is not greater, GW-BASIC branches back to the statement after the FOR statement, and the process is repeated. If it is greater, execution continues with the statement following the NEXT statement. This is a FOR-NEXT loop."
   ],
   [
    "p",
    "The body of the loop is skipped if the initial value of the loop times the sign of the step exceeds the final value times the sign of the step."
   ],
   [
    "p",
    "If STEP is negative, the final value of the counter is set to be less than the initial value. The counter is decremented each time through the loop, and the loop is executed until the counter is less than the final value."
   ]
  ],
  "examples": [
   "10 K=10\n20 FOR I%=1 TO K STEP 2\n30   PRINT I%\n40 NEXT\nRUN\n 1\n 3\n 5\n 7\n 9",
   "10 R=0\n20 FOR S=1 TO R\n30   PRINT S\n40 NEXT S",
   "10 S=5\n20 FOR S=1 TO S+5\n30   PRINT S;\n40 NEXT\nRUN\n 1 2 3 4 5 6 7 8 9 10"
  ],
  "note": None
 },
 "NEXT": {
  "title": "FOR ... NEXT Statement",
  "brief": "To end a FOR ... NEXT loop and continue with the next iteration.",
  "syntax": "FOR variable=x TO y [STEP z]\n.\n.\n.\nNEXT [variable][,variable...]",
  "details": [
   [
    "p",
    "variable is used as a counter."
   ],
   [
    "p",
    "x,y, and z are numeric expressions."
   ],
   [
    "p",
    "STEP z specifies the counter increment for each loop."
   ],
   [
    "p",
    "The first numeric expression (x) is the initial value of the counter. The second numeric expression (y) is the final value of the counter."
   ],
   [
    "p",
    "Program lines following the FOR statement are executed until the NEXT statement is encountered. Then, the counter is incremented by the amount specified by STEP."
   ],
   [
    "p",
    "If STEP is not specified, the increment is assumed to be 1."
   ],
   [
    "p",
    "A check is performed to see if the value of the counter is now greater than the final value (y). If it is not greater, GW-BASIC branches back to the statement after the FOR statement, and the process is repeated. If it is greater, execution continues with the statement following the NEXT statement. This is a FOR-NEXT loop."
   ],
   [
    "p",
    "The body of the loop is skipped if the initial value of the loop times the sign of the step exceeds the final value times the sign of the step."
   ],
   [
    "p",
    "If STEP is negative, the final value of the counter is set to be less than the initial value. The counter is decremented each time through the loop, and the loop is executed until the counter is less than the final value."
   ]
  ],
  "examples": [
   "10 K=10\n20 FOR I%=1 TO K STEP 2\n30   PRINT I%\n40 NEXT\nRUN\n 1\n 3\n 5\n 7\n 9",
   "10 R=0\n20 FOR S=1 TO R\n30   PRINT S\n40 NEXT S",
   "10 S=5\n20 FOR S=1 TO S+5\n30   PRINT S;\n40 NEXT\nRUN\n 1 2 3 4 5 6 7 8 9 10"
  ],
  "note": None
 },
 "WHILE": {
  "title": "WHILE ... WEND Statement",
  "brief": "To execute a series of statements in a loop as long as a given condition is true.",
  "syntax": "WHILE expression\n.\n.\n.\n[loop statements]\n.\n.\n.\nWEND",
  "details": [
   [
    "p",
    "If expression is nonzero (true), loop statements are executed until the WEND statement is encountered. GW-BASIC then returns to the WHILE statement and checks expression. If it is still true, the process is repeated."
   ],
   [
    "p",
    "If it is not true, execution resumes with the statement following the WEND statement."
   ],
   [
    "p",
    "WHILE and WEND loops may be nested to any level. Each WEND matches the most recent WHILE."
   ],
   [
    "p",
    "An unmatched WHILE statement causes a \"WHILE without WEND\" error. An unmatched WEND statement causes a \"WEND without WHILE\" error."
   ]
  ],
  "examples": [
   "90 'BUBBLE SORT ARRAY A$\n100 FLIPS=1\n110 WHILE FLIPS\n115 FLIPS=0\n120 FOR N=1 TO J-1\n130 IF A$(N)>A$(N+1) THEN SWAP A$(N), A$(N+1): FLIPS=1\n140 NEXT N\n150 WEND"
  ],
  "note": None
 },
 "WEND": {
  "title": "WHILE ... WEND Statement",
  "brief": "To end a WHILE ... WEND loop and re-check the WHILE condition.",
  "syntax": "WHILE expression\n.\n.\n.\n[loop statements]\n.\n.\n.\nWEND",
  "details": [
   [
    "p",
    "If expression is nonzero (true), loop statements are executed until the WEND statement is encountered. GW-BASIC then returns to the WHILE statement and checks expression. If it is still true, the process is repeated."
   ],
   [
    "p",
    "If it is not true, execution resumes with the statement following the WEND statement."
   ],
   [
    "p",
    "WHILE and WEND loops may be nested to any level. Each WEND matches the most recent WHILE."
   ],
   [
    "p",
    "An unmatched WHILE statement causes a \"WHILE without WEND\" error. An unmatched WEND statement causes a \"WEND without WHILE\" error."
   ]
  ],
  "examples": [
   "90 'BUBBLE SORT ARRAY A$\n100 FLIPS=1\n110 WHILE FLIPS\n115 FLIPS=0\n120 FOR N=1 TO J-1\n130 IF A$(N)>A$(N+1) THEN SWAP A$(N), A$(N+1): FLIPS=1\n140 NEXT N\n150 WEND"
  ],
  "note": None
 },
 "PSET": {
  "title": "PSET / PRESET Statement",
  "brief": "To display (or erase) a point at a specified place on the graphics window.",
  "syntax": "PSET(x,y)[,color]\nPRESET(x,y)[,color]",
  "details": [
  [
   "p",
   "(x,y) represents the coordinates of the point in pixels.",
  ],
  [
   "p",
   "color is the color number (0-15) of the point, or in a graphics mode the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function). If color is not given, the current default foreground color is used. PRESET with no color erases the point: it sets it to the background color (color 0).",
  ],
  [
   "p",
   "Coordinates can be given in either absolute or relative form.",
  ],
  [
   "h",
   "Absolute Form",
  ],
  [
   "p",
   "(absolute x, absolute y) is more common and refers directly to a point without regard to the last point referenced. For example:",
  ],
  [
   "pre",
   "(10,10)",
  ],
  [
   "h",
   "Relative Form",
  ],
  [
   "p",
   "STEP (x offset, y offset) is a point relative to the most recent point referenced. For example:",
  ],
  [
   "pre",
   "STEP(10,10)",
  ],
  [
   "p",
   "Coordinate values may lie beyond the edge of the window; points outside the window are not plotted (line-clipping).",
  ],
  [
   "p",
   "(0,0) is the upper-left corner of the window; the lower-right corner is (XSZ()-1, YSZ()-1).",
  ],
  [
   "p",
   "See the COLOR statement for more information about colors.",
  ],
  [
   "p",
   "PSET and PRESET are valid only in graphics mode; in text mode they have no effect.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 CLS\n30 FOR I = 0 TO 100\n40 PSET (I,I)\n50 NEXT",
"40 FOR I = 100 TO 0 STEP -1\n50 PSET(I,I),0\n60 NEXT I"
  ]
},
 "PRESET": {
  "title": "PSET / PRESET Statement",
  "brief": "To display (or erase) a point at a specified place on the graphics window.",
  "syntax": "PSET(x,y)[,color]\nPRESET(x,y)[,color]",
  "details": [
  [
   "p",
   "(x,y) represents the coordinates of the point in pixels.",
  ],
  [
   "p",
   "color is the color number (0-15) of the point, or in a graphics mode the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function). If color is not given, the current default foreground color is used. PRESET with no color erases the point: it sets it to the background color (color 0).",
  ],
  [
   "p",
   "Coordinates can be given in either absolute or relative form.",
  ],
  [
   "h",
   "Absolute Form",
  ],
  [
   "p",
   "(absolute x, absolute y) is more common and refers directly to a point without regard to the last point referenced. For example:",
  ],
  [
   "pre",
   "(10,10)",
  ],
  [
   "h",
   "Relative Form",
  ],
  [
   "p",
   "STEP (x offset, y offset) is a point relative to the most recent point referenced. For example:",
  ],
  [
   "pre",
   "STEP(10,10)",
  ],
  [
   "p",
   "Coordinate values may lie beyond the edge of the window; points outside the window are not plotted (line-clipping).",
  ],
  [
   "p",
   "(0,0) is the upper-left corner of the window; the lower-right corner is (XSZ()-1, YSZ()-1).",
  ],
  [
   "p",
   "See the COLOR statement for more information about colors.",
  ],
  [
   "p",
   "PSET and PRESET are valid only in graphics mode; in text mode they have no effect.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 CLS\n30 FOR I = 0 TO 100\n40 PSET (I,I)\n50 NEXT",
"40 FOR I = 100 TO 0 STEP -1\n50 PSET(I,I),0\n60 NEXT I"
  ]
},
 "OPTION": {
  "title": "OPTION BASE Statement",
  "brief": "To declare the minimum value for array subscripts.",
  "syntax": "OPTION BASE n",
  "details": [
   [
    "p",
    "n is 1 or 0. The default base is 0."
   ],
   [
    "p",
    "If the statement OPTION BASE 1 is executed, the lowest value an array subscript can have is 1."
   ],
   [
    "p",
    "An array subscript may never have a negative value."
   ],
   [
    "p",
    "OPTION BASE gives an error only if you change the base value."
   ],
   [
    "p",
    "Note"
   ],
   [
    "p",
    "You must code the OPTION BASE statement before you can define or use any arrays. If an attempt is made to change the option base value after any arrays are in use, an error results."
   ]
  ],
  "examples": [],
  "note": None
 },
 "SCREEN": {
  "title": "SCREEN Statement",
  "brief": "To set the specifications for the display screen.",
  "syntax": "SCREEN [mode] [,[colorswitch]][,[apage]][,[vpage]]",
  "details": [
  [
   "p",
   "The SCREEN statement selects the screen mode. The modes open a graphics window of a fixed pixel size (or, for mode 0, the text console). The window is created by the underlying windowing system (tkinter on Windows) and can be resized with the window's own controls; see the SCREENSIZE statement if you want to choose the size yourself. Changing the screen mode clears the screen.",
  ],
  [
   "pre",
   "Mode | Description\n0  | Text mode: the console window, 40 columns x 25 lines\n1  | Graphics window, 320 x 200 pixels\n2  | Graphics window, 640 x 200 pixels\n7  | Graphics window, 320 x 200 pixels (the default graphics mode)\n8  | Graphics window, 640 x 200 pixels\n9  | Graphics window, 640 x 350 pixels\n10 | Graphics window, 640 x 350 pixels",
  ],
  [
   "p",
   "Any other mode number causes an \"Illegal function call\" error. The colorswitch, apage, and vpage arguments are accepted for compatibility but have no effect in this interpreter.",
  ],
  [
   "h",
   "SCREEN Function",
  ],
  [
   "p",
   "With no arguments, the SCREEN function returns the current screen mode: x = SCREEN.",
  ],
  [
   "p",
   "The function form SCREEN(n) returns the current color (0-15) of pen n (see the INK statement).",
  ],
  [
   "p",
   "The function form SCREEN(row, col[, z]) returns the ASCII code (0-255) for the character at the specified row (1 to 25) and column (1 to 40). If the optional argument z is true, the color attribute of the character is returned instead of its ASCII code (see the COLOR statement). Any value outside the indicated range results in an \"Illegal function call\" error.",
  ]
  ],
  "examples": [
"100 X = SCREEN(10, 10)\n' If the character at 10,10 is A, then X is 65.",
"10 SCREEN 7\n20 CIRCLE (160,100),50"
  ]
},
 "SCREENSIZE": {
  "title": "SCREENSIZE Instruction",
  "brief": "To open a window of a specific pixel size (width x height), or a window that fills the screen.",
  "syntax": "SCREENSIZE [x [, y]] | SCREENSIZE FULLSCREEN",
  "details": [
  [
   "p",
   "The SCREENSIZE instruction opens a graphics window that is x pixels wide and y pixels tall, where x and y are integer expressions giving the width and height in pixels. Unlike the SCREEN statement (which selects from a fixed set of window sizes), SCREENSIZE lets you choose any size you want, so you do not have to remember screen-mode numbers. The size is optional: a plain SCREENSIZE opens the classic 320x200 window (the same size as SCREEN 7), and SCREENSIZE x opens a square x-by-x window, so a direct find-and-replace of SCREEN 7 with SCREENSIZE works without change. The size is limited to 4096 pixels per side; out-of-range values cause an \"Illegal function call\" error. Alternatively, SCREENSIZE FULLSCREEN opens the window maximized so that it fills the screen; the interpreter determines the size (the screen size) rather than the program, and XSZ() and YSZ() report the live screen dimensions.",
  ],
  [
   "p",
   "The new screen uses the full 16-color VGA palette (colors 0-15), which is the maximum number of colors this interpreter supports. The background starts black (color 0) and the default drawing color is white (color 7); change them with the COLOR statement.",
  ],
  [
   "h",
   "Behavior",
  ],
  [
   "p",
   "The graphics window appears only when SCREENSIZE is executed; it is not shown at program load or when a program is read in. After SCREENSIZE runs, all the normal graphics statements work unchanged: COLOR, CIRCLE, LINE, PSET, PRESET, PAINT, and DRAW. Coordinates range from (0,0) at the upper-left corner to (x-1, y-1) at the lower-right corner.",
  ],
  [
   "p",
   "The window is a standard OS window: you can drag its edges to resize it at any time. The drawing surface follows the window: drag it larger and the surface grows to fill it (newly exposed area is the background color); drag it smaller and the excess is cropped. Read the live size with XSZ() and YSZ() (see those functions).",
  ],
  [
   "p",
   "The window's top-left corner is placed at the position set by the most recent LOCATE instruction: row is the distance from the top of the screen, column the distance from the left, in pixels - so LOCATE 10,10 followed by SCREENSIZE 200,200 opens the 200x200 window with its top-left corner at (10,10). Until a LOCATE runs, the default is the top-left corner of the screen. Each SCREENSIZE positions the window, so a later SCREENSIZE uses the LOCATE position in effect at that time. SCREENSIZE FULLSCREEN maximizes instead of positioning.",
  ]
  ],
  "examples": [
"10 LOCATE 10, 10\n20 SCREENSIZE 200, 200\n30 CIRCLE (100, 100), 50\n40 SLEEP 2",
"10 SCREENSIZE 640, 480\n20 COLOR 6\n30 CIRCLE (320, 240), 100\n40 SLEEP 2",
"10 SCREENSIZE 1000, 800\n20 CLS\n30 W = XSZ(): H = YSZ()\n40 CIRCLE (W/2, H/2), 100",
"10 SCREENSIZE FULLSCREEN\n20 CLS\n30 W = XSZ(): H = YSZ()\n40 CIRCLE (W/2, H/2), 100"
  ],
  "note": "The window is created lazily when SCREENSIZE executes and its top-left corner is placed at the position the last LOCATE set (default: the top-left corner of the screen). The maximum color depth is the 16-color VGA palette (colors 0-15)."
},
 "TEXTFONT": {
  "title": "TEXTFONT Instruction",
  "brief": "To set the font face and weight (bold, italic) used for text drawn on the monitor (the window).",
  "syntax": "TEXTFONT [font][, [bold][, [italic]]]",
  "details": [
  [
   "p",
   "The TEXTFONT instruction chooses the face the text on the monitor (the graphics window) is drawn in, and its weight. font is one of eleven face names - Arial, Segoe, Courier, Georgia, Tahoma, Calibri, NewTimes (Times New Roman), Verdana, Trebuchet, Canada (Candara), and Impact - matched without regard to upper and lower case. The bold argument is B or BOLD for bold and NB or NONBOLD for not bold; the italic argument is I, ITALIC, or ITALICS for italic and NI, NONITALIC, NONITALICS, or NOTITALIC for not italic. Each argument is optional and an omitted argument takes its own default, not the current value: font defaults to Arial, bold to not bold, and italic to not italic. So a bare TEXTFONT restores the default face (Arial, not bold, not italic), TEXTFONT ,,I is Arial regular italic, TEXTFONT ,B is Arial bold, and TEXTFONT Canada is Candara regular."
  ],
  [
   "p",
   "The text is always drawn from the real anti-aliased face fitted to the current TEXTSIZE cell - a larger TEXTSIZE gives bigger text of the same face, and B or I switches to that face's bold or italic file. Tahoma and Impact ship without separate bold or italic files, so a weight requested for them falls back to their single regular face. Changing the face takes effect from the next character drawn: lines already on the surface keep the face they were printed with (the monitor model), and the setting persists for the rest of the program and across CLS and SCREEN. Every RUN resets TEXTFONT to the default face, along with TEXTSIZE 11 and TEXTRotate 0. An unknown face name or an unrecognised bold or italic argument is an \"Illegal function call\"."
  ]
  ],
  "examples": [
"10 SCREENSIZE 320, 200\n20 CLS\n30 TEXTSIZE 11\n40 LOCATE 1, 1: TEXTFONT: PRINT \"ARIAL REGULAR\"\n50 LOCATE 2, 1: TEXTFONT ,B: PRINT \"ARIAL BOLD\"\n60 LOCATE 3, 1: TEXTFONT ,,I: PRINT \"ARIAL ITALIC\"\n70 LOCATE 4, 1: TEXTFONT NewTimes,B: PRINT \"TIMES NEW ROMAN BOLD\"\n80 LOCATE 5, 1: TEXTFONT Canada: PRINT \"CANDARA\"\n90 PAUSE",
"10 SCREENSIZE 320, 200\n20 CLS\n30 TEXTSIZE 13\n40 LOCATE 1, 1: TEXTFONT Verdana: PRINT \"VERDANA\"\n50 LOCATE 2, 1: TEXTFONT Verdana,B: PRINT \"VERDANA BOLD\"\n60 LOCATE 3, 1: TEXTFONT Verdana,,I: PRINT \"VERDANA ITALIC\"\n70 LOCATE 4, 1: TEXTFONT Impact: PRINT \"IMPACT\"\n80 PAUSE"
  ],
  "note": "TEXTFONT is an extension of classic GW-BASIC (the original has one fixed monitor font). It only affects text drawn on the monitor's character page, not graphics drawing."
},
 "TEXTSIZE": {
  "title": "TEXTSIZE Instruction",
  "brief": "To set the size, in pixels, of a character of text on the monitor (the window).",
  "syntax": "TEXTSIZE [size]",
  "details": [
  [
   "p",
   "The TEXTSIZE instruction sets the size, in pixels, of each character cell on the monitor (the graphics window), where size is a positive integer expression. The text is drawn from the real anti-aliased face chosen by TEXTFONT (Arial by default) fitted to a size-by-size pixel cell, so a larger size gives bigger, smoother text of the same face. A program starts with the default TEXTSIZE 11."
  ],
  [
   "p",
   "TEXTSIZE does not change the window's pixel dimensions - only how large the characters are. The number of character columns and rows that fit on the monitor is the window size divided by the text size, so a 320x200 window shows 29x18 characters at the default TEXTSIZE 11, and 20x12 at TEXTSIZE 16. LOCATE, PRINT, and INPUT all address the same character grid, so they scale with the text size automatically."
  ],
  [
   "p",
   "With no argument (a bare TEXTSIZE) the text size is reset to the default 11-pixel cell. A size below 1 is also treated as the default 11. The setting persists for the rest of the program; it can be changed at any time, including at the Ok prompt, and takes effect immediately. Every RUN resets it to 11, along with TEXTFONT and TEXTRotate 0."
  ]
  ],
  "examples": [
"10 SCREENSIZE 320, 200\n20 CLS\n30 TEXTSIZE 16\n40 PRINT \"BIGGER TEXT\"",
"10 SCREENSIZE 320, 200\n20 CLS\n30 FOR S = 8 TO 24 STEP 4\n40 LOCATE S/4, 1\n50 TEXTSIZE S\n60 PRINT \"TEXTSIZE \"; S\n70 NEXT S"
  ],
  "note": "TEXTSIZE is an extension of classic GW-BASIC (there is no such instruction in the original). It only affects text drawn on the monitor's character page, not graphics drawing."
},
 "TEXTROTATE": {
  "title": "TEXTRotate Instruction",
  "brief": "To rotate the lines of text drawn by 0-359 degrees clockwise.",
  "syntax": "TEXTRotate [degrees]",
  "details": [
  [
   "p",
   "The TEXTRotate instruction rotates each line that PRINT, LOCATE, and INPUT draw from now on, by degrees (an integer 0-359) CLOCKWISE - the whole line as a rigid object about its pivot, the text cursor's position at the line's start. Every character is turned by the same angle about the centre of its own cell and placed one cell further along the baseline rotated by that angle from horizontal, so the line spins as one object about the pivot instead of the characters tilting in place: with 90 the line runs straight down from the pivot, with 180 it runs back to the left, with 270 it runs straight up, and with 45 or 135 it runs along a diagonal. The character grid underneath is untouched - the cursor still advances one cell per character, LOCATE still addresses grid rows and columns, and when the line ends its newline moves the cursor to the start of the next grid row exactly as for an upright line."
  ],
  [
   "p",
   "The rotation is persistent monitor state, like TEXTSIZE and COLOR: it applies to every line drawn until another TEXTRotate changes it, and it persists across CLS and SCREEN. Every RUN resets the rotation to upright (0), along with TEXTSIZE 11 and TEXTFONT. Lines already on the surface are not re-drawn, so existing text keeps the angle it was printed with (the monitor model: the surface shows what was drawn), and changing the angle repaints nothing - the new angle simply applies from the next line, so the window never flashes. The pivot and the angle are captured when a line's first rotated character is drawn, so a line in progress never kinks: a TEXTRotate typed in the middle of a line that is already rotating takes effect from the next line."
  ],
  [
   "p",
   "The rotated line is composited into the pixel buffer as well as the window display, so GET captures the text exactly as the monitor shows it. Characters that run off the surface are clipped like any drawing. With no argument (a bare TEXTRotate) or 0 the text is upright again. A value outside 0-359 is an \"Illegal function call\"."
  ]
  ],
  "examples": [
"10 SCREENSIZE 320, 200\n20 CLS\n30 TEXTSIZE 16\n40 LOCATE 1, 1: PRINT \"UPRIGHT\"\n50 LOCATE 2, 2: TEXTRotate 45: PRINT \"45\"\n60 LOCATE 2, 6: TEXTRotate 90: PRINT \"90\"\n70 LOCATE 4, 20: TEXTRotate 180: PRINT \"180\"\n80 LOCATE 12, 2: TEXTRotate 270: PRINT \"270\"",
"10 SCREENSIZE 480, 320\n20 CLS\n30 TEXTSIZE 16\n40 FOR D = 0 TO 330 STEP 30\n50 LOCATE 14 - D/30, 14 - D/30: TEXTRotate D: PRINT \"ROT\"\n60 NEXT D"
  ],
  "note": "TEXTRotate is an extension of classic GW-BASIC (there is no such instruction in the original). It rotates whole lines about their pivot; it does not change the character grid, the cursor's grid position, or the window's pixel dimensions."
},
 "PAUSE": {
  "title": "PAUSE Instruction",
  "brief": "To stop the program until the user presses the SPACE BAR or ENTER, and then continue.",
  "syntax": "PAUSE",
  "details": [
  [
   "p",
   "The PAUSE instruction stops the program and waits until the user presses the SPACE BAR or the ENTER key, and then continues with the next instruction. Any other key is ignored and the wait continues. PAUSE takes no arguments - PAUSE 5 is an \"Expected end of statement\" error. It can be used as a numbered statement inside a program (10 PAUSE) or as an immediate statement at the Ok prompt."
  ],
  [
   "p",
   "While the program is paused, pressing CTRL+C stops execution as usual, and ESC - or closing the graphics window - stops the program the same way as anywhere else. When the graphics window is open, SPACE or ENTER typed into the window releases the pause, exactly as it would in the console."
  ],
  [
   "p",
   "When the program's input is not an interactive console (redirected input, or a test harness), PAUSE reads a line instead of a single key so the wait never hangs: any line, including an empty one (ENTER), releases the pause, and at end-of-file the program simply continues."
  ]
  ],
  "examples": [
"10 CLS\n20 PRINT \"PRESS SPACE OR ENTER TO CONTINUE\"\n30 PAUSE\n40 PRINT \"THE PROGRAM RESUMED\"",
"10 FOR I = 1 TO 5\n20 PRINT \"PASS \"; I\n30 PAUSE\n40 NEXT I"
  ],
  "note": "PAUSE is an extension of classic GW-BASIC (the original has SLEEP but no PAUSE)."
},
 "WCLOSE": {
  "title": "WCLOSE Instruction",
  "brief": "To close the graphics window and return input/output to the console, without stopping the program.",
  "syntax": "WCLOSE",
  "details": [
  [
   "p",
   "The WCLOSE instruction destroys the graphics window (the one opened by SCREEN, SCREENSIZE, or WINDOW), exactly the way the window's own ESC key or a Ctrl+C would. It takes no arguments and it can be used both as a numbered statement inside a program (10 WCLOSE) and as an immediate statement at the Ok prompt."
  ],
  [
   "p",
   "When the window is closed, the input/output that the window was receiving returns to the console: the program keeps running in its current screen mode, and its next PRINT, INPUT, or INKEY$ goes to the console instead of the window. A later SCREEN, SCREENSIZE, or WINDOW opens the window again on demand."
  ],
  [
   "p",
   "The window is closed only by program end, by Ctrl+C (or the window's own ESC / close box), or by WCLOSE - it is never closed by a bare WINDOW statement, which only resets the world-coordinate mapping."
  ]
  ],
  "examples": [
"10 SCREENSIZE 320, 200\n20 CLS\n30 PRINT \"PRESS ESC OR RUN WCLOSE\"\n40 SLEEP 1\n50 GOTO 40\n60 ' 10 WCLOSE  ' typed at the Ok prompt closes the window",
"10 WINDOW (-200,200)-(200,200)\n20 CLS\n30 WCLOSE\n40 PRINT \"BACK AT THE CONSOLE\""
  ],
  "note": "WCLOSE is an extension of classic GW-BASIC (there is no such instruction in the original). It closes the window only - the program continues running and the screen stays in its current mode."
},
 "DEFINT": {
  "title": "DEFINT Statement",
  "brief": "To declare the named variables as integer.",
  "syntax": "DEFINT name[, name ...]",
  "details": [
   [
    "p",
    "type is INT (integer), SNG (single-precision number), DBL (double-precision number), or STR (string of 0-255 characters)."
   ],
   [
    "p",
    "names are the exact names of the variables to be typed, separated by commas; a range of two letters (A-Z) names the single-letter variables in between."
   ],
   [
    "p",
    "A DEFtype statement declares that the named variables specify that type of variable. However, a type declaration character (%,!,#,$) always takes precedence over a DEFtype statement in the typing of a variable."
   ],
   [
    "p",
    "If no type declaration statements are encountered, BASIC assumes all variables are single-precision. Single-precision is the default value."
   ]
  ],
  "examples": [
   "10 DEFDBL L-P",
   "10 DEFSTR A\n20 A=\"120#\"",
   "10 DEFINT I-N, W-Z\n20 W$=\"120#\""
  ],
  "note": None
 },
 "DEFDBL": {
  "title": "DEFDBL Statement",
  "brief": "To declare the named variables as double-precision.",
  "syntax": "DEFDBL name[, name ...]",
  "details": [
   [
    "p",
    "type is INT (integer), SNG (single-precision number), DBL (double-precision number), or STR (string of 0-255 characters)."
   ],
   [
    "p",
    "names are the exact names of the variables to be typed, separated by commas; a range of two letters (A-Z) names the single-letter variables in between."
   ],
   [
    "p",
    "A DEFtype statement declares that the named variables specify that type of variable. However, a type declaration character (%,!,#,$) always takes precedence over a DEFtype statement in the typing of a variable."
   ],
   [
    "p",
    "If no type declaration statements are encountered, BASIC assumes all variables are single-precision. Single-precision is the default value."
   ]
  ],
  "examples": [
   "10 DEFDBL L-P",
   "10 DEFSTR A\n20 A=\"120#\"",
   "10 DEFINT I-N, W-Z\n20 W$=\"120#\""
  ],
  "note": None
 },
 "DEFSNG": {
  "title": "DEFSNG Statement",
  "brief": "To declare the named variables as single-precision.",
  "syntax": "DEFSNG name[, name ...]",
  "details": [
   [
    "p",
    "type is INT (integer), SNG (single-precision number), DBL (double-precision number), or STR (string of 0-255 characters)."
   ],
   [
    "p",
    "names are the exact names of the variables to be typed, separated by commas; a range of two letters (A-Z) names the single-letter variables in between."
   ],
   [
    "p",
    "A DEFtype statement declares that the named variables specify that type of variable. However, a type declaration character (%,!,#,$) always takes precedence over a DEFtype statement in the typing of a variable."
   ],
   [
    "p",
    "If no type declaration statements are encountered, BASIC assumes all variables are single-precision. Single-precision is the default value."
   ]
  ],
  "examples": [
   "10 DEFDBL L-P",
   "10 DEFSTR A\n20 A=\"120#\"",
   "10 DEFINT I-N, W-Z\n20 W$=\"120#\""
  ],
  "note": None
 },
 "DEFSTR": {
  "title": "DEFSTR Statement",
  "brief": "To declare the named variables as string.",
  "syntax": "DEFSTR name[, name ...]",
  "details": [
   [
    "p",
    "type is INT (integer), SNG (single-precision number), DBL (double-precision number), or STR (string of 0-255 characters)."
   ],
   [
    "p",
    "names are the exact names of the variables to be typed, separated by commas; a range of two letters (A-Z) names the single-letter variables in between."
   ],
   [
    "p",
    "A DEFtype statement declares that the named variables specify that type of variable. However, a type declaration character (%,!,#,$) always takes precedence over a DEFtype statement in the typing of a variable."
   ],
   [
    "p",
    "If no type declaration statements are encountered, BASIC assumes all variables are single-precision. Single-precision is the default value."
   ]
  ],
  "examples": [
   "10 DEFDBL L-P",
   "10 DEFSTR A\n20 A=\"120#\"",
   "10 DEFINT I-N, W-Z\n20 W$=\"120#\""
  ],
  "note": None
 },
 "GET": {
  "title": "GET Statement",
  "brief": "To read a record from a random disk file into a random buffer.",
  "syntax": "GET [#]file number[,record number]",
  "details": [
   [
    "p",
    "file number is the number under which the file was opened."
   ],
   [
    "p",
    "record number is the number of the record, within the range of 1 to 16,777,215."
   ],
   [
    "p",
    "If record number is omitted, the next record (after the last GET) is read into the buffer."
   ],
   [
    "p",
    "After a GET statement, INPUT# and LINE INPUT# may be used to read characters from the random file buffer."
   ],
   [
    "p",
    "GET may also be used for communications files. record number is the number of bytes to be read from the communications buffer. record number cannot exceed the buffer length set in the OPEN COM(n) statement."
   ]
  ],
  "examples": [
   "10 OPEN \"R\", 1, \"A:VENDOR.FIL\"\n20 FIELD 1, 30 AS VENDNAMES$, 20 AS ADDR$, 15 AS CITY$\n30 GET 1\n40 PRINT VENDNAMES$, ADDR$, CITY$\n50 CLOSE 1"
  ],
  "note": "This interpreter also supports the keyboard form GET var$, which reads a single character from the keyboard into a string variable."
 },
 "PUT": {
  "title": "PUT Statement",
  "brief": "To write a record from a random buffer to a random disk file.",
  "syntax": "PUT [#]file number[,record number]",
  "details": [
   [
    "p",
    "file number is the number under which the file was opened."
   ],
   [
    "p",
    "record number is the number of the record. If it is omitted, the record has the next available record number (after the last PUT)."
   ],
   [
    "p",
    "The largest possible record number is 232 -1. This will allow you to have large files with short record lengths. The smallest possible record number is 1."
   ],
   [
    "p",
    "The PRINT#, PRINT# USING, LSET, RSET, or WRITE# statements may be used to put characters in the random file buffer before a PUT statement."
   ],
   [
    "p",
    "In the case of WRITE#, GW-BASIC pads the buffer with spaces up to an enter."
   ],
   [
    "p",
    "Any attempt to read or write past the end of the buffer causes a \"Field overflow\" error."
   ],
   [
    "p",
    "PUT can be used for communications files. Here record number is the number of bytes written to the file. Record number must be less than or equal to the length of the buffer set in the OPEN \"COM(n) statement."
   ]
  ],
  "examples": [],
  "note": None
 },
 "DELETE": {
  "title": "DELETE Command",
  "brief": "To delete program lines or line ranges.",
  "syntax": "DELETE [line number1][-line number2]\nDELETE line number1-",
  "details": [
   [
    "p",
    "line number1 is the first line to be deleted."
   ],
   [
    "p",
    "line number2 is the last line to be deleted."
   ],
   [
    "p",
    "GW-BASIC always returns to command level after a DELETE command is executed. Unless at least one line number is given, an \"Illegal Function Call\" error occurs."
   ],
   [
    "p",
    "The period (.) may be used to substitute for either line number to indicate the current line."
   ],
   [
    "p",
    "A line number entered by itself (with no statement text) deletes that single line from the program, without the DELETE keyword. If the line does not exist, nothing happens."
   ]
  ],
  "examples": [
   "DELETE 40\nDeletes line 40.",
   "DELETE 40-100\nDeletes lines 40 through 100, inclusively.",
   "DELETE -40\nDeletes all lines up to and including line 40.",
   "DELETE 40-\nDeletes all lines from line 40 to the end of the program.",
   "40\nEntering just a line number deletes that line (equivalent to DELETE 40)."
  ],
  "note": "DELETE is a command-level command: type it at the Ok prompt, not on a numbered program line. To delete a file from a disk, use the KILL command. As an alternative to the DELETE command, type a line number alone at the Ok prompt to delete that line."
 },
 "RUN": {
  "title": "RUN Command",
  "brief": "To execute the program currently loaded in memory.",
  "syntax": "RUN [line number]",
  "details": [
   [
    "p",
    "RUN runs the program currently loaded in memory. RUN does not load a file from disk: use LOAD to bring a program in first, then RUN it."
   ],
   [
    "p",
    "RUN with no argument begins execution at the first (lowest) line number of the loaded program. RUN line number begins execution at that line instead."
   ],
   [
    "p",
    "If there is no program in memory when RUN is executed, an error (No loaded program) is reported."
   ],
   [
    "p",
    "If you are using the speaker on the computer, please note that executing the RUN command will turn off any sound that is currently running and will reset to Music Foreground. Also, the PEN and STRIG Statements are reset to OFF."
   ]
  ],
  "examples": [
   "RUN"
  ],
  "note": "Used as a statement inside a program, RUN stops execution and returns to the Ok prompt."
 },
 "COMMON": {
  "title": "COMMON Statement",
  "brief": "To declare COMMON variables.",
  "syntax": "COMMON variables",
  "details": [
   [
    "p",
    "variables are one or more variables, separated by commas."
   ],
   [
    "p",
    "COMMON statements may appear anywhere in a program, although it is recommended that they appear at the beginning."
   ],
   [
    "p",
    "Any number of COMMON statements may appear in a program, but the same variable cannot appear in more than one COMMON statement."
   ],
   [
    "p",
    "Place parentheses after the variable name to indicate array variables."
   ]
  ],
  "examples": [
   "100 COMMON A, B, C, D(),G$"
  ],
  "note": None
 },
 "SYSTEM": {
  "title": "SYSTEM Command",
  "brief": "To return to MS-DOS.",
  "syntax": "SYSTEM",
  "details": [
   [
    "p",
    "Save your program before pressing return, or the program will be lost."
   ],
   [
    "p",
    "The SYSTEM command closes all the files before it returns to MS-DOS. If you entered GW-BASIC through a batch file from MS-DOS, the SYSTEM command returns you to the batch file, which continues executing at the point it left off."
   ]
  ],
  "examples": [
   "SYSTEM\nA>"
  ],
  "note": "In this implementation SYSTEM returns to the Ok prompt (the interpreter stays running)."
 },
 "EDIT": {
  "title": "EDIT Command",
  "brief": "To display a specified line, and to position the cursor under the first digit of the line number.",
  "syntax": "EDIT line number\nEDIT .",
  "details": [
   [
    "p",
    "line number is the number of a line existing in the program."
   ],
   [
    "p",
    "A period (.) refers to the current line. The following command enters EDIT at the current line:"
   ],
   [
    "pre",
    "EDIT ."
   ],
   [
    "p",
    "When a line is entered, it becomes the current line."
   ],
   [
    "p",
    "The current line is always the last line referenced by an EDIT statement, LIST command, or error message."
   ],
   [
    "p",
    "If line number refers to a line which does not exist in the program, an \"Undefined Line Number\" error occurs."
   ]
  ],
  "examples": [
   "EDIT 150"
  ],
  "note": "In this implementation EDIT is accepted but has no effect."
 },
 "LEDIT": {
  "title": "LEDIT Command",
  "brief": "Edit a program line in place: the line is displayed with the cursor after its last character.",
  "syntax": "LEDIT line number",
  "details": [
   [
    "p",
    "line number is the number of a line existing in the program."
   ],
   [
    "p",
    "LEDIT displays the referenced line for in-place editing, with the cursor positioned after the last character of the line."
   ],
   [
    "p",
    "Use the LEFT and RIGHT arrow keys to move the cursor. BACKSPACE and DELETE remove characters. Typed characters are inserted at the cursor position (they do not overwrite existing text)."
   ],
   [
    "p",
    "Press ENTER to store the edited line. Press ESC or CTRL+C to cancel and leave the line unchanged."
   ],
   [
    "p",
    "If line number refers to a line which does not exist in the program, an \"Undefined Line Number\" error occurs."
   ]
  ],
  "examples": [
   "LEDIT 10",
   "LEDIT 123"
  ],
  "note": None
 },
 "TRACE": {
  "title": "TRACE Command",
  "brief": "Display the line being executed while the program runs, at a rate of lines per second.",
  "syntax": "TRACE ON [lines per second] [PAUSE]\nTRACE OFF\nTRACE",
  "details": [
   [
    "p",
    "TRACE ON enables tracing: as the program runs, the line being executed is displayed at the given rate of lines per second. The optional lines-per-second value defaults to 3 and must be a whole number from 1 to 100; an out-of-range value produces an error. While tracing is on, the program is paced to the specified rate - after each displayed line, execution pauses until the interval has elapsed, so the program runs at no more than the given lines per second. With TRACE OFF the program runs at full speed."
   ],
   [
    "p",
    "Every line that runs is displayed, including each iteration of a FOR/NEXT, WHILE/WEND, or DO/LOOP, and each is paced at the lines-per-second rate."
   ],
   [
    "p",
    "The optional PAUSE keyword makes the interpreter pause after each displayed line and resume only when you press ENTER or the SPACE BAR (no message is printed; any other key is ignored). The program resumes on the next line by itself - it does not break out to the Ok prompt. Press CTRL+C to end execution. For example, TRACE ON 5 PAUSE paces the program to 5 lines per second and waits for ENTER or SPACE after every line; TRACE ON 5 (without PAUSE) simply paces the program and runs continuously without waiting."
   ],
   [
    "p",
    "TRACE OFF disables tracing (and clears the PAUSE setting). A bare TRACE reports whether tracing is on or off, and at what rate. The trace flag is also cleared by NEW."
   ]
  ],
  "examples": [
   "TRACE ON",
   "TRACE ON 7",
   "RUN",
   "TRACE ON 5 PAUSE",
   "RUN",
   "TRACE OFF"
  ],
  "note": None
 },
 "TRAP": {
  "title": "TRAP Statement",
  "brief": "Turn the runtime safety checks on or off (TRAP ON / TRAP OFF).",
  "syntax": "TRAP ON\nTRAP OFF",
  "details": [
   [
    "p",
    "TRAP arms or bypasses the interpreter's per-statement runtime safety checks. With TRAP ON (the default), every statement runs the overflow guard and, when an ON KEY or ON COM trap is set, the pending key/COM event is polled. With TRAP OFF those checks are skipped, so integer-heavy and tight-loop programs run faster."
   ],
   [
    "p",
    "TRAP OFF does not hide errors: syntax errors, type mismatches (for example X$ = 5), and subscript out-of-range are still reported exactly as before. It only skips the value-domain checks (overflow and the ON KEY/COM trap poll). Use it once a program is known to be correct; it is not a substitute for debugging."
   ],
   [
    "p",
    "The setting is per run: it resets to ON at the start of every RUN, so a TRAP OFF in one run does not carry into the next or into immediate (direct) mode."
   ]
  ],
  "examples": [
   "10 TRAP OFF\n20 FOR I = 1 TO 1000000\n30   Y = Y + I\n40 NEXT I\n50 PRINT Y",
   "10 TRAP ON\n20 X = 5\n30 PRINT X * 4"
  ],
  "note": "TRAP is an extension to GW-BASIC (not a standard GW-BASIC statement). It is supported by both immediate mode and compiled RUN."
 },
 "CONT": {
  "title": "CONT Command",
  "brief": "To continue program execution after a break.",
  "syntax": "CONT",
  "details": [
   [
    "p",
    "Resumes program execution after CTRL-BREAK, STOP, or a trace stop (TRACE ON). Execution continues at the point where the break happened."
   ],
   [
    "p",
    "CONT is useful in debugging, in that it lets you set break points with the STOP statement, modify variables using direct statements, and continue program execution."
   ]
  ],
  "examples": [
   "STOP",
   "CONT"
  ],
  "note": None
 },
 "WAIT": {
  "title": "WAIT Statement",
  "brief": "To suspend program execution while monitoring the status of a machine input port.",
  "syntax": "WAIT port number, n[,j]",
  "details": [
   [
    "p",
    "port number represents a valid machine port number within the range of 0 to 65535."
   ],
   [
    "p",
    "n and j are integer expressions in the range of 0 to 255."
   ],
   [
    "p",
    "The WAIT statement causes execution to be suspended until a specified machine input port develops a specified bit pattern."
   ],
   [
    "p",
    "The data read at the port is XORed with the integer expression j, and then ANDed with n."
   ],
   [
    "p",
    "If the result is zero, GW-BASIC loops back and reads the data at the port again."
   ],
   [
    "p",
    "If the result is nonzero, execution continues with the next statement."
   ],
   [
    "p",
    "When executed, the WAIT statement tests the byte n for set bits. If any of the bits is set, then the program continues with the next statement in the program. WAIT does not wait for an entire pattern of bits to appear, but only for one of them to occur."
   ],
   [
    "p",
    "It is possible to enter an infinite loop with the WAIT statement. You can exit the loop by pressing CTRL-BREAK, or by resetting the system."
   ],
   [
    "p",
    "If j is omitted, zero is assumed."
   ]
  ],
  "examples": [
   "100 WAIT 32,2"
  ],
  "note": "In this implementation WAIT with a single argument suspends execution for that many seconds (capped at 5); WAIT port, n[, j] polls the simulated machine port (the value last written by OUT) in a bounded loop, so it always completes."
 },
 "ELSE": {
  "title": "IF ... THEN ... ELSE Statement",
  "brief": "Part of IF ... THEN ... ELSE; the ELSE statement runs when the IF expression is false.",
  "syntax": "IF expression[,] THEN statement(s)[,][ELSE statement(s)]\n IF expression[,] GOTO line number[[,] ELSE statement(s)]",
  "details": [
   [
    "p",
    "If the result of expression is nonzero (logical true), the THEN or GOTO line number is executed."
   ],
   [
    "p",
    "If the result of expression is zero (false), the THEN or GOTO line number is ignored and the ELSE line number, if present, is executed. Otherwise, execution continues with the next executable statement. A comma is allowed before THEN and ELSE."
   ],
   [
    "p",
    "THEN and ELSE may be followed by either a line number for branching, or one or more statements to be executed."
   ],
   [
    "p",
    "GOTO is always followed by a line number."
   ],
   [
    "p",
    "If the statement does not contain the same number of ELSE's and THEN's line number, each ELSE is matched with the closest unmatched THEN. For example:"
   ],
   [
    "pre",
    "IF A=B THEN IF B=C THEN PRINT \"A=C\" ELSE PRINT \"A < > C\""
   ],
   [
    "p",
    "will not print \"A < > C\" when A < > B."
   ],
   [
    "p",
    "If an IF...THEN statement is followed by a line number in the direct mode, an \"Undefined line number\" error results, unless a statement with the specified line number was previously entered in the indirect mode."
   ],
   [
    "p",
    "Because IF ..THEN...ELSE is all one statement, the ELSE clause cannot be on a separate line. It must be all on one line."
   ]
  ],
  "examples": [
   "200 IF N THEN GET #1, N",
   "100 IF(N<20) and (N>10) THEN DB=1979-1: GOTO 300\n110 PRINT \"OUT OF RANGE\"",
   "210 IF IOFLAG THEN PRINT A$ ELSE LPRINT A$"
  ],
  "note": None
 },
 "ON": {
  "title": "ON Statement",
  "brief": "To branch to one of several line numbers depending on an expression, or to enable error trapping.",
  "syntax": "ON expression GOTO line numbers\nON expression GOSUB line numbers\nON ERROR GOTO line number\nON ERROR OFF\nON KEY(n) GOSUB line number\nON KEY(n) GOTO line number\nON KEY(n) OFF\nON KEY OFF",
  "details": [
   [
    "h",
    "ON ... GOTO and ON ... GOSUB"
   ],
   [
    "p",
    "In the ON ... GOTO statement, the value of expression determines which line number in the list will be used for branching. For example, if the value is 3, the third line number in the list will be destination of the branch. If the value is a non-integer, the fractional portion is rounded."
   ],
   [
    "p",
    "In the ON ... GOSUB statement, each line number in the list must be the first line number of a subroutine."
   ],
   [
    "p",
    "If the value of expression is zero or greater than the number of items in the list (but less than or equal to 255), GW-BASIC continues with the next executable statement."
   ],
   [
    "p",
    "If the value of expression is negative, or greater than 255, an \"Illegal function call\" error occurs."
   ],
   [
    "h",
    "ON ERROR GOTO"
   ],
   [
    "p",
    "Once error trapping has been enabled, all errors detected by GW-BASIC, including direct mode errors, (for example, syntax errors) cause GW-BASIC to branch to the line in the program which begins the specified error-handling subroutine."
   ],
   [
    "p",
    "GW-BASIC branches to the line specified by the ON ERROR statement until a RESUME statement is found."
   ],
   [
    "p",
    "If line number does not exist, an \"Undefined line\" error results."
   ],
   [
    "p",
    "To disable error trapping, execute the following statement:"
   ],
   [
    "pre",
    "ON ERROR GOTO 0"
   ],
   [
    "p",
    "Subsequent errors print an error message and halt execution."
   ],
   [
    "p",
    "An ON ERROR GOTO 0 statement in an error-trapping subroutine causes GW-BASIC to stop and print the error message for the error that caused the trap. It is recommended that all error-trapping subroutines execute an ON ERROR GOTO 0 if an error is encountered for which there is no recovery action."
   ],
   [
    "p",
    "If an error occurs during execution of an error-handling subroutine, the GW-BASIC error message is printed and execution terminated. Error trapping does not occur within the error-handling subroutine."
   ]
  ],
  "examples": [
   "100 IF R<1 or R>4 then print \"ERROR\":END",
   "200 ON R GOTO 150,300,320,390",
   "10 ON ERROR GOTO 1000\n.\n.\n.\n1000 A=ERR: B=ERL\n1010 PRINT A, B\n1020 RESUME NEXT",
   "10 KEY 15, CHR$(4)+CHR$(70) REM define the key trapped as 15\n20 ON KEY(15) GOSUB 1000\n30 KEY(15) ON\n.\n.\n.\n1000 PRINT \"key trapped\"\n1010 RETURN"
  ],
  "note": "This interpreter also supports ON KEY(n) GOSUB/GOTO, ON KEY(n) OFF, ON KEY OFF, and ON TIMER(n) [GOTO|OFF] (parsed, not emulated). Key trapping is emulated in program mode: at the start of every statement the keyboard is checked, and a press of a trapped key whose event is ON branches to the trap line (the key is consumed; INKEY$/GET KEY cannot see it). KEY(n) ON | OFF | STOP control each event; while a trap is running its event is automatically stopped, and the RETURN from the trap routine automatically does an ON unless an explicit KEY(n) OFF was done inside the trap. No trapping occurs in direct mode."
 },
 "SETFPS": {
  "title": "SETFPS Statement",
  "brief": "To set the frame rate of the graphics window.",
  "syntax": "SETFPS x",
  "details": [
  [
   "p",
   "SETFPS x limits the graphics window to a maximum of x frames per second. x is any positive number (rounded to an integer; there is no upper limit). The default (no SETFPS yet) is unlimited - the program runs as fast as it can. SETFPS UNLIMITED (or SETFPS 0) removes the cap again. The cap is a ceiling only: a value the window cannot reach simply lets it paint as fast as it can.",
  ],
  [
   "p",
   "Each time the window is repainted after a graphics statement, execution pauses just long enough to keep the repaint rate at or below the target. The setting only limits the maximum repaint rate; it cannot make the window repaint faster than it already does. The window stays responsive while paused: you can resize it or press Ctrl+C to stop the program.",
  ],
  [
   "p",
   "With SETFPS in effect, a program can move an object a fixed number of pixels per frame and get a steady on-screen speed without reading TIMER. To keep one repaint per frame, combine the erase and redraw of an animated object on a single line (using :); each graphics statement repaints the window once, and every repaint counts against the frame budget.",
  ],
  [
   "p",
   "SETFPS is an extension of this interpreter; it is not part of MS-DOS BASIC.",
  ]
  ],
  "examples": [
"10 SCREENSIZE 320,200\n20 COLOR 4, 0\n30 CLS\n40 SETFPS 30\n50 X = X + 8\n60 IF X > 300 THEN X = 0\n70 CIRCLE (X-8,100),10,0 : CIRCLE (X,100),10,4\n80 GOTO 70"
  ],
  "note": "The new rate applies starting with the next graphics repaint."
},
 "SLEEP": {
  "title": "SLEEP Statement",
  "brief": "To pause program execution for a specified number of seconds.",
  "syntax": "SLEEP n",
  "details": [
  [
   "p",
   "SLEEP stops program execution for n seconds, where n is any numeric expression (fractions are allowed). After the pause, execution continues with the next statement. While paused the console stays responsive: Ctrl+C stops the program.",
  ],
  [
   "p",
   "SLEEP is a GW-BASIC extension; it is not part of MS-DOS BASIC.",
  ]
  ],
  "examples": [
"10 SLEEP 1\n20 PRINT \"one second has passed\"",
"10 SLEEP .5 : BEEP"
  ]
},
 "SOUND": {
  "title": "SOUND Statement",
  "brief": "To generate a tone through the sound driver.",
  "syntax": "SOUND freq,duration",
  "details": [
  [
   "p",
   "freq is the desired frequency in Hertz (cycles per second). freq is a numeric expression within the range of 37 to 32767.",
  ],
  [
   "p",
   "duration is the desired duration in clock ticks. Clock ticks occur 18.2 times per second. duration must be a numeric expression within the range of 0 to 65535.",
  ],
  [
   "p",
   "Values below .022 produce an infinite sound until the next SOUND or PLAY statement is executed.",
  ],
  [
   "p",
   "If duration is zero, any active SOUND statement is turned off. If no SOUND statement is running, a duration of zero has no effect.",
  ],
  [
   "p",
   "To produce a period of silence, use the following statement: SOUND 32767, duration",
  ]
  ],
  "examples": [
"2500 SOUND RND*1000+37, 2\n2600 GOTO 2500"
  ],
  "note": "On Windows this interpreter plays SOUND tones for real through the Windows sound driver (winsound, a square wave like the old PC speaker) in a background thread, so SOUND never blocks the program. On other platforms the sound is simulated and a starting tone is approximated with the terminal bell."
},
 "SEEK": {
  "title": "SEEK Statement",
  "brief": "To set a variable to the record number currently in a random file buffer.",
  "syntax": "SEEK #filenum, var",
  "details": [
   [
    "p",
    "filenum is the number under which a random file was opened with OPEN. var is set to the number of the record that is currently in the random file buffer (the record most recently read or written)."
   ],
   [
    "p",
    "After a file is opened, SEEK returns 0. For a file opened in BINARY mode, var is set to the current byte position in the file instead."
   ]
  ],
  "examples": [
   "10 OPEN \"RANDOM\", 1, \"DATA.DAT\", 80\n20 PUT #1, 5, \"record five\"\n30 SEEK #1, N\n40 PRINT N    :  5"
  ],
  "note": None
 },
 "REDIM": {
  "title": "REDIM Statement",
  "brief": "To change the size of an array, optionally preserving its contents.",
  "syntax": "REDIM [PRESERVE] varname(sub1[, sub2, ...])",
  "details": [
   [
    "p",
    "REDIM changes the dimensions of an array that was already declared with DIM (or already used). If the array has not been declared, REDIM declares it."
   ],
   [
    "p",
    "Without PRESERVE, all values in the array are lost. With PRESERVE, the existing values are kept and the array is resized."
   ]
  ],
  "examples": [
   "10 DIM A(10)\n20 FOR I = 1 TO 10 : A(I) = I : NEXT\n30 REDIM PRESERVE A(20)\n40 PRINT A(10)    :  10",
   "10 DIM B(5)\n20 REDIM B(10)    :  \"B is now B(0) to B(10), values lost\""
  ],
  "note": None
 },
 "INK": {
  "title": "INK Statement",
  "brief": "To set the pen color used by graphics output.",
  "syntax": "INK n [, color]",
  "details": [
  [
   "p",
   "INK sets the color of pen n (0-15) to color, a color number (0-15) or, in a graphics mode, the value of the RGB(r,g,b) function, which names a full-precision color (see the RGB function). Graphics statements that do not specify a color use the current foreground color (set with COLOR), not a pen color, so INK mainly matters for the SCREEN(n) function form and for keeping track of colors in your program.",
  ],
  [
   "p",
   "With a single argument, INK n returns the current color of pen n, so it can be used in an expression. The INK(n) function form is also accepted: it returns the current color of pen n - 0-15 for a palette color, or the 16+ index of an RGB() color. The default color of every pen is white (7).",
  ]
  ],
  "examples": [
"10 SCREEN 1\n20 INK 3, 6\n30 C = INK(3)"
  ]
},
 "CURSOR": {
  "title": "CURSOR Statement",
  "brief": "To make the text cursor visible or invisible.",
  "syntax": "CURSOR n",
  "details": [
  [
   "p",
   "If n is nonzero, the text cursor is displayed; if n is zero, the cursor is hidden. The setting affects the console text window only; the graphics window has no cursor.",
  ]
  ],
  "examples": [
"10 CLS\n20 CURSOR 0\n30 SLEEP 2\n40 CURSOR 1"
  ]
},
 "DO": {
  "title": "DO ... LOOP Statement",
  "brief": "To repeat a block of statements until a condition is met.",
  "syntax": "DO [WHILE expression | UNTIL expression]\n.\n.\n.\n[loop statements]\n.\n.\n.\nLOOP [WHILE expression | UNTIL expression]",
  "details": [
   [
    "p",
    "DO...LOOP repeats the loop statements. The DO line's condition, if any, is checked before each pass, including the first: with WHILE the block runs while the expression is true, with UNTIL only until it becomes true. If the condition is not satisfied, the block (and the LOOP statement) is skipped entirely."
   ],
   [
    "p",
    "If the LOOP line has WHILE or UNTIL, its condition is checked after each pass; when it is not satisfied, control continues with the statement after the LOOP. A DO...LOOP with no conditions loops forever."
   ],
   [
    "p",
    "DO...LOOP is a GW-BASIC extension; it is not part of MS-DOS BASIC. DO...LOOP blocks may be nested."
   ]
  ],
  "examples": [
   "10 N = 0\n20 DO\n30 N = N + 1\n40 LOOP UNTIL N >= 10\n50 PRINT N    :  10",
   "10 I = 1\n20 DO WHILE I <= 5\n30 PRINT I\n40 I = I + 1\n50 LOOP"
  ],
  "note": None
 },
 "LOOP": {
  "title": "LOOP Statement",
  "brief": "To end a DO...LOOP block, optionally checking a condition.",
  "syntax": "LOOP [WHILE expression | UNTIL expression]",
  "details": [
   [
    "p",
    "LOOP returns control to the DO statement that began the loop. If a condition is given, it is checked after each pass: WHILE continues while the expression is true, UNTIL continues until the expression is true."
   ],
   [
    "p",
    "See DO ... LOOP for the complete description and examples."
   ]
  ],
  "examples": [
   "10 N = 0\n20 DO\n30 N = N + 1\n40 LOOP UNTIL N >= 5"
  ],
  "note": None
 },
 "LPRINT": {
  "title": "LPRINT and LPRINT USING Statements",
  "brief": "To print data at the line printer.",
  "syntax": "LPRINT [list of expressions][;]\nLPRINT USING string exp; list of expressions[;]",
  "details": [
   [
    "p",
    "list of expressions consists of the string or numeric expressions separated by semicolons."
   ],
   [
    "p",
    "string expressions is a string literal or variable consisting of special formatting characters. The formatting characters determine the field and the format of printed strings or numbers."
   ],
   [
    "p",
    "These statements are the same as PRINT and PRINT USING, except that output goes to the line printer. For more information about string and numeric fields and the variables used in them, see the PRINT and PRINT USING statements."
   ],
   [
    "p",
    "The LPRINT and LPRINT USING statements assume that your printer is an 80-character-wide printer."
   ]
  ],
  "examples": [
   "10 LPRINT \"LINE PRINTER TEST\"",
   "10 LPRINT USING \"#### ####\"; 1234"
  ],
  "note": "In this interpreter the line printer is simulated: LPRINT statements are accepted but their output is not displayed or written to a file."
 },
 "LSET": {
  "title": "LSET and RSET Statements",
  "brief": "To move data from memory to a random-file buffer and left justify it in preparation for a PUT statement.",
  "syntax": "LSET string variable = string expression",
  "details": [
   [
    "p",
    "If string expression requires fewer bytes than were fielded to string variable, LSET left-justifies the string in the field (spaces are used to pad the extra positions)."
   ],
   [
    "p",
    "If the string is too long for the field, characters are dropped from the right."
   ],
   [
    "p",
    "To convert numeric values to strings before the LSET statement is used, see the MKI$, MKS$, and MKD$ functions."
   ],
   [
    "p",
    "LSET may also be used with a nonfielded string variable to left-justify a string in the variable's current length. See the RSET statement to right-justify a string."
   ]
  ],
  "examples": [
   "110 A$=SPACE$(20)\n120 LSET A$=N$\nThe string N$ is left-justified in the 20-character field A$."
  ],
  "note": None
 },
 "RSET": {
  "title": "LSET and RSET Statements",
  "brief": "To move data from memory to a random-file buffer and right justify it in preparation for a PUT statement.",
  "syntax": "RSET string variable = string expression",
  "details": [
   [
    "p",
    "If string expression requires fewer bytes than were fielded to string variable, RSET right-justifies the string in the field (spaces are used to pad the extra positions)."
   ],
   [
    "p",
    "If the string is too long for the field, characters are dropped from the right."
   ],
   [
    "p",
    "To convert numeric values to strings before the RSET statement is used, see the MKI$, MKS$, and MKD$ functions."
   ],
   [
    "p",
    "RSET may also be used with a nonfielded string variable to right-justify a string in the variable's current length. See the LSET statement to left-justify a string."
   ]
  ],
  "examples": [
   "110 A$=SPACE$(20)\n120 RSET A$=N$\nThese two statements right-justify the string N$ in a 20-character field. This can be valuable for formatting printed output."
  ],
  "note": None
 },
  "MUSICFILE": {
   "title": "MUSICFILE Instruction",
   "brief": "To assign a Windows .wav, .mp3 or .wma sound file to a numeric variable or array element.",
   "syntax": "MUSICFILE variable, file name\nMUSICFILE array(subscripts), file name\nMUSICFILE variable, stringvar$\nMUSICFILE array(subscripts), stringvar$",
   "details": [
    [
     "p",
     "MUSICFILE binds a Windows .wav, .mp3 or .wma sound file to a numeric variable, or to an element of a numeric array (defined with DIM, or an implicit array used in range). The variable then acts as a music handle: PLAYMUSIC variable plays the file last assigned to it. MUSICFILE itself plays nothing - it only makes the assignment. Assigning the same variable again replaces its music."
    ],
    [
     "p",
     "The file name may be a quoted string (MUSICFILE a,\"my tone.wav\" - use this form for names with spaces or drive paths), a bare name without spaces (MUSICFILE a,tone.wav), or a string variable or string array element holding the file name (MUSICFILE a,x$). A file name in a variable is looked up when the statement runs, so its value may change between executions. The file must exist when MUSICFILE is executed, otherwise a \"File not found\" error occurs."
    ],
    [
     "p",
     "The assignments are cleared by NEW and kept across RUNs. MUSICFILE can be used as a numbered statement inside a program or as an immediate statement at the Ok prompt. Off Windows (or in a headless --nogui run) there is no audio device: MUSICFILE still validates the variable and the file, but PLAYMUSIC does nothing audible, like SOUND off Windows."
    ]
   ],
   "examples": [
    "10 MUSICFILE a,tone.wav\n20 PLAYMUSIC a\n30 END",
    "10 DIM abc(9)\n20 MUSICFILE abc(2),test.wav\n30 PLAYMUSIC abc(2)",
    "10 MUSICFILE a,song.mp3\n20 PLAYMUSIC a\n30 END"
   ],
   "note": "MUSICFILE is an extension of classic GW-BASIC (there is no such instruction in the original). On Windows the file plays through WinMM MCI (mciSendStringA -- the same driver stack Windows Media Player uses), non-blocking, on its own stream independent of SOUND, BEEP and PLAY."
  },
  "PLAYMUSIC": {
   "title": "PLAYMUSIC Instruction",
   "brief": "To play the Windows .wav, .mp3 or .wma file assigned to a variable or array element with MUSICFILE.",
   "syntax": "PLAYMUSIC variable\nPLAYMUSIC array(subscripts)",
   "details": [
    [
     "p",
     "PLAYMUSIC plays the .wav, .mp3 or .wma file that MUSICFILE assigned to the given variable (or array element). The file plays non-blocking: the program continues with the next instruction while the sound plays, so PLAYMUSIC is safe inside game loops. Playing a music file interrupts the music currently playing (one at a time); PLAYMUSIC a again restarts it from the beginning."
    ],
    [
     "p",
     "A variable that was never given a music file with MUSICFILE is a \"No music assigned\" error. An array element that is out of range is the usual \"Subscript out of range\" error, a string variable or array is a \"Type Mismatch\" error, and a file that was deleted after the MUSICFILE is a \"File not found\" error at play time. The file must be a valid .wav, .mp3 or .wma; an unreadable file plays nothing."
    ]
   ],
   "examples": [
    "10 MUSICFILE a,tone.wav\n20 PLAYMUSIC a\n30 END",
    "10 DIM xyz(9)\n20 MUSICFILE xyz(9),go.wav\n30 PLAYMUSIC xyz(9)"
   ],
   "note": "PLAYMUSIC is an extension of classic GW-BASIC (there is no such instruction in the original). It is independent of SOUND, BEEP and PLAY, which keep working while a music file plays."
  },
  "STOPMUSIC": {
   "title": "STOPMUSIC Instruction",
   "brief": "To stop the music file that PLAYMUSIC is currently playing.",
   "syntax": "STOPMUSIC",
   "details": [
    [
     "p",
     "STOPMUSIC takes no arguments. It stops the music file that PLAYMUSIC started. If no music is playing, STOPMUSIC does nothing. The MUSICFILE assignments are not affected: a later PLAYMUSIC starts the music again from the beginning."
    ],
    [
     "p",
     "Music also stops on its own whenever the graphics window is closed, the program terminates (END, an untrapped error, or a break via Ctrl+C/ESC/X), or a new program is RUN. A STOP does not stop the music: the program's world (including the playing file) is frozen while the program is stopped, so the music keeps playing at the prompt and is still going when CONT resumes the program - STOPMUSIC is how you quiet it, at the prompt or while running."
    ]
   ],
   "examples": [
    "10 MUSICFILE a,tone.wav\n20 PLAYMUSIC a\n30 SLEEP 2\n40 STOPMUSIC\n50 PRINT \"quiet now\"\n60 END"
   ],
   "note": "STOPMUSIC is an extension of classic GW-BASIC (there is no such instruction in the original). It only affects the PLAYMUSIC music stream; SOUND, BEEP and PLAY are independent."
  },
  "TYPE": {
   "title": "TYPE ... END TYPE Statement",
   "brief": "To define a new user-defined variable type (a named record of fields).",
   "syntax": "TYPE type name[(field list)]\n   field list: field [AS data type][(length)] [,field [AS data type][(length)]] ...\nEND TYPE",
   "details": [
   [
    "p",
    "TYPE declares a new user-defined variable type: a named record made up of fields, each of which is an independent variable with its own data type. The type name must not be the same as any other variable or array name, and it is not used like a normal variable - variables of the type are created and referenced with the & (ampersand) symbol in front of the name."
   ],
   [
    "p",
    "A TYPE statement is written on one line:  TYPE type name (field1 [AS data type] [(length)] ,field2 [AS data type] [(length)] , ... )  Each field's data type is optional and defaults to SINGLE; the length in parentheses is required for string fields (AS STRING) and gives the number of characters the string holds. The allowed data types are INTEGER, SINGLE, DOUBLE, STRING, and LONG."
   ],
   [
    "p",
    "In addition to the one-line form, this interpreter also accepts the multi-line form, where the field list is written one field per line and the declaration is closed with END TYPE. A TYPE line that already contains a parenthesis is treated as the one-line form."
   ],
   [
    "p",
    "Variables of the type are declared by putting an ampersand in front of the name (for example  A&  after  TYPE A (X AS INTEGER) ), and their fields are read and written with a dot:  A&.X = 5. The total size of the record is the sum of the sizes of its fields."
   ]
  ],
  "examples": [
   "10 TYPE EMP (NAME AS STRING * 20, DEPT AS INTEGER, SALARY AS SINGLE)\n20 A&.NAME = \"JOHN\"\n30 A&.DEPT = 12\n40 A&.SALARY = 42000\n50 PRINT A&.NAME, A&.DEPT, A&.SALARY",
   "10 TYPE POINT (X AS INTEGER, Y AS INTEGER)\n20 END TYPE\n30 P&.X = 10 : P&.Y = 20 : PRINT P&.X, P&.Y"
  ],
  "note": "END TYPE (the multi-line form) is an extension of classic GW-BASIC; the one-line TYPE form is standard."
 },
 "ENDIF": {
   "title": "ENDIF Statement",
   "brief": "To end a multi-line IF ... THEN block (extension).",
   "syntax": "IF expression THEN\n   ... statements ...\n[ELSE\n   ... statements ...]\nENDIF",
   "details": [
   [
    "p",
    "Classic GW-BASIC requires the whole IF ... THEN ... ELSE on a single line. ENDIF lets you write the IF block across several lines: the IF ... THEN line opens the block, the statements that follow run when the expression is true, an optional ELSE line (with its own statements) runs when it is false, and ENDIF closes the block. When ENDIF is reached, execution continues with the line after it."
   ],
   [
    "p",
    "Blocks nest by line: an IF ... THEN on its own line opens a scope that the next unmatched ELSE or ENDIF at the same level closes. ENDIF is not needed when the ELSE clause is on the same line as the THEN (the classic one-line form still works)."
   ]
  ],
  "examples": [
   "10 IF A > B THEN\n20   PRINT A\n30 ELSE\n40   PRINT B\n50 ENDIF",
   "10 IF X > 0 THEN\n20   GOSUB 1000\n30 ENDIF\n40 PRINT \"done\""
  ],
  "note": "ENDIF is an extension of classic GW-BASIC (there is no such statement in the original)."
 },
 "MUSICVOLUME": {
   "title": "MUSICVOLUME Instruction",
   "brief": "To set the volume of the music file that PLAYMUSIC plays.",
   "syntax": "MUSICVOLUME number",
   "details": [
    [
     "p",
     "MUSICVOLUME sets the volume of the music stream that PLAYMUSIC started. number is an integer from 0 to 100: 100 is the loudest, 0 is silent but the music keeps playing. A number outside the range is an \"Illegal function call\" error. Set while music is playing, the volume applies immediately; set when nothing is playing, the value is stored and applied the next time PLAYMUSIC starts."
    ],
    [
     "p",
     "MUSICVOLUME changes only the volume of the music stream. It does not touch the system volume, and SOUND, BEEP and PLAY are independent of it. The effective loudness is the system volume times the MUSICVOLUME percentage: 50 with the system volume at half is about a quarter of the maximum loudness. Some playback devices do not support volume control (on some systems, .wav files): for those, the music plays at the system volume whatever MUSICVOLUME says."
    ]
   ],
   "examples": [
    "10 MUSICFILE a,tone.wav\n20 PLAYMUSIC a\n30 SLEEP 1\n40 MUSICVOLUME 0\n50 SLEEP 1\n60 MUSICVOLUME 100\n70 SLEEP 2\n80 STOPMUSIC"
   ],
   "note": "MUSICVOLUME is an extension of classic GW-BASIC (there is no such instruction in the original). It only affects the PLAYMUSIC music stream; SOUND, BEEP and PLAY are independent."
  }
}


# Operators usable inside expressions.  The logical operator entries are
# taken from the "Logical Operators" section of the GW-BASIC User's Guide
# chapter 6 page in the manual/ subfolder (Table 6.2).
HELP_OPERATORS = {
 "MOD": {
  "title": "MOD Operator",
  "brief": "To return the remainder of the integer division of two numeric expressions.",
  "syntax": "expression MOD expression",
  "details": [
   [
    "p",
    "MOD (modulus arithmetic) returns the integer remainder left after the integer division of the first expression by the second. Both expressions are rounded to integers first, then the remainder of the integer division is returned. In the order of evaluation, MOD is performed just after the integer-division operator (\\)."
   ],
   [
    "p",
    "The remainder takes the sign of the first expression, so for example -7 MOD 3 is -1, not 2. If the second expression is zero, \"Division by zero\" is printed, machine infinity with the sign of the first expression is supplied as the result, and execution continues. The INT and FIX functions are also useful in modulus arithmetic."
   ]
  ],
  "examples": [
   "10 X = 10.4 MOD 4\n20 PRINT X\n' Result is 2: 10 rounds to 10, 4 to 4, and 10 \\ 4 = 2 with remainder 2.",
   "10 X = 25.68 MOD 6.99\n20 PRINT X\n' Result is 5: 26 \\ 7 = 3 with remainder 5 (25.68 rounds to 26, 6.99 to 7)."
  ],
  "note": None
 },
 "\\": {
  "title": "\\ Operator (Integer Division)",
  "brief": "To perform integer division of two numeric expressions, discarding any fractional part.",
  "syntax": "expression \\ expression",
  "details": [
   [
    "p",
    "The backslash (\\) is the integer-division operator. Both expressions are rounded to integers first, then the quotient is truncated to an integer (the fractional part is discarded). In the order of evaluation, \\ is performed just before MOD and after the ordinary floating-point operators * and /."
   ],
   [
    "p",
    "If the second expression is zero, \"Division by zero\" is printed, machine infinity with the sign of the first expression is supplied as the result, and execution continues. Use the floating-point division operator (/) when you want the fractional part of the result."
   ]
  ],
  "examples": [
   "10 X = 10 \\ 4\n20 PRINT X\n' Result is 2: the fractional part of 10/4 (2.5) is discarded.",
   "10 X = 25.68 \\ 6.99\n20 PRINT X\n' Result is 3: 25.68 rounds to 26 and 6.99 to 7, and 26 \\ 7 = 3."
  ],
  "note": None
 },
 "AND": {
  "title": "AND Operator",
  "brief": "To return the logical AND of two numeric expressions, compared bit by bit.",
  "syntax": "expression AND expression",
  "details": [
   [
    "p",
    "AND is a logical operator. The logical operators convert their operands to signed two's complement integers and perform the operation in bits; that is, each bit of the result is determined by the corresponding bits in the two operands. AND (conjunction) sets a result bit to 1 only when both corresponding bits are 1, and to 0 otherwise. In Boolean terms, X AND Y is true only when both X and Y are true."
   ],
   [
    "table",
    "X | Y | X AND Y\nT | T | T\nT | F | F\nF | T | F\nF | F | F"
   ],
   [
    "p",
    "The outcome of a logical operation is a bitwise result which is either true (not zero) or false (zero). If both operands are supplied as 0 or -1, logical operators return 0 or -1."
   ]
  ],
  "examples": [
   "10 X = 1 AND 0\n20 PRINT X\n' Result is 0 (false): 1 is true and 0 is false, and\n' true AND false is false."
  ],
  "note": "AND reduces its operands to their truth value (nonzero = true, 0 = false) and applies the bitwise AND, returning 0 or -1. Multi-bit operands therefore normalize: 1 AND 0 = 0."
 },
 "OR": {
  "title": "OR Operator",
  "brief": "To return the logical OR of two numeric expressions, compared bit by bit.",
  "syntax": "expression OR expression",
  "details": [
   [
    "p",
    "OR is a logical operator. The logical operators convert their operands to signed two's complement integers and perform the operation in bits; that is, each bit of the result is determined by the corresponding bits in the two operands. OR (disjunction) sets a result bit to 1 when either (or both) of the corresponding bits is 1, and to 0 only when both are 0. In Boolean terms, X OR Y is true when at least one of X and Y is true."
   ],
   [
    "table",
    "X | Y | X OR Y\nT | T | T\nT | F | T\nF | T | T\nF | F | F"
   ],
   [
    "p",
    "The outcome of a logical operation is a bitwise result which is either true (not zero) or false (zero). If both operands are supplied as 0 or -1, logical operators return 0 or -1."
   ]
  ],
  "examples": [
   "10 X = 1 OR 0\n20 PRINT X\n' Result is -1 (true): 1 is true and 0 is false, and\n' true OR false is true."
  ],
  "note": "OR reduces its operands to their truth value (nonzero = true, 0 = false) and applies the bitwise OR, returning 0 or -1. Multi-bit operands therefore normalize: 1 OR 0 = -1."
 },
 "XOR": {
  "title": "XOR Operator",
  "brief": "To return the logical XOR (exclusive OR) of two numeric expressions, compared bit by bit.",
  "syntax": "expression XOR expression",
  "details": [
   [
    "p",
    "XOR is a logical operator. The logical operators convert their operands to signed two's complement integers and perform the operation in bits; that is, each bit of the result is determined by the corresponding bits in the two operands. XOR (exclusive or) sets a result bit to 1 when the two corresponding bits differ, and to 0 when they are the same. In Boolean terms, X XOR Y is true when exactly one of X and Y is true."
   ],
   [
    "table",
    "X | Y | X XOR Y\nT | T | F\nT | F | T\nF | T | T\nF | F | F"
   ],
   [
    "p",
    "The outcome of a logical operation is a bitwise result which is either true (not zero) or false (zero). If both operands are supplied as 0 or -1, logical operators return 0 or -1."
   ]
  ],
  "examples": [
   "10 X = 1 XOR 0\n20 PRINT X\n' Result is -1 (true): 1 is true and 0 is false, and the values\n' differ, so true XOR false is true."
  ],
  "note": "XOR reduces its operands to their truth value (nonzero = true, 0 = false) and applies the bitwise XOR, returning 0 or -1. Multi-bit operands therefore normalize: 1 XOR 0 = -1."
 },
 "NOT": {
  "title": "NOT Operator",
  "brief": "To return the logical NOT of a numeric expression, inverted bit by bit.",
  "syntax": "NOT expression",
  "details": [
   [
    "p",
    "NOT is a logical operator that takes a single expression. As with the other logical operators, the operand is converted to a signed two's complement integer and the operation is performed in bits: each bit of the result is the complement (inversion) of the corresponding bit of the operand. In Boolean terms, NOT X is true when X is false, and false when X is true."
   ],
   [
    "table",
    "X | NOT X\nT | F\nF | T"
   ],
   [
    "p",
    "Because NOT is a bitwise complement, NOT 0 is -1 (all bits 1) and NOT -1 is 0 (all bits 0). The outcome is a bitwise result which is either true (not zero) or false (zero)."
   ]
  ],
  "examples": [
   "10 X = NOT 0\n20 PRINT X\n' Result is -1 (true): 0 is false, and NOT false is true."
  ],
  "note": "NOT reduces its operand to its truth value (nonzero = true, 0 = false) and applies the bitwise NOT, returning 0 or -1. NOT 0 = -1 and NOT -1 = 0."
 },
 "EQV": {
  "title": "EQV Operator",
  "brief": "To return the logical equivalence of two numeric expressions, compared bit by bit.",
  "syntax": "expression EQV expression",
  "details": [
   [
    "p",
    "EQV is a logical operator. The logical operators convert their operands to signed two's complement integers and perform the operation in bits; that is, each bit of the result is determined by the corresponding bits in the two operands. EQV (equivalence) sets a result bit to 1 when the two corresponding bits are equal, and to 0 when they differ."
   ],
   [
    "table",
    "X | Y | X EQV Y\nT | T | T\nT | F | F\nF | T | F\nF | F | T"
   ],
   [
    "p",
    "The outcome of a logical operation is a bitwise result which is either true (not zero) or false (zero). If both operands are supplied as 0 or -1, logical operators return 0 or -1."
   ]
  ],
  "examples": [
   "10 X=1 EQV 0\n20 PRINT X\n' Result is 0 (false): 1 is true and 0 is false, and\n' true EQV false is false (Table 6.2)."
  ],
  "note": "EQV reduces its operands to their truth value (nonzero = true, 0 = false) and applies Table 6.2, returning 0 or -1. Multi-bit operands therefore normalize: 1 EQV 0 = 0."
 },
 "IMP": {
  "title": "IMP Operator",
  "brief": "To return the logical implication of two numeric expressions, compared bit by bit.",
  "syntax": "expression IMP expression",
  "details": [
   [
    "p",
    "IMP is a logical operator. The logical operators convert their operands to signed two's complement integers and perform the operation in bits; that is, each bit of the result is determined by the corresponding bits in the two operands. IMP (implication) sets a result bit to 0 only when the first operand's bit is 1 and the second operand's bit is 0; otherwise the result bit is 1. In Boolean terms, X IMP Y is the same as NOT X OR Y."
   ],
   [
    "table",
    "X | Y | X IMP Y\nT | T | T\nT | F | F\nF | T | T\nF | F | T"
   ],
   [
    "p",
    "The outcome of a logical operation is a bitwise result which is either true (not zero) or false (zero). If both operands are supplied as 0 or -1, logical operators return 0 or -1."
   ]
  ],
  "examples": [
   "10 X=1 IMP 0\n20 PRINT X\n' Result is 0 (false): 1 is true and 0 is false, and\n' true IMP false is false (Table 6.2)."
  ],
  "note": "IMP reduces its operands to their truth value (nonzero = true, 0 = false) and applies Table 6.2, returning 0 or -1. Multi-bit operands therefore normalize: 1 IMP 0 = 0."
 },
}


class MorePager:
    """Output wrapper that pauses when the display is about to fill up.

    Used for long REPL output such as HELP.  When the output reaches the
    bottom of the display, "Pausing" is printed and the interpreter waits
    for the user to press the space or Enter key before continuing.  It
    pauses as many times as needed until the output is complete.
    """

    def __init__(self, out, input_func=None):
        self.out = out
        self.input_func = input_func if input_func is not None else input
        # Only pause in an interactive terminal (never when piped).
        try:
            self.enabled = sys.stdout.isatty()
        except Exception:
            self.enabled = False
        size = shutil.get_terminal_size((80, 25))
        self.lines_total = max(size.lines, 4)
        self.count = 0  # lines written since the last pause

    def __call__(self, text, newline=True):
        full = text + ('\n' if newline else '')
        n = full.count('\n')
        if n > 0 and self.enabled and self.count + n >= self.lines_total:
            # Pause before the line that would land on the bottom row so
            # the "Pausing" message itself is visible on the last row.
            self.count = 0
            self.out("Pausing")
            try:
                self.input_func()
            except EOFError:
                pass
            except KeyboardInterrupt:
                # Ctrl+C while paused: stop paging for the remaining
                # output instead of exiting the interpreter.
                self.enabled = False
        self.count += n
        self.out(text, newline)


def _help_first_sentence(text):
    text = text.strip()
    if '...' in text:
        return text
    i = text.find('. ')
    if i > 0:
        return text[:i + 1]
    return text


def _help_wrap(text, indent):
    """Word-wrap a paragraph of help text to a fixed width."""
    words = text.split()
    if not words:
        return []
    limit = 72 - len(indent)
    lines = []
    cur = ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > limit:
            lines.append(cur)
            cur = w
        else:
            cur = cur + ' ' + w if cur else w
    if cur:
        lines.append(cur)
    return [indent + l for l in lines]


def _print_help_entry(out, entry):
    title = entry['title']
    out(title)
    out('=' * min(len(title), 72))
    out('')
    for l in _help_wrap(entry['brief'], ''):
        out(l)
    out('')
    out('Syntax:')
    for line in entry['syntax'].splitlines():
        out('    ' + line)
    out('')
    for kind, text in entry['details']:
        if kind == 'h':
            out(text)
            out('')
            continue
        if kind == 'p':
            for l in _help_wrap(text, '    '):
                out(l)
            out('')
        else:  # 'pre' or 'table'
            for line in text.splitlines():
                out('    ' + line)
            out('')
    if entry['examples']:
        out('Examples:')
        for ex in entry['examples']:
            for line in ex.splitlines():
                out('    ' + line)
            out('')
    if entry.get('note'):
        out('Note:')
        for l in _help_wrap(entry['note'], '    '):
            out(l)


def _help_brief(entry):
    return _help_first_sentence(entry['brief'])


def print_help(out):
    out('HELP')
    out('====')
    out('')
    out('Commands (type at the Ok prompt):')
    for name in sorted(HELP_COMMANDS):
        if name in GRAPHICS_TOPICS:
            continue
        out('  %-8s %s' % (name, _help_brief(HELP_COMMANDS[name])))
    out('')
    out('Instructions (BASIC statements):')
    for name in sorted(HELP_INSTRUCTIONS):
        if name in GRAPHICS_TOPICS:
            continue
        out('  %-10s %s' % (name, _help_brief(HELP_INSTRUCTIONS[name])))
    out('')
    out('Functions:')
    for name in sorted(HELP_FUNCTIONS):
        if name in GRAPHICS_TOPICS:
            continue
        out('  %-10s %s' % (name, _help_brief(HELP_FUNCTIONS[name])))
    out('')
    out('Operators (used in expressions):')
    for name in sorted(HELP_OPERATORS):
        if name in GRAPHICS_TOPICS:
            continue
        out('  %-10s %s' % (name, _help_brief(HELP_OPERATORS[name])))
    out('')
    out('Graphics:')
    out('')
    _print_graphics_section(out)
    out('')
    out('Type HELP <command, instruction, function, or operator> for a detailed description and examples.')
    out('Type HELP <graphics topic> for details on any of the graphics entries above.')


def _print_graphics_section(out):
    """Print the Graphics section of the HELP index.

    Entries are grouped into sub-sections: drawing primitives, colors,
    viewports and windows, image transfer, and graphics functions.  Each
    sub-section lists only the names that actually exist in the help
    tables; empty sub-sections are skipped.
    """
    groups = [
        ("Screen modes", ["SCREEN", "SCREENSIZE", "TEXTSIZE",
                           "TEXTFONT", "TEXTROTATE", "WCLOSE"]),
        ("Drawing primitives", ["LINE", "CIRCLE", "DRAW", "PAINT",
                                 "PSET", "PRESET", "INK", "CURSOR"]),
        ("Colors", ["COLOR", "PALETTE"]),
        ("Viewports and windows", ["VIEW", "WINDOW"]),
        ("Graphics functions", ["POINT", "RGB", "XSZ", "YSZ"]),
    ]
    all_tables = [HELP_COMMANDS, HELP_INSTRUCTIONS, HELP_FUNCTIONS, HELP_OPERATORS]
    for label, names in groups:
        present = [n for n in names if any(n in t for t in all_tables)]
        if not present:
            continue
        out('  ' + label + ':')
        for name in present:
            for t in all_tables:
                if name in t:
                    out('    %-12s %s' % (name, _help_brief(t[name])))
                    break
        out('')


def show_help_topic(out, topic):
    key = topic.upper()
    key = COMMAND_ALIASES.get(key, key)
    if key in HELP_COMMANDS:
        _print_help_entry(out, HELP_COMMANDS[key])
        return
    if key in HELP_INSTRUCTIONS:
        _print_help_entry(out, HELP_INSTRUCTIONS[key])
        return
    if key in HELP_FUNCTIONS:
        _print_help_entry(out, HELP_FUNCTIONS[key])
        return
    if key in HELP_OPERATORS:
        _print_help_entry(out, HELP_OPERATORS[key])
        return
    out("No help for '%s'." % topic)
    out('Type HELP for the list of commands and instructions.')


# --------------------------------------------------------------------------- #
#  Ok-prompt line reader
# --------------------------------------------------------------------------- #
# The Ok prompt uses the original plain input() while no window is open -
# a pure interception, nothing is replaced.  When a window IS open the
# prompt switches to a key-at-a-time reader (mirroring the LEDIT editor)
# so the graphics window can be pumped between keystrokes.  A window left
# open by a stopped/finished program therefore stays live at the prompt:
# its last frame keeps showing, ESC/X closes it (Screen.pump destroys it
# at this clean Python boundary), and a console Ctrl+C is a plain
# character the editor turns into KeyboardInterrupt — which
# _repl_session swallows instead of letting it race the interpreter.
# Stopped at a STOP (program awaiting CONT) with a window open: the prompt
# stays on the key-at-a-time reader (the window must keep pumping so ESC/X
# stay live), but the prompt's draws and its key reads go to the console -
# the console is the monitor for the debugging session (see
# IoDevice._stopped).  CONT clears the stopped flag, and the window takes
# the monitor back with the first resumed line.

def _console_key_pending(strict=False):
    """True if a keyboard character is waiting in the console input queue.

    `strict` selects the gate for the two very different situations:

    strict (a graphics window is open): on Windows, msvcrt.kbhit().  The
    caller pairs the gate with a BLOCKING console read while the window
    must keep pumping, so the gate must fire only when a real character
    can actually be consumed: kbhit reports only keyboard input, so the
    FOCUS event the console receives the moment the window steals focus
    does not count.  (The fail-open peek gate counted that event and
    sent the reader into a blocking getwch() on every poll - which sat
    there while the user typed into the window, freezing it.)  When
    kbhit itself fails, report False: the window's own keyboard still
    works, and the alternative - a blocking read on a queue that may be
    empty - is exactly the freeze we are avoiding.

    non-strict (no window): the original Windows path,
    PeekConsoleInputW.  That is the battle-tested console-only gate:
    FOCUS/MOUSE events count too, but the blocking reader consumes and
    discards them (it returns None for non-key records), so they can
    never wedge it.  A failed peek reports True - the caller then does a
    blocking read, which keeps input working.  This path must never
    depend on kbhit: on some consoles kbhit misbehaves (or stdin is not
    a console at all) and a gate that answers False there kills console
    input entirely.

    On Unix (both modes): a zero-timeout select on stdin.
    """
    if os.name == 'nt':
        if strict:
            try:
                import msvcrt
                return msvcrt.kbhit()
            except Exception:
                return False  # never block on a queue that may be empty
        try:
            import ctypes
            k32 = ctypes.windll.kernel32
            k32.GetStdHandle.restype = ctypes.c_void_p
            handle = k32.GetStdHandle(-10)  # STD_INPUT_HANDLE
            if not handle:
                return False
            buf = ctypes.create_string_buffer(4096)
            n = ctypes.c_ulong(0)
            if k32.PeekConsoleInputW(ctypes.c_void_p(handle), buf, 64,
                                     ctypes.byref(n)):
                return n.value > 0
            return True  # peek failed: let a blocking read handle it
        except Exception:
            return True
    try:
        import select
        return bool(select.select([sys.stdin], [], [], 0.0)[0])
    except Exception:
        return False


def _prompt_raw_console():
    """Switch the console to raw mode for the Ok-prompt line editor.

    Windows: disable processing / line input / echo / mouse so keys are
    read one at a time and Ctrl+C arrives as a plain 0x03 character
    (no CTRL_C_EVENT).  Unix: termios cbreak.  Returns a zero-argument
    callable that restores the previous mode, or None when the console
    could not be switched (the caller then uses the plain input path, so
    the console never ends up half-raw and broken for the next reader).
    """
    if os.name == 'nt':
        try:
            import ctypes
            k32 = ctypes.windll.kernel32
            k32.GetStdHandle.restype = ctypes.c_void_p
            handle = k32.GetStdHandle(-10)  # STD_INPUT_HANDLE
            if handle:
                mode = ctypes.c_ulong(0)
                if k32.GetConsoleMode(ctypes.c_void_p(handle),
                                      ctypes.byref(mode)):
                    saved = mode.value

                    def restore():
                        k32.SetConsoleMode(ctypes.c_void_p(handle), saved)

                    if not k32.SetConsoleMode(ctypes.c_void_p(handle), 0):
                        return None
                    return restore
        except Exception:
            pass
        return None
    try:
        import termios
        import tty
        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        tty.setcbreak(fd)

        def restore():
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

        return restore
    except Exception:
        return None


def _monitor_line_redraw(screen, row, col, prefix, buf, pos):
    """Redraw an editable line on the monitor (the open graphics window),
    anchored at character cell (row, col).  The whole line is rewritten on
    every change and a block cursor marks `pos` (the character under it is
    drawn with the colors swapped) - the hardware way of showing a cursor
    on the old monitor.  `pos` is relative to the buffer (after `prefix`),
    like the console editors.
    """
    text = prefix + ''.join(buf)
    caret = len(prefix) + pos
    fg, bg = screen.fg, screen.bg
    screen.locate(row, col)
    # Wipe whatever an earlier, longer draw left behind...
    screen.print_text(' ' * (len(text) + 1), newline=False)
    screen.locate(row, col)
    # ...and redraw the line with the block cursor at `pos`.
    for i, ch in enumerate(text):
        if i == caret:
            screen.fg, screen.bg = bg, fg
            screen.print_text(ch, newline=False)
            screen.fg, screen.bg = fg, bg
        else:
            screen.print_text(ch, newline=False)
    screen.fg, screen.bg = bg, fg
    screen.print_text(text[caret] if caret < len(text) else ' ',
                      newline=False)
    screen.fg, screen.bg = fg, bg


def _monitor_line_commit(screen, row, col, prefix, buf):
    """Submit an editable line on the monitor: redraw it at its anchor and
    move the cursor to a fresh line (where the next prompt will appear)."""
    screen.locate(row, col)
    screen.print_text(prefix + ''.join(buf) + '\n', newline=False)


def _prompt_readline(repl, prefix=''):
    """Read one Ok-prompt line.

    With no window open the line is read with the original plain input()
    call (the console's own editor) - the middle layer merely intercepts
    the call, it does not replace the mechanism.  While the graphics
    window is open the prompt lives on the monitor (the
    window): the line is drawn on the text page with a block cursor and the
    keys come from the window's keyboard.  Keys typed at the console are
    just as good - whichever keyboard the user is typing on wins - and if
    the window closes while a line is being typed (ESC / close box) the
    editor seamlessly continues on the console.

    ENTER submits the line; ESC clears it (the window's own ESC binding
    closes the window when the window has the focus); Ctrl+C raises
    KeyboardInterrupt (the REPL swallows it and re-prompts); Ctrl+Z/EOF
    raises EOFError (the REPL exits); LEFT/RIGHT/HOME/END/BACKSPACE/
    DELETE/TAB and characters edit the line.  Returns the submitted text.
    """
    io = repl.io
    if not io.window_live() or not sys.stdin.isatty():
        # No window open (or no interactive console at all): the original
        # plain input() path, exactly as the interpreter has always read
        # the Ok prompt.  No raw console mode, no key polling: the
        # console keeps its own echo / line editing / Ctrl+C handling and
        # its input mode is never touched, so a program's own INPUT right
        # afterwards works exactly as it always did.  The middle layer is
        # a pure interception: with no window there is nothing to
        # redirect to, and the original call runs unmodified.
        if prefix:
            io.write(prefix, newline=False)
        return repl.input_func()
    # A window is open: the line must be read key at a time so the window
    # can be pumped between keystrokes (ESC / close box can close it
    # mid-line), which the plain input() cannot do.
    restore = _prompt_raw_console()
    if restore is None:
        # The console could not be switched to raw mode: use the plain
        # input path rather than a half-raw console (the open window
        # simply is not pumped between keystrokes and shows its last
        # frame while the line is read).
        if prefix:
            io.write(prefix, newline=False)
        return repl.input_func()
    try:
        _enable_vt_processing()
        flush = sys.stdout.flush
        buf = []
        pos = 0
        # Anchor of the prompt line on the monitor, captured once when the
        # first window draw happens (the editor redraws in place while the
        # screen's own cursor wanders with every draw).
        anchor = [None, None]

        def draw_console():
            # Clear the line, write the prefix + buffer, then reposition
            # the cursor to `pos` (same trick as the LEDIT editor).
            text = prefix + ''.join(buf)
            cursor_text = prefix + ''.join(buf[:pos])
            io.write('\x1b[2K\x1b[G' + text + '\x1b[G' + cursor_text,
                     newline=False)
            flush()

        def draw():
            # Stopped at a STOP: draw on the console even while the window
            # is still open (the console is the monitor; see _stopped).
            if io.window_live() and not io._stopped():
                if anchor[0] is None:
                    screen = repl.interpreter.screen
                    if screen.is_text():
                        pc, pr = screen.cols, screen.rows
                    else:
                        pc, pr = screen._gfx_text_page()
                    anchor[0] = min(screen.cursor_row, pr - 1)
                    anchor[1] = min(screen.cursor_col, pc - 1)
                _monitor_line_redraw(repl.interpreter.screen, anchor[0],
                                     anchor[1], prefix, buf, pos)
            else:
                draw_console()

        def read_key():
            # A key typed while the window is focused sits in the system
            # key queue (the window's <Key> adapter feeds it); a key typed
            # at the console arrives through the console reader.  Whichever
            # the user is typing on wins (see IoDevice for the shapes).
            # Stopped at a STOP: the console is the monitor, so the
            # window's keyboard is ignored (the window is still pumped
            # below, so its ESC / close box stay live).
            key = None if io._stopped() else io.pop_window_key()
            if key is not None:
                return key
            # Strict only while the window is live: with no window the
            # original fail-open gate applies and a blocking read is safe
            # (nothing is left to freeze - see _console_key_pending).
            if _console_key_pending(io.window_live()):
                if os.name == 'nt':
                    return _read_key()
                fd = sys.stdin.fileno()
                ch = os.read(fd, 1)
                if not ch:
                    raise EOFError
                return _decode_key_byte(ch[0], fd)
            # No key yet: keep the graphics window alive between
            # keystrokes (this is also where a pending ESC/X close of the
            # window gets destroyed), then wait briefly.
            try:
                repl.interpreter.screen.pump()
            except Exception:
                pass
            time.sleep(0.02)
            return None

        draw()
        while True:
            try:
                key = read_key()
            except (KeyboardInterrupt, EOFError):
                raise
            except Exception:
                key = None  # can't read the key right now: keep waiting
            if key is None:
                continue
            if key == 'enter':
                if io.window_live() and anchor[0] is not None:
                    _monitor_line_commit(repl.interpreter.screen,
                                         anchor[0], anchor[1], prefix, buf)
                else:
                    io.write('\n', newline=False)
                    flush()
                return ''.join(buf)
            if key == 'ctrl_c':
                raise KeyboardInterrupt
            if key == 'eof':
                raise EOFError
            if key == 'escape':
                buf = []
                pos = 0
            elif key == 'left':
                if pos > 0:
                    pos -= 1
            elif key == 'right':
                if pos < len(buf):
                    pos += 1
            elif key == 'home':
                pos = 0
            elif key == 'end':
                pos = len(buf)
            elif key == 'backspace':
                if pos > 0:
                    del buf[pos - 1]
                    pos -= 1
            elif key == 'delete':
                if pos < len(buf):
                    del buf[pos]
            elif key == 'tab':
                buf.insert(pos, '\t')
                pos += 1
            elif len(key) == 1:
                # Printable character: insert at the cursor (insert mode).
                buf.insert(pos, key)
                pos += 1
            # Any other key (up/down/pageup/pagedown) is ignored.
            draw()
    except (KeyboardInterrupt, EOFError):
        # Clean up the editor line before propagating: the REPL handler
        # continues from a fresh line.
        if io.window_live() and anchor[0] is not None:
            _monitor_line_commit(repl.interpreter.screen, anchor[0],
                                 anchor[1], prefix, buf)
        else:
            io.write('\x1b[2K\x1b[G\n', newline=False)
            flush()
        raise
    finally:
        restore()


def main():
    args = sys.argv[1:]
    # The graphics window is created lazily the moment a program executes a
    # graphics SCREEN command, so no --gui flag is needed for a graphics
    # program to show a window.  --nogui forces headless (e.g. for test
    # suites); --gui is accepted for compatibility but no longer required.
    # gui means "a window is allowed": True by default, False only with
    # --nogui.  (It is passed to Screen as gui_allowed; a False default here
    # would suppress the window for every normal run.)
    gui = '--nogui' not in args
    args = [a for a in args if a not in ('--gui', '--nogui')]
    if len(args) > 0:
        repl = BasicREPL(gui=gui)
        try:
            repl.load_file(args[0])
            repl.run()
        except BasicError as e:
            # A load-time error that escaped load_file's own guards is
            # reported like any other command error.
            repl._emit("Error: %s" % e)
        except Exception as e:
            # Last-resort guard: an unexpected internal failure during a
            # file run must not dump a raw Python traceback; report it
            # plainly, mirroring the Ok-prompt safety net in
            # _repl_session.
            repl._emit("Error: %s: %s" % (type(e).__name__, e))
            sys.exit(1)
        return
    repl = BasicREPL(gui=gui)
    # Startup: clear the screen immediately, before the first intro text is
    # written - the same VT clear+home CLS uses on the virtual screen (the
    # console is the monitor while no window is open).  VT processing is
    # enabled first or Windows would print the escape bytes as garbage; the
    # call is a no-op on other platforms and the first prompt read repeats
    # it harmlessly.
    _enable_vt_processing()
    repl._emit("\033[2J\033[H", False)
    repl._emit("GW-BASIC enhanced for Windows")
    repl._emit("Type HELP for commands, BYE to quit.\n\nReady\n\n")
    try:
        _repl_session(repl)
    except KeyboardInterrupt:
        # Safety net: a Ctrl+C that escaped every specific handler
        # (e.g. landing mid-command) must not lose the program. Return
        # to the Ok prompt; a second unhandled Ctrl+C will exit.
        repl._emit("\n")
        _repl_session(repl)


def _repl_session(repl):
    while True:
        # AUTO mode (manual AUTO): print the next line number as the prompt
        # and store the input with that number prepended; an asterisk after
        # the number warns that the line is already in use.
        prefix = ''
        if repl.auto is not None:
            num, inc = repl.auto
            prefix = '%d%s ' % (num, '*' if num in repl.program else '')
        try:
            line = _prompt_readline(repl, prefix)
        except EOFError:
            repl._emit("")
            break
        except KeyboardInterrupt:
            # Ctrl+C at the Ok prompt: ignore it and stay in the interpreter.
            # It also terminates AUTO mode (manual AUTO).
            if repl.auto is not None:
                repl.auto = None
                repl.io.write('\n', newline=False)
            continue
        if repl.auto is not None:
            num, inc = repl.auto
            text = line.strip()
            if not text:
                # Return with no text terminates AUTO mode without storing
                # the prompted line number.
                repl.auto = None
                repl.io.write('\n', newline=False)
                continue
            elif text.isdigit():
                # An explicit line number with no text stores a blank line
                # at that number (it is not the DELETE-line command in AUTO
                # mode); the counter continues from the number just stored.
                repl.program[int(text)] = []
                repl.source.pop(int(text), None)
                repl.dirty = True
                repl.update_interpreter()
                repl.auto = (int(text), inc)
            elif text[0].isdigit():
                # An explicit line number overrides the auto number; the
                # counter continues from the number just stored.
                explicit = int(text.split(None, 1)[0])
                repl.auto = (explicit, inc)
                repl.load_line(text)
            else:
                repl.load_line('%d %s' % (num, text))
            repl.auto = (repl.auto[0] + inc, inc)
            continue  # no "Ready" in AUTO mode: the next prompt follows
        line = line.strip()
        if not line:
            continue
        upper = line.upper()
        if upper in ('BYE', 'EXIT', 'QUIT'):
            # Close any graphics window so quitting does not leave one behind.
            repl.interpreter.screen.close()
            break
        elif upper == 'HELP' or upper.startswith('HELP '):
            parts = line.split(None, 1)
            # Page pauses wait for a key through the I/O middle layer, so
            # HELP works with the program's window open too.
            pager = MorePager(repl._emit, repl.io.read_line)
            if len(parts) > 1 and parts[1].strip():
                show_help_topic(pager, parts[1].strip())
            else:
                print_help(pager)
        elif upper == 'NEW':
            repl.new()
        elif upper == 'AUTO' or upper.startswith('AUTO '):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.auto_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper == 'CLEAR' or upper.startswith('CLEAR '):
            parts = line.split(None, 1)
            # CLEAR takes no options: anything after the command name is a
            # syntax error (clear_command() raises BasicError on it).
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.clear_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper.startswith('RUN'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            repl._emit("")  # newline after the run command, before program output
            try:
                repl.run_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
            except Exception as e:
                # Safety net, mirroring the immediate-mode branch: an
                # unexpected internal failure must not kill the
                # interpreter with a raw traceback.
                repl._emit("Error: %s: %s" % (type(e).__name__, e))
        elif upper.startswith('COMPILE'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.compile_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
            except Exception as e:
                # Safety net: a compiler failure must not kill the
                # interpreter; report it and re-prompt.
                repl._emit("Error: %s: %s" % (type(e).__name__, e))
        elif upper.startswith('CRUN'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.crun_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
            except Exception as e:
                repl._emit("Error: %s: %s" % (type(e).__name__, e))
        elif upper.startswith('LIST'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.list_command(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper.startswith('LOAD'):
            parts = line.split(None, 1)
            if len(parts) > 1:
                argstr = parts[1].strip()
                run_after = False
                if argstr.upper().endswith(',R'):
                    argstr = argstr[:-2].strip()
                    run_after = True
                try:
                    # LOAD filename[,r]: r keeps data files open AND runs
                    # the program after loading (manual LOAD).
                    repl.load_command(argstr, keep_files=run_after,
                                      run_after=run_after)
                except BasicError as e:
                    repl._emit("Error: %s" % e)
            else:
                repl._emit("Usage: LOAD filename[,r]")
        elif upper.startswith('SAVE'):
            parts = line.split(None, 1)
            rest = parts[1].strip() if len(parts) > 1 else ''
            # The state machine (save_command) resolves the destination:
            # the given name; the last file for a bare SAVE; or a prompt
            # for a bare SAVE of a program that was never saved.  No options
            # are accepted after the file name.
            try:
                repl.save_command(rest or None,
                                  prompt_func=lambda: _prompt_readline(
                                      repl, 'Enter filename: '))
            except BasicError as e:
                repl._emit("Error: %s" % e)
            except Exception as e:
                # Safety net: a save failure must not kill the interpreter.
                repl._emit("Error: %s: %s" % (type(e).__name__, e))
        elif upper.startswith('DELETE'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.delete_lines(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper.startswith('EDIT'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.edit_line(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper.startswith('LEDIT'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            try:
                repl.ledit_line(argstr)
            except BasicError as e:
                repl._emit("Error: %s" % e)
        elif upper.startswith('TRACE'):
            parts = line.split(None, 1)
            argstr = parts[1].strip() if len(parts) > 1 else ''
            repl.trace_command(argstr)
        elif upper == 'CONT':
            repl.cont_command()
        elif upper == 'RENUM' or upper.startswith('RENUM '):
            parts = line.split(None, 1)
            argstr = parts[1] if len(parts) > 1 else ''
            repl.renum(argstr)
        elif upper == 'TOKEN':
            repl.show_tokens()
        else:
            try:
                repl.load_line(line)
            except KeyboardInterrupt:
                # Ctrl+C while an immediate-mode statement is running
                # (e.g. INPUT): stop it and return to the Ok prompt.
                repl._emit("Break")
            except BasicError as e:
                # A parse/store error that escaped load_line's own guards:
                # report it like any other command error.
                repl._emit("Error: %s" % e)
            except Exception as e:
                # Safety net: an unexpected failure handling a prompt line
                # must never kill the interpreter (the program stays in
                # memory); report it and re-prompt.
                repl._emit("Error: %s: %s" % (type(e).__name__, e))
        # After every command/statement is executed, print "Ready" on its
        # own line so the user knows they can enter the next command.
        # Numbered BASIC instructions (e.g. "10 PRINT ...") are only stored
        # in the program, so they do not print "Ready"; the Ok prompt
        # follows directly, matching real GW-BASIC behavior.  LEDIT also
        # omits "Ready": it leaves the edited line on screen and moves the
        # cursor to a fresh line itself.  A bare line number is a command
        # (it deletes the line), so it prints "Ready" like any command.
        first = line.split(None, 1)[0]
        bare_line_num = first.isdigit() and len(line.split(None, 1)) == 1
        if ((not first.isdigit() or bare_line_num)
                and not upper.startswith('LEDIT')):
            screen = repl.interpreter.screen
            # Only a RUNNING program may hold the graphics window open: the
            # two things that destroy it are program end and Ctrl+C.  "Ready"
            # marks a program that has ended (or never ran), so a window that
            # is still open - or a screen still in graphics mode - is torn
            # down here, exactly like a bare WINDOW (window destroyed, screen
            # back to text mode).  A STOP/break leaves the program loaded for
            # CONT, so its window stays open.
            if (screen._root is not None or not screen.is_text()) \
                    and not repl.interpreter._stopped:
                screen.close()
                screen.set_mode(0)
            if screen.cursor_col != 0:
                # The last output ended without a newline (e.g. PRINT "HI";):
                # terminate the line first so "Ready" starts on a fresh line.
                repl.io.write("", newline=True)
            repl._emit("\nReady\n")


if __name__ == '__main__':
    main()
