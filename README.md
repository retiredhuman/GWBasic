[README.md](https://github.com/user-attachments/files/32152952/README.md)
# GW-BASIC for Windows — gwibasic & gwcbasic

A modern GW-BASIC remake for Windows, in two single-file programs:

| File | What it is |
|------|------------|
| `gwibasic.py` | The GW-BASIC **interpreter** (interactive REPL + program runner) |
| `gwcbasic.py` | The GW-BASIC **native compiler** (.bas → native Windows .exe) |

Both scripts can themselves be packaged with PyInstaller into **self-contained
.exe files** (`gwibasic.exe`, `gwcbasic.exe`) that run with no Python install
needed. And with `gwcbasic`, any BASIC program you write can be compiled into
its own standalone .exe — no Python, no interpreter, no external files at
runtime.

---

## 1. gwibasic.py — the Interpreter

### What it is
A from-scratch GW-BASIC interpreter in one Python file. It boots with the
classic "Ready" prompt and supports program editing, running, saving, an
on-line HELP system, a virtual 80x25 text screen, a lazy-opened graphics
window, PC-speaker-style sound, and real music playback.

### How it works
- **Startup:** `python gwibasic.py` starts the interactive REPL;
  `python gwibasic.py program.bas` loads and runs a file immediately.
  `--nogui` forces headless mode; `--gui` is accepted but no longer needed
  (the graphics window opens by itself the moment a program uses it).
- **Execution:** statements are tokenized, parsed, and run by a fast
  compile-to-Python engine; errors are reported GW-BASIC style and never
  crash the interpreter.
- **The screen:** a virtual text screen (SCREEN 0) driven with VT escape
  codes in the console. `SCREEN 1, 2, 7, 8, 9, 10` opens a tkinter graphics
  window (mode 7 is the classic 320x200 look). The window is created lazily
  and destroyed at program end or Ctrl+C.
- **Sound:** `SOUND`/`BEEP`/`PLAY` use the Windows beep driver (winsound —
  a square wave like the PC speaker) on a background thread, so BASIC keeps
  running while notes play. `MUSICFILE`/`PLAYMUSIC` play real .wav/.mp3/.wma
  files through WinMM MCI.
- **Memory:** `PEEK`/`POKE`/`BLOAD`/`BSAVE`/`DEF SEG` work against a
  simulated 64K memory segment (not real MS-DOS addresses).
- **Input:** full-line editing at the prompt (arrows, Home/End, Insert,
  Delete), `INKEY$`, `INPUT$`, `KEY ON`/`ON KEY`, and mouse support via the
  `MOUSE` statement.

### Console commands (the highlighted workflow)

> **★ COMPILE** — builds the current program into a native Windows .exe
> using the gwcbasic compiler (which must sit next to gwibasic). It takes no
> filename and never touches your .bas: unsaved edits are compiled from a
> timestamped temporary file, and a later SAVE commits them by renaming.
> On success you get a one-line summary (source → exe, size).
>
> **★ CRUN** — runs the .exe produced by COMPILE as an independent process
> (its own console or its own graphics window) while the interpreter stays
> at the Ready prompt. `CRUN filename` runs a specific .exe.

> In short: **type `COMPILE`, then `CRUN`** at the interpreter console to go
> from edited program to running native executable.

Other immediate-mode commands:

| Command | Purpose |
|---------|---------|
| `HELP [topic]` | Built-in help: full command/instruction/function reference |
| `RUN [line]` | Run the loaded program (optionally starting at the given line; no filenames — LOAD first) |
| `LIST [n[-m]][,file]` | List program lines; hyphen ranges (`20-`, `-20`), `.` = current line; optional file to list to |
| `LOAD file[,r]` | Load a .bas (without `,r` files are closed and variables cleared; `,r` keeps files/variables open and runs the program after loading) |
| `SAVE file` / bare `SAVE` | Save program (bare SAVE reuses the last name, or prompts if never saved) |
| `NEW` | Erase program, variables, and open files |
| `AUTO [start[,inc]]` | Automatic line numbering; `AUTO .[,inc]` starts at the current line; Ctrl+C or a bare RETURN ends it |
| `DELETE a[-b]` | Delete lines (ranges as in LIST, `.` = current line; bare DELETE is an error) |
| `EDIT n` / `LEDIT n` | EDIT displays the line and makes it the current line; LEDIT edits it in place (arrow keys, ENTER stores, ESC cancels) |
| `RENUM [new],[old line][,inc]` | Renumber lines and update all line references (defaults: 10, first line, 10) |
| `CLEAR` | Zero variables, reset arrays, close files, disable ON ERROR, stop sound (memory/stack expressions accepted, simulated) |
| `CONT` | Continue after a STOP, break, or trace stop |
| `TRACE ON [lps] [PAUSE]` / `TRACE OFF` / `TRACE` | Display executed lines, paced to `lps` lines per second (default 3, range 1–100); `PAUSE` waits for ENTER/SPACE after every `lps` traced lines; bare TRACE reports the state |
| `TOKEN` | Show every program line with its token stream |
| `BYE` / `EXIT` / `QUIT` | Quit the interpreter |

### BASIC statements supported
`BEEP BLOAD BSAVE CALL-free graphics (CIRCLE DRAW LINE PAINT PSET PRESET POINT)
CLOSE CLS COLOR COMMON CONT DATA DEF FN DEF SEG DEFDBL DEFINT DEFSNG DEFSTR
DELETE DIM DO...LOOP EDIT ELSE END ENDIF ENVIRON ERASE ERROR FIELD FOR...NEXT
GET GOSUB GOTO IF...THEN INK INPUT INPUT# KEY KILL LEDIT LET LINE LOCATE LOOP
LPRINT (accepted) LSET MOUSE MUSICFILE MUSICVOLUME NEXT ON...GOTO/GOSUB/KEY
OPEN (INPUT/OUTPUT/APPEND/RANDOM/BINARY) OPTION OUT PAINT PALETTE PAUSE PEEK-
side: POKE PLAY PLAYMUSIC PRESET PUT RANDOMIZE READ REDIM REM RESTORE RESUME
RETURN RSET RUN SCREEN SCREENSIZE SEEK SETFPS SLEEP STOP STOPMUSIC SWAP SYSTEM
TEXTFONT TEXTROTATE TEXTSIZE TRACE TRAP VIEW WAIT WCLOSE WEND WHILE WINDOW
WRITE` — plus `COMPILE`/`CRUN` as interpreter commands.

### Functions supported
`ABS ACOS ASC ASIN ATN BIN$ CDBL CHR$ CINT COS CSNG CSRLIN CVD CVI CVS DATE$
DAY DIR$ ENVIRON$ EOF EXP FIX FRE HEX$ HOUR INKEY$ INPUT$ INSTR INT LCASE$
LEFT$ LEN LOC LOF LOG MID$ MINUTE MKD$ MKI$ MKS$ MONTH OCT$ PEEK PEER POINT
POS RGB RIGHT$ RND ROUND ROUNDDOWN ROUNDFRAC ROUNDUP SECOND SGN SIN SPACE$
SPC SQR STR$ STRING$ TAB TAN TIME$ TIMER TRIM$ UCASE$ VAL VARPTR VARPTR$
YEAR XSZ YSZ` — plus user `DEF FN` functions.

### Extensions beyond classic GW-BASIC
`DO...LOOP`, `MOUSE`, `SETFPS`, `TEXTFONT`/`TEXTSIZE`/`TEXTROTATE`, `INK`,
`RGB()`, `PAUSE`, `CURSOR`, `WINDOW`/`SCREENSIZE` windowed display,
`MUSICFILE`/`PLAYMUSIC`/`STOPMUSIC`/`MUSICVOLUME`, `TRAP`, `PEER`,
`XSZ`/`YSZ`, `ROUND`/`ROUNDUP`/`ROUNDDOWN`/`ROUNDFRAC`, and the
`COMPILE`/`CRUN` native-build workflow.

### No longer supported (no meaning under Windows)
- **`CHAIN`, `MERGE`, `LINK`, `OLD`** — overlay/chaining of .BAS/.BSV files:
  gone; just LOAD/SAVE ordinary files.
- **`LLIST`** — printing the program to a line printer: gone.
- **`PCOPY`** — screen pages: replaced by the single windowed display.
- **`CSAVE`/`CLOAD`** — cassette tape: gone.
- **`FILES`** — use a normal Windows shell `dir` instead (`DIR$` still works).
- **`TRON`/`TROFF`** — replaced by `TRACE`.
- **`LPRINT` / `LPT1:`–`LPT3:`** — accepted for compatibility but a no-op.
- **`COM1:`/`COM2:` file devices, real MS-DOS `DEF SEG` memory** — the
  statements run against the simulated segment only; real hardware ports
  and DOS memory are not touched.
- **Classic 40-column text modes (SCREEN 3–6)** — the Windows display keeps
  the 80-column text model plus graphics modes 0, 1, 2, 7, 8, 9, 10.

### Tools needed
- **Python 3** (64-bit recommended) — standard library only;
  **tkinter** for the graphics window (bundled with the Windows Python
  installer), **msvcrt/winsound/winmm** via ctypes (built into Windows
  Python).
- To package as `gwibasic.exe`: **PyInstaller** (`--windowed` builds are
  handled — the app runs fine with no console).
- To use `COMPILE` from the console: **gwcbasic** (gwcbasic.exe or
  gwcbasic.py) sitting in the same folder, plus the MSVC toolchain (see
  below).

---

## 2. gwcbasic.py — the Native Compiler

### What it is
A single-file **GW-BASIC-to-native compiler**. It turns a .bas program into
a standalone 64-bit Windows .exe with **no Python and no external files
needed at runtime** — the parser, the C code generator, and the whole C
runtime are embedded inside gwcbasic.py itself. The compiled program
mirrors the interpreter's behavior bit-for-bit, including its documented
quirks.

### How it works
Per program: **parse → generate C → cl.exe → `<name>.exe` written next to
the source** (`spawn.bas` → `spawn.exe`).

- **Native codegen (default):** type-specialized, direct-jump C generation
  — roughly 100x+ faster than the VM on compute-heavy programs, with
  byte-identical output. Statements the generator can't specialize run as
  bridge islands through the same runtime, so the native path is a strict
  superset of the VM path.
- **Embedded runtime:** the generated .exe links a C runtime providing the
  console, the graphics window, sound, and files (user32, gdi32, winmm).
- **Console behavior:** every compiled program starts with a console; the
  runtime closes it the instant a graphics window opens (double-click and
  `CRUN` behave identically). A text-only program keeps its console until
  it exits.

### Commands (command-line usage)

    gwcbasic [options] <prog.bas> [more.bas ...]

| Option | Purpose |
|--------|---------|
| *(none)* | Native compile and link each .bas to a self-contained .exe |
| `--vm` | Use the legacy VM (bytecode) codegen — diagnostic fallback only |
| `--keep-c` | Also save the generated `<name>.c` next to the source |
| `--c-only` | Generate the .c only; skip the compile/link step |
| `-h` / `--help` | Show usage |

Bare names get `.bas` appended automatically; multiple files may be given
and a summary (`N/M built`) is printed at the end.

### Inside the interpreter: COMPILE and CRUN
gwibasic's console exposes the compiler directly — **`COMPILE`** builds the
in-memory program (via gwcbasic, invisibly, with a one-line success summary)
and **`CRUN`** launches the result as its own process. This is the
highlighted inner-loop: edit → `COMPILE` → `CRUN` → `SAVE`.

### Tools needed
- **Python 3** to run `gwcbasic.py` (or use the pre-built `gwcbasic.exe`,
  which is itself a self-contained PyInstaller package).
- **Microsoft Visual C++ (MSVC) build tools** — `cl.exe` must be present on
  the same machine. The build recipe expects a flat MSVC Include layout,
  e.g. Visual Studio BuildTools with `VC\Tools\MSVC\14.x` and the Windows
  10 SDK (`10.0.26100.0`); the MSVC and SDK Include/Lib directories are
  passed to cl.exe directly.
- Link libraries used: `user32.lib`, `gdi32.lib`, `winmm.lib` (all from the
  MSVC/SDK install — nothing else to install).

---

## Quick start

    python gwibasic.py                # interactive GW-BASIC
    python gwibasic.py prime.bas      # run a program file
    python gwcbasic.py prime.bas      # prime.bas -> prime.exe (native)
    prime.exe                         # runs standalone — no Python needed

    ' Or live inside the interpreter:
    READY> LOAD PRIME.BAS
    READY> COMPILE        ' -> prime.exe
    READY> CRUN           ' run it in its own window/console
