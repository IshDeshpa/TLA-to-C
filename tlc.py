import re, tempfile, subprocess
from pathlib import Path

tmp = None
tmp_print_idx = None
cfg_path = None

def setup(tla_path, _cfg_path, tla_text, cfg_text):
    global tmp, tmp_print_idx, cfg_path
    cfg_path = str(Path(_cfg_path).resolve())

    lines = tla_text.splitlines(True)

    extends_re = re.compile(r'^\s*EXTENDS\s+(.*)$')
    idx = next((i for i, L in enumerate(lines) if extends_re.match(L)), None)
    if idx is not None:
        mods = [m.strip() for m in extends_re.match(lines[idx]).group(1).split(',')]
        if 'TLAPS' in mods:   mods.remove('TLAPS')
        if 'TLC'   not in mods: mods.insert(0, 'TLC')
        lines[idx] = f"EXTENDS {', '.join(mods)}\n"
    else:
        module_re = re.compile(r'^\s*-{4,}\s*MODULE\b')
        midx = next((i for i, L in enumerate(lines) if module_re.match(L)), None)
        if midx is None:
            raise RuntimeError("Cannot find MODULE header")
        lines.insert(midx+1, "EXTENDS TLC\n")

    thm_re, endmod_re = re.compile(r'^\s*THEOREM\b'), re.compile(r'^={4,}')
    tidx = next((i for i, L in enumerate(lines) if thm_re.match(L)), None)
    if tidx is not None:
        eidx = next((j for j in range(tidx+1, len(lines)) if endmod_re.match(lines[j])), None)
        if eidx is None:
            raise RuntimeError("End of theorem not found")
        del lines[tidx:eidx]

    init_re = re.compile(r'^\s*Init\s*==')
    start = next((i for i, L in enumerate(lines) if init_re.match(L)), None)
    if start is None:
        raise RuntimeError("Init block not found")
    tmp_print_idx = next((j for j in range(start+1, len(lines)) if lines[j].strip()==""), len(lines))

    tmp_text = ''.join(lines)
    tmp_path = Path(tempfile.gettempdir()) / Path(tla_path).name
    tmp = open(tmp_path, 'w')
    tmp.write(tmp_text)
    tmp.flush()

def evaluate(value):
    global tmp, tmp_print_idx, cfg_path

    def expand_ranges(expr):
        return re.sub(
            r'(\S+)\s*\.\.\s*(\S+)',
            r'{i \\in \1..\2 : TRUE}',
            expr
        )
    value_expanded = expand_ranges(value)

    path = tmp.name
    with open(path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    print_line = f"    /\\ Print({value_expanded}, TRUE)\n"

    if tmp_print_idx is None:
        raise RuntimeError("Init boundaries not set")
    lines.insert(tmp_print_idx, print_line)

    with open(path, 'w', encoding='utf-8') as f:
        f.writelines(lines)

    cmd = [
        "java", "-cp", "tla2tools.jar", "tlc2.TLC",
        "-config", cfg_path, path
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)

    out_lines = proc.stdout.splitlines()
    marker = "Computing initial states"
    start = next((i for i, L in enumerate(out_lines) if L.startswith(marker)), None)
    if start is None or start+1 >= len(out_lines):
        raise RuntimeError("TLC output not in expected format")

    printed = out_lines[start+1].strip()
    if printed.endswith(" TRUE"):
        printed = printed[:-5]
    only_expr = printed.strip()

    return only_expr
