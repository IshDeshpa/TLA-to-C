#!/usr/bin/env python3
import argparse
from pathlib import Path
import tlc
import parser as tla_parser
import re
import ast

def parse_args():
    argp = argparse.ArgumentParser(
        description="Convert a PlusCal/TLA+ specification into C code with config file."
    )
    argp.add_argument("tla_file", type=Path,  help="Path to the TLA file")
    argp.add_argument("config_file", type=Path, help="Path to the configuration file")
    args = argp.parse_args()
    for attr in ("tla_file", "config_file"):
        p = getattr(args, attr)
        if not p.is_file():
            argp.error(f"{p} does not exist or is not a file.")
    return args

def parse_config(cfg_text):
    constants = {}
    invariants = []
    in_const_block = False
    in_inv_block = False

    for raw_line in cfg_text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith('#'):
            continue

        m = re.match(r'^CONSTANTS?\s+([A-Za-z_]\w*)\s*=\s*(.+)$', line)
        if m:
            name, val_txt = m.group(1), m.group(2).strip()
            try:
                value = ast.literal_eval(val_txt)
            except Exception:
                value = val_txt
            constants[name] = value
            continue

        if line == "CONSTANT" or line == "CONSTANTS":
            in_const_block = True
            in_inv_block = False
            continue

        if line == "INVARIANT" or line == "INVARIANTS":
            in_inv_block = True
            in_const_block = False
            continue

        if line.startswith(("SPECIFICATION", "INIT", "NEXT", "PROPERTY")):
            in_const_block = in_inv_block = False
            continue

        if in_const_block and '=' in line:
            name, val_txt = (part.strip() for part in line.split('=', 1))
            try:
                value = ast.literal_eval(val_txt)
            except Exception:
                value = val_txt
            constants[name] = value
            continue

        if in_inv_block:
            invariants.append(line)
            continue

    return constants, invariants

def main():
    args = parse_args()

    tla_text = args.tla_file.read_text(encoding="utf-8")
    cfg_text = args.config_file.read_text(encoding="utf-8")
    tla_bytes = args.tla_file.read_bytes()

    tlc.setup(str(args.tla_file), str(args.config_file), tla_text, cfg_text)

    constants, invariants = parse_config(cfg_text)
    
    tla_parser.parse(constants, invariants, tla_bytes)

    # TODO: tla_parser.parse should return stuff. Use it to create C file

if __name__ == "__main__":
    main()
