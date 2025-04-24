#!/usr/bin/env python3
import argparse
from pathlib import Path
import tlc
import parser as tla_parser
import re

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
    # TODO: Constants is a dictonary where the key is the name of the constant and value is the value in .cfg file
    # TODO: Invariants are the properties to check in the TLC model checker, thus should be translated to C. It is a list of string names
    return constants, invariants

def main():
    args = parse_args()

    tla_text = args.tla_file.read_text(encoding="utf-8")
    cfg_text = args.config_file.read_text(encoding="utf-8")
    tla_bytes = args.tla_file.read_bytes()

    tlc.setup(str(args.tla_file), str(args.config_file), tla_text, cfg_text)

    # TODO: finish parsing of config file. Hardcoding for now with whatever is in Test.cfg
    # constants, invariants = parse_config(cfg_text)
    constants = {"N": 10}
    invariants = ["Double", "Increment", "TestInc", "Init"]
    
    tla_text = tla_bytes.decode("utf-8")
    tla_text = re.sub(r"(?ms)^\\* BEGIN TRANSLATION.*?^\\* END TRANSLATION.*?\n", "", tla_text)
    tla_bytes = tla_text.encode("utf-8")
    
    tla_parser.parse(constants, invariants, tla_bytes)

    # TODO: tla_parser.parse should return stuff. Use it to create C file

if __name__ == "__main__":
    main()
