#!/usr/bin/env python3
import argparse
from pathlib import Path
import tlc
import parser as tla_parser

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

# def read_config_file(cfg_file_name):
#     r"""
#     Parses the config file and extracts:
#       - specification (string): provided on the same line as the keyword SPECIFICATION.
#       - constants (dict): assignments following the CONSTANT section.
#       - invariants (list): names listed under the INVARIANT section.
#       - properties (list): names listed under the PROPERTY section.
#     Lines starting with '*' (or "\*") are treated as comments.
#     The key parts can appear in any order.
#     """
#     specification = ""
#     constants = {}
#     invariants = []
#     properties = []
#     current_section = None
# 
#     # Open the configuration file.
#     with open(cfg_file_name, 'r') as f:
#         for line in f:
#             # Remove leading/trailing whitespace.
#             line = line.strip()
#             if not line:
#                 continue  # Skip blank lines.
#             # Skip comment lines that start with '*' or '\*'.
#             if line.startswith("*") or line.startswith("\\*"):
#                 continue
# 
#             # Check if the line starts with a section header.
#             tokens = line.split(maxsplit=1)
#             header = tokens[0].upper()
#             
#             # Handle SPECIFICATION (only singular is accepted).
#             if header == "SPECIFICATION":
#                 specification = tokens[1].strip() if len(tokens) > 1 else ""
#                 current_section = None  # One-off value.
#                 continue
# 
#             # Map possible plural or singular forms to a canonical section name.
#             if header in ("CONSTANT", "CONSTANTS"):
#                 current_section = "CONSTANT"
#                 continue
#             if header in ("INVARIANT", "INVARIANTS"):
#                 current_section = "INVARIANT"
#                 continue
#             if header in ("PROPERTY", "PROPERTIES"):
#                 current_section = "PROPERTY"
#                 continue
# 
#             # Process the line based on the current section.
#             if current_section == "CONSTANT":
#                 # Expect a format like "NP = 5" (with possible extra spaces).
#                 if '=' in line:
#                     name, value = line.split('=', 1)
#                     constants[name.strip()] = value.strip()
#             elif current_section == "INVARIANT":
#                 invariants.append(line)
#             elif current_section == "PROPERTY":
#                 properties.append(line)
#             # If no section is active, ignore the line.
# 
#     return specification, constants, invariants, properties

def main():
    args = parse_args()

    tla_text = args.tla_file.read_text(encoding="utf-8")
    cfg_text = args.config_file.read_text(encoding="utf-8")

    tlc.setup(str(args.tla_file), str(args.config_file), tla_text, cfg_text)

    result = tlc.evaluate("0..(N-1)")
    print(result)

    # tla_parser.parse(tla_text, cfg_text)

if __name__ == "__main__":
    main()
