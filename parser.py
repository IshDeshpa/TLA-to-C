#!/usr/bin/env python3
import argparse
import model

def parse_args():
    # Set up argparse to take two positional arguments: config file and TLA file.
    parser = argparse.ArgumentParser(
        description="Convert a TLA+ specification into C code with config file."
    )
    parser.add_argument("config_file", help="Path to the configuration file")
    parser.add_argument("tla_file", help="Path to the TLA file")
    args = parser.parse_args()
    return args.config_file, args.tla_file

def read_config_file(cfg_file_name):
    r"""
    Parses the config file and extracts:
      - specification (string): provided on the same line as the keyword SPECIFICATION.
      - constants (dict): assignments following the CONSTANT section.
      - invariants (list): names listed under the INVARIANT section.
      - properties (list): names listed under the PROPERTY section.
    Lines starting with '*' (or "\*") are treated as comments.
    The key parts can appear in any order.
    """
    specification = ""
    constants = {}
    invariants = []
    properties = []
    current_section = None

    # Open the configuration file.
    with open(cfg_file_name, 'r') as f:
        for line in f:
            # Remove leading/trailing whitespace.
            line = line.strip()
            if not line:
                continue  # Skip blank lines.
            # Skip comment lines that start with '*' or '\*'.
            if line.startswith("*") or line.startswith("\\*"):
                continue

            # Check if the line starts with a section header.
            tokens = line.split(maxsplit=1)
            header = tokens[0].upper()
            
            # Handle SPECIFICATION (only singular is accepted).
            if header == "SPECIFICATION":
                specification = tokens[1].strip() if len(tokens) > 1 else ""
                current_section = None  # One-off value.
                continue

            # Map possible plural or singular forms to a canonical section name.
            if header in ("CONSTANT", "CONSTANTS"):
                current_section = "CONSTANT"
                continue
            if header in ("INVARIANT", "INVARIANTS"):
                current_section = "INVARIANT"
                continue
            if header in ("PROPERTY", "PROPERTIES"):
                current_section = "PROPERTY"
                continue

            # Process the line based on the current section.
            if current_section == "CONSTANT":
                # Expect a format like "NP = 5" (with possible extra spaces).
                if '=' in line:
                    name, value = line.split('=', 1)
                    constants[name.strip()] = value.strip()
            elif current_section == "INVARIANT":
                invariants.append(line)
            elif current_section == "PROPERTY":
                properties.append(line)
            # If no section is active, ignore the line.

    return specification, constants, invariants, properties

def read_tla_file(tla_file_name):
    # Reads the entire TLA file and returns its content.
    with open(tla_file_name, 'rb') as f:
        return f.read()

def main():
    # Parse args
    cfg_file_name, tla_file_name = parse_args()
    
    # Read config file
    specification, constants, invariants, properties = read_config_file(cfg_file_name)
    
    # Read TLA file
    tla = read_tla_file(tla_file_name)
    
    # Parse TLA file
    model.parse_tla_file(specification, constants, invariants, properties, tla)

    # Convert parse to C structures
    # Generate C file
    # Write C file
    

if __name__ == "__main__":
    main()

