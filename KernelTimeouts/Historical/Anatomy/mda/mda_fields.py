#!/usr/bin/env python3
import argparse
import re

PATTERN = re.compile(r"MDA_FIELD\s+(\S+)\s+(\d+)\s+(\S+)")

parser = argparse.ArgumentParser()
parser.add_argument("log")
parser.add_argument("output")
args = parser.parse_args()
found = {}
with open(args.log, encoding="utf-8") as stream:
    for line in stream:
        match = PATTERN.search(line)
        if match:
            structure, index, field = match.groups()
            found[(structure, int(index))] = field
if not found:
    parser.error("no MDA_FIELD records found")
with open(args.output, "w", encoding="utf-8") as stream:
    for (structure, index), field in sorted(found.items()):
        stream.write(f"{structure} {index} {field}\n")
