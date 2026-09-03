#!/usr/bin/env python3
"""Check the hygiene invariants of the built blueprint document.

Run from the repository root:

    python3 blueprint/check_blueprint.py [DECL_LIST_PATH]

The file set is *derived*, not hard-coded: the script starts at
``blueprint/src/content.tex`` and follows every ``\\input`` transitively, so it
measures exactly the document that would be built, and picks up a chapter as
soon as it is inputted.

What it enforces (each of these makes the exit status non-zero):

* every ``\\uses{...}`` target resolves to a ``\\label{...}`` somewhere in the
  document -- a dangling target is a broken edge in the blueprint dependency
  graph.  ``\\uses{none}`` is the blueprint's explicit "no dependencies"
  marker and counts as resolved;
* no ``\\label{...}`` is defined twice -- two chapters colliding on a label
  silently redirect every reference to one of them;
* no ``\\lean{}`` is empty -- an empty tag feeds a blank declaration name to
  the name list, which is then reported as a missing declaration.

It also reports, per file, the counts the blueprint-hygiene work is measured
by: ``\\label``s, ``\\lean{`` tags, empty ``\\lean{}`` tags and ``\\leanok``s.

Counting notes, each of which has caught a wrong census in this project:

* ``\\uses{...}``, ``\\lean{...}`` and ``\\label{...}`` span source lines, so
  everything is matched with ``re.S``.  A line-based ``grep`` finds 18
  distinct ``\\uses`` targets in ``proper_base_change.tex`` where there are
  312;
* LaTeX ``%`` comments and ``\\verb|...|`` spans are blanked before any
  matching, so a tag written inside a comment does not inflate the counts.

With ``DECL_LIST_PATH`` given, the list of declaration names named by
``\\lean{...}`` is written there, one per line, sorted -- suitable input for
an existence/axiom check.  The list covers the whole ``content.tex`` closure:
every file the document inputs contributes its names.

The blueprint itself cannot be compiled in the agent sandbox: there is no
``leanblueprint``, no ``plastex`` and no LaTeX engine there.  This script is a
source-level check and is not a substitute for building the document.
"""

import pathlib
import re
import sys

SRC = pathlib.Path("blueprint/src")
ROOT = SRC / "content.tex"

INPUT_RE = re.compile(r"\\input\{([^}]*)\}")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}", re.S)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.S)
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.S)


def blank(text):
    """Replace ``\\verb|...|`` spans and ``%`` comments by whitespace."""
    out = []
    for line in text.split("\n"):
        line = re.sub(r"\\verb(.)(.*?)\1", " ", line)
        m = re.search(r"(?<!\\)%", line)
        out.append(line[: m.start()] if m else line)
    return "\n".join(out)


def resolve(name):
    """Turn the argument of an ``\\input`` into a path under ``blueprint/src``."""
    path = SRC / name
    if path.suffix != ".tex":
        path = path.with_suffix(".tex")
    return path


def collect(path, seen, order):
    """Depth-first walk of ``\\input`` from ``path``, recording files in order."""
    path = path.resolve()
    if path in seen:
        return
    seen.add(path)
    order.append(path)
    text = blank(path.read_text(encoding="utf-8"))
    for m in INPUT_RE.finditer(text):
        child = resolve(m.group(1).strip())
        if child.exists():
            collect(child, seen, order)
        else:
            print(f"MISSING INPUT {m.group(1).strip()} in {rel(path)}")


def rel(path):
    try:
        return str(path.relative_to(pathlib.Path.cwd()))
    except ValueError:
        return str(path)


def split(arg):
    return [x.strip() for x in arg.split(",") if x.strip()]


def main(argv):
    if not ROOT.exists():
        print(f"{ROOT} not found -- run this from the repository root.")
        return 2

    seen, order = set(), []
    collect(ROOT, seen, order)

    labels = {}          # label -> [file, ...]
    uses = {}            # target -> [file, ...]
    leans = {}           # declaration name -> [file, ...]
    empty_leans = []     # (file, line) of every empty \lean{}
    per_file = []

    for path in order:
        text = blank(path.read_text(encoding="utf-8"))
        name = rel(path)
        n_label = n_lean = n_empty = 0
        for m in LABEL_RE.finditer(text):
            lab = m.group(1).strip()
            if lab:
                labels.setdefault(lab, []).append(name)
                n_label += 1
        for m in USES_RE.finditer(text):
            for target in split(m.group(1)):
                uses.setdefault(target, []).append(name)
        for m in LEAN_RE.finditer(text):
            n_lean += 1
            names = split(m.group(1))
            if not names:
                n_empty += 1
                empty_leans.append((name, text[: m.start()].count("\n") + 1))
            for decl in names:
                leans.setdefault(decl, []).append(name)
        per_file.append((name, n_label, n_lean, n_empty, text.count("\\leanok")))

    unresolved = sorted(t for t in uses if t != "none" and t not in labels)
    duplicates = sorted(lab for lab, files in labels.items() if len(files) > 1)

    width = max(len(name) for name, *_ in per_file)
    print(f"{'file':{width}}  {'label':>6} {'lean{':>6} {'empty':>6} {'leanok':>6}")
    for name, n_label, n_lean, n_empty, n_ok in per_file:
        print(f"{name:{width}}  {n_label:6d} {n_lean:6d} {n_empty:6d} {n_ok:6d}")
    totals = [sum(row[i] for row in per_file) for i in (1, 2, 3, 4)]
    print(f"{'TOTAL':{width}}  {totals[0]:6d} {totals[1]:6d} {totals[2]:6d} {totals[3]:6d}")
    print()
    print(f"{len(order)} files inputted from {rel(ROOT)}")
    print(f"{sum(len(f) for f in labels.values())} labels, {len(labels)} distinct")
    print(f"{len(uses)} distinct \\uses targets, {len(unresolved)} unresolved")
    print(f"{len(leans)} distinct \\lean names")
    print(f"{len(duplicates)} duplicate labels, {len(empty_leans)} empty \\lean{{}}")

    for target in unresolved:
        print(f"  UNRESOLVED \\uses{{{target}}} in {', '.join(sorted(set(uses[target])))}")
    for lab in duplicates:
        print(f"  DUPLICATE \\label{{{lab}}} in {', '.join(labels[lab])}")
    for name, line in empty_leans:
        print(f"  EMPTY \\lean{{}} at {name}:{line}")

    if len(argv) > 1:
        out = pathlib.Path(argv[1])
        out.write_text("\n".join(sorted(leans)) + "\n", encoding="utf-8")
        print(f"wrote {len(leans)} declaration names to {out}")

    return 1 if (unresolved or duplicates or empty_leans) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
