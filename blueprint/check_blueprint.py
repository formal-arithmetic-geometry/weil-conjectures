#!/usr/bin/env python3
"""Check the hygiene invariants of the built blueprint document.

Run from the repository root:

    python3 blueprint/check_blueprint.py [DECL_LIST_PATH]

Two populations of Lean declaration names are read.

The first is the ``.tex`` blueprint.  Its file set is *derived*, not hard-coded:
the script starts at ``blueprint/src/content.tex`` and follows every
``\\input`` transitively, so it measures exactly the document that would be
built, and picks up a chapter as soon as it is inputted.  Those files name
declarations in ``\\lean{...}``.

The second is ``blueprint/verso/``, a second (Verso) rendering of the Nagata
blueprint whose nodes name their realising declarations in a
``(lean := "...")`` option instead.  It is read because nothing else looks at
those names: the Verso package is a separate lake package, so it is outside the
main project's ``lake build``, and it is outside the ``content.tex`` closure, so
the ``\\lean{...}`` scan above never sees it.  Without this, a declaration
renamed in ``WeilConjectures`` leaves the Verso names dangling until somebody
takes a manual census.  The directory is optional -- it does not exist on every
branch -- and its absence is reported, not an error.

This script does not check that any name *exists*; that is
``lake exe checkdecls``'s job, and ``DECL_LIST_PATH`` below is how the two
populations are handed to it in one pass.

What it enforces (each of these makes the exit status non-zero):

* every ``\\uses{...}`` target resolves to a ``\\label{...}`` somewhere in the
  document -- a dangling target is a broken edge in the blueprint dependency
  graph.  ``\\uses{none}`` is the blueprint's explicit "no dependencies"
  marker and counts as resolved;
* no ``\\label{...}`` is defined twice -- two chapters colliding on a label
  silently redirect every reference to one of them;
* no ``\\lean{}`` is empty -- an empty tag feeds a blank declaration name to
  the name list, which is then reported as a missing declaration;
* no Verso ``(lean := "")`` option is empty -- it feeds a blank name to that
  same list in exactly the same way.

It also reports, per file, the counts the blueprint-hygiene work is measured
by: ``\\label``s, ``\\lean{`` tags, empty ``\\lean{}`` tags and ``\\leanok``s.

Counting notes, each of which has caught a wrong census in this project:

* ``\\uses{...}``, ``\\lean{...}`` and ``\\label{...}`` span source lines, so
  everything is matched with ``re.S``.  A line-based ``grep`` finds 18
  distinct ``\\uses`` targets in ``proper_base_change.tex`` where there are
  312;
* LaTeX ``%`` comments and ``\\verb|...|`` spans are blanked before any
  matching, so a tag written inside a comment does not inflate the counts.

With ``DECL_LIST_PATH`` given, the declaration names are written there, one
per line, sorted -- suitable input for ``lake exe checkdecls`` or an axiom
check.  The list is the deduplicated *union* of both populations: the
``\\lean{...}`` names of the whole ``content.tex`` closure and the Verso
``(lean := "...")`` names.  The split between them is printed.  The literal
``...``, which appears in the prose that documents the option's syntax, is not
a name and is skipped; each skip is reported.

A PDF build of the blueprint is out of reach in the agent sandbox: there is no
LaTeX engine, no ``bibtex`` and no ``dvisvgm``.  The web (plasTeX) build *is*
possible there -- ``leanblueprint``, ``plastex`` and their plugins install from
the wheels already in the pip cache -- but it needs a ``pygraphviz`` stub and a
``kpsewhich`` shim to get through.  This script is a cheap source-level check
and is not a substitute for either build.
"""

import pathlib
import re
import sys

SRC = pathlib.Path("blueprint/src")
ROOT = SRC / "content.tex"
VERSO = pathlib.Path("blueprint/verso")

# The placeholder in the prose documenting the ``(lean := "...")`` syntax.  The
# test is equality with this exact string and nothing cleverer: a Lean name may
# carry Unicode letters and primes, so an identifier regex would silently drop
# real names (six of them here, e.g. ``...IdealSheafData.blowupι``).
PLACEHOLDER = "..."

INPUT_RE = re.compile(r"\\input\{([^}]*)\}")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}", re.S)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.S)
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.S)
VERSO_LEAN_RE = re.compile(r'\(lean\s*:=\s*"([^"]*)"\)', re.S)


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


def verso_scan():
    """Collect the ``(lean := "...")`` names of every file under ``blueprint/verso``.

    Returns ``(per_file, names, skipped, empty)`` where ``per_file`` is a list
    of ``(file, occurrences, names)`` rows in path order, ``names`` maps a
    declaration name to the files naming it, ``skipped`` and ``empty`` are
    ``(file, line)`` lists for the ``...`` placeholder and for an empty option.
    ``per_file`` is ``None`` when the directory is absent.
    """
    if not VERSO.is_dir():
        return None, {}, [], []
    per_file, names, skipped, empty = [], {}, [], []
    for path in sorted(VERSO.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        name = rel(path)
        n_occ = n_name = 0
        for m in VERSO_LEAN_RE.finditer(text):
            n_occ += 1
            line = text[: m.start()].count("\n") + 1
            decls = split(m.group(1))
            if not decls:
                empty.append((name, line))
            for decl in decls:
                if decl == PLACEHOLDER:
                    skipped.append((name, line))
                    continue
                n_name += 1
                names.setdefault(decl, []).append(name)
        per_file.append((name, n_occ, n_name))
    return per_file, names, skipped, empty


def main(argv):
    if not ROOT.exists():
        print(f"{ROOT} not found -- run this from the repository root.")
        return 2

    seen, order = set(), []
    collect(ROOT, seen, order)
    verso_files, verso_names, verso_skipped, verso_empty = verso_scan()

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

    print()
    if verso_files is None:
        print(f"{VERSO} not present -- no Verso (lean := \"...\") names to check.")
    else:
        width = max([len(name) for name, *_ in verso_files] + [len("TOTAL")])
        print(f"{'verso file':{width}}  {'(lean:=':>7} {'names':>6}")
        for name, n_occ, n_name in verso_files:
            print(f"{name:{width}}  {n_occ:7d} {n_name:6d}")
        n_occ = sum(row[1] for row in verso_files)
        n_name = sum(row[2] for row in verso_files)
        print(f"{'TOTAL':{width}}  {n_occ:7d} {n_name:6d}")
        print()
        print(f"{len(verso_files)} Verso files under {VERSO}, "
              f"{n_occ} (lean := \"...\") options, {n_name} names, "
              f"{len(verso_names)} distinct")
        print(f"{len(verso_skipped)} \"{PLACEHOLDER}\" placeholders skipped, "
              f"{len(verso_empty)} empty (lean := \"\")")
        for name, line in verso_skipped:
            print(f"  SKIPPED \"{PLACEHOLDER}\" at {name}:{line}")
        for name, line in verso_empty:
            print(f"  EMPTY (lean := \"\") at {name}:{line}")

    if len(argv) > 1:
        out = pathlib.Path(argv[1])
        union = sorted(set(leans) | set(verso_names))
        out.write_text("\n".join(union) + "\n", encoding="utf-8")
        both = len(set(leans) & set(verso_names))
        print()
        print(f"wrote {len(union)} declaration names to {out}")
        print(f"  {len(leans)} from \\lean{{}}, {len(verso_names)} from Verso, "
              f"{both} in both")

    return 1 if (unresolved or duplicates or empty_leans or verso_empty) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
