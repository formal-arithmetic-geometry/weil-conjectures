#!/usr/bin/env python3
"""Read the source selected by the stage-2 compilers, including the published baseline.

An existing artifact may predate the working tree. Never describe that artifact
with the newer source: use its published commit unless nt_source_overlay selects
the module for private compilation. This command does not refresh artifacts.
"""
import json
import pathlib
import re
import subprocess
import sys

from nt_source_overlay import source_for_import


class SourceUnavailable(RuntimeError):
    pass


def read_source(root, module):
    """Return (source text, provenance) for the compiler's version of module."""
    if not re.fullmatch(r"(?:Sheaf|WeilConjectures|Mathlib)(?:\.[A-Za-z_][A-Za-z0-9_']*)+", module):
        raise SourceUnavailable("Expected a Lean module name")
    root = pathlib.Path(root)
    lean = root / "lean"
    rel = module.replace(".", "/") + ".lean"
    if module.startswith("Mathlib."):
        path = lean / ".lake/packages/mathlib" / rel
        try:
            return path.read_text(), "Mathlib package source"
        except OSError as exc:
            raise SourceUnavailable(f"Module source unavailable: {module}") from exc
    private = source_for_import(root, lean, rel)
    if private is not None:
        return private.read_text(), "current source selected for private compilation"
    artifact = lean / ".lake/build/lib/lean" / pathlib.PurePosixPath(rel).with_suffix(".olean")
    if not artifact.is_file():
        raise SourceUnavailable(f"Module source unavailable: {module}")
    try:
        commit = json.loads((root / "local/builds/published.json").read_text())["commit"]
        text = subprocess.check_output(
            ["git", "show", f"{commit}:lean/{rel}"], cwd=root,
            text=True, stderr=subprocess.PIPE)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        raise SourceUnavailable(
            f"Published source unavailable for {module}; refusing to substitute newer working-tree text") from exc
    return text, f"published commit {commit}"


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: nt_compile_source.py Module.Name")
    module = sys.argv[1]
    try:
        text, origin = read_source(pathlib.Path(__file__).resolve().parent.parent, module)
    except SourceUnavailable as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(f"Compile source for {module}: {origin}", file=sys.stderr)
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
