#!/usr/bin/env python3
"""Certify large live drift against a completed prepared upstream build.

The candidate is a disposable latest-live merge made by sync-upstream.sh, never
the live repository. Existing files may change only indented `theorem`/`lemma`
`:= by` bodies. Everything outside those bodies is compared byte-for-byte.
Unsupported syntax and interface changes fail closed. New modules may import
only modules already present in the prepared compiled library or its packages.
All changed files compile separately, against the prepared imports, within 60 s.
No artifact is written into either input tree and no multi-module build is run.
"""
from __future__ import annotations

import os
import sys

# tools/queue.py is the project queue tool, not Python's queue module. Remove
# this script directory before importing concurrent.futures' stdlib dependency.
sys.path[:] = [p for p in sys.path if os.path.realpath(p or os.getcwd()) != os.path.dirname(os.path.realpath(__file__))]

import argparse
import concurrent.futures
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile
import time
import tomllib


class Rejected(ValueError):
    pass


def mask_literals(text: str) -> str:
    """Preserve positions/newlines while hiding nested comments and strings."""
    out = list(text)
    i, comment, string = 0, 0, False
    while i < len(text):
        if comment:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "; comment += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "; comment -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                if i + 1 < len(text) and text[i + 1] != "\n": out[i + 1] = " "
                i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "; comment = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end - i); i = end
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if comment or string: raise Rejected("unterminated comment/string")
    return "".join(out)


DECL = re.compile(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|public)\s+)*(?:theorem|lemma)\s+", re.M)
ESCAPE = re.compile(r"\b(?:run_tac|run_elab|elab|macro|syntax|attribute|set_option|initialize)\b")


def skeleton(text: str) -> tuple[str, int]:
    """Erase only syntactically simple top-level tactic theorem bodies."""
    masked = mask_literals(text)
    ranges = []
    for decl in DECL.finditer(masked):
        i, depth, colon, ambiguous = decl.end(), [], False, False
        proof = None
        while i < len(masked):
            c = masked[i]
            if c in "({[⟨": depth.append(c)
            elif c in ")}]⟩":
                if not depth: break
                if "({[⟨".index(depth.pop()) != ")}]⟩".index(c): break
            elif not depth:
                if c == ":" and not masked.startswith(":=", i): colon = True
                if masked.startswith(":=", i):
                    by = re.match(r":=\s*by\b", masked[i:])
                    if colon and by and not ambiguous: proof = i + by.end()
                    break
                if re.match(r"(?:letI?|haveI?|suffices|obtain)\b", masked[i:]): ambiguous = True
                # A second unindented command means this is unsupported syntax.
                if c == "\n":
                    tail = masked[i + 1:]
                    if tail and not tail[0].isspace(): break
            i += 1
        if proof is None: continue
        end = len(text)
        for line in re.finditer(r"^\S", masked[proof:], re.M):
            pos = proof + line.start()
            # The remainder of the := by line is an ordinary proof expression.
            if "\n" not in masked[proof:pos]: continue
            end = pos; break
        body = masked[proof:end]
        if ESCAPE.search(body): raise Rejected("environment-changing tactic syntax in proof")
        # Do not hide a command indented into the body. Lean accepts some commands
        # outside a theorem even with indentation, so identify them conservatively.
        if re.search(r"^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|public|unsafe|partial|scoped|local)\s+)*(?:end|namespace|section|import|export|open|variable|def|abbrev|instance|axiom|opaque|theorem|lemma|class|structure|inductive)\b", body, re.M):
            raise Rejected("ambiguous command-like line inside proof")
        ranges.append((proof, end))
    result, start = [], 0
    for begin, end in ranges:
        if begin < start: raise Rejected("overlapping theorem bodies")
        result += [text[start:begin], "\n<PROOF>\n"]
        start = end
    result.append(text[start:])
    return "".join(result), len(ranges)


def git(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def sources(root: pathlib.Path) -> dict[str, bytes]:
    names = subprocess.check_output(["git", "-C", str(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "lean"], text=True).split("\0")
    result = {}
    for name in set(names):
        if not name: continue
        path = root / name
        if path.is_symlink(): raise Rejected(f"symlink source: {name}")
        if path.is_file(): result[name] = path.read_bytes()
    return result


def digest(files: dict[str, bytes]) -> str:
    h = hashlib.sha256()
    for name, data in sorted(files.items()): h.update(name.encode() + b"\0" + data + b"\0")
    return h.hexdigest()


def options(lean: pathlib.Path, rel: str) -> list[str]:
    config = tomllib.loads((lean / "lakefile.toml").read_text())
    def flatten(mapping, prefix=""):
        result = {}
        for key, value in mapping.items():
            name = prefix + key
            if isinstance(value, dict): result.update(flatten(value, name + "."))
            else: result[name] = value
        return result
    opts = flatten(config.get("leanOptions", {}))
    if not rel.startswith(("WeilConjectures/", "Comparator/")):
        for lib in config.get("lean_lib", []):
            if lib.get("name") == "Sheaf": opts.update(flatten(lib.get("leanOptions", {})))
    return [f"-D{k}={str(v).lower() if isinstance(v, bool) else v}" for k, v in opts.items()]


def run(args) -> dict:
    prepared, candidate, built = (pathlib.Path(x).resolve() for x in (args.prepared, args.candidate, args.built_lean))
    if prepared == candidate: raise Rejected("candidate must be a disposable separate tree")
    if not 1 <= args.timeout <= 60: raise Rejected("timeout must be between 1 and 60 seconds")
    if not 1 <= args.workers <= 8: raise Rejected("workers must be between 1 and 8")
    heads = [git(p, "rev-parse", "HEAD") for p in (prepared, candidate)]
    old, new = sources(prepared), sources(candidate)
    if built != prepared / "lean":
        raise Rejected("built-lean must be the prepared tree's lean directory")
    before = [digest(old), digest(new)]
    changed = sorted(name for name in old.keys() | new.keys() if old.get(name) != new.get(name))
    deleted = [name for name in changed if name not in new]
    if deleted: raise Rejected("deleted prepared files: " + ", ".join(deleted))
    for name in changed:
        if not name.endswith(".lean"): raise Rejected("non-Lean build input changed: " + name)
        if name in old:
            a, count_a = skeleton(old[name].decode())
            b, count_b = skeleton(new[name].decode())
            if a != b or count_a != count_b:
                raise Rejected("interface or unsupported proof syntax changed: " + name)
    if any(old.get("lean/" + name) != (built / name).read_bytes() for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json")):
        raise Rejected("prepared and built package configuration differ")
    env = os.environ.copy()
    env["PATH"] = str(pathlib.Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    lp = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=built, env=env, text=True).strip()
    roots = [pathlib.Path(p) if pathlib.Path(p).is_absolute() else built / p for p in lp.split(os.pathsep)]
    env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in roots)
    compiler = subprocess.check_output(["lake", "env", "which", "lean"], cwd=built, env=env, text=True).strip()
    for name in changed:
        code = mask_literals(new[name].decode())
        lines = code.splitlines()
        parsed_imports = 0
        for index, line in enumerate(lines):
            match = re.match(r"^(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
            if not match: continue
            parsed_imports += 1
            if name not in old:
                following = next((x for x in lines[index + 1:] if x.strip()), "")
                if following[:1].isspace():
                    raise Rejected("ambiguous multiline import in new module: " + name)
            for module in match.group(1).split():
                if not re.fullmatch(r"[\w.]+", module): raise Rejected("unsupported import: " + name)
                artifact = pathlib.Path(module.replace(".", "/") + ".olean")
                if not any((root / artifact).is_file() for root in roots):
                    raise Rejected(f"import has no prepared built artifact: {name}: {module}")
                own = "lean/" + module.replace(".", "/") + ".lean"
                comparator = "lean/Comparator/" + module.replace(".", "/") + ".lean"
                if own in new and own not in old or comparator in new and comparator not in old:
                    raise Rejected(f"imports a new unbuilt module: {name}: {module}")
        if name not in old and parsed_imports != len(re.findall(r"\bimport\b", code)):
            raise Rejected("unsupported import syntax in new module: " + name)
    results = []
    with tempfile.TemporaryDirectory(prefix="upstream-drift-") as scratch_name:
        scratch = pathlib.Path(scratch_name)
        for name in changed:
            path = scratch / name.removeprefix("lean/")
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(new[name])
        def check(name):
            rel = name.removeprefix("lean/")
            start = time.monotonic()
            cmd = ["timeout", "--kill-after=2", str(args.timeout), "nice", "-n19", compiler, *options(built, rel), "-R", str(scratch), str(scratch / rel)]
            proc = subprocess.run(cmd, cwd=built, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            return {"path": name, "exit": proc.returncode, "seconds": round(time.monotonic() - start, 2), "output": proc.stdout[-6000:]}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            for result in pool.map(check, changed):
                results.append(result)
                print(f"{result['path']}: exit={result['exit']} seconds={result['seconds']}", flush=True)
    if heads != [git(p, "rev-parse", "HEAD") for p in (prepared, candidate)] or before != [digest(sources(prepared)), digest(sources(candidate))]:
        raise Rejected("an input tree changed during certification")
    return {"ok": all(r["exit"] == 0 for r in results), "prepared_head": heads[0], "candidate_head": heads[1], "prepared_sources_sha256": before[0], "candidate_sources_sha256": before[1], "changed_files": len(changed), "new_files": sum(name not in old for name in changed), "timeout": args.timeout, "workers": args.workers, "checks": results}


def self_test():
    base = "import Mathlib\n@[simp]\ntheorem foo (x : Nat) : x = x := by\n  rfl\n\ndef bar := 1\n"
    assert skeleton(base)[0] == skeleton(base.replace("  rfl", "  exact rfl"))[0]
    for changed in (base.replace("Nat", "Int"), base.replace("simp", "ext"), base.replace("def bar := 1", "def bar := 2"), base.replace("Mathlib", "Lean"), base.replace("  rfl", "  rfl\nset_option autoImplicit true")):
        assert skeleton(base)[0] != skeleton(changed)[0]
    for bad in (base.replace("  rfl", "  run_tac pure ()"), base.replace("  rfl", "  rfl\n  def sneaky := 1")):
        try: skeleton(bad)
        except Rejected: pass
        else: raise AssertionError("ambiguous proof accepted")
    # A := in a binder is retained, and a let-expression in a signature fails closed.
    simple = "theorem x (n : Nat := 0) : n = n := by\n  rfl\n"
    assert skeleton(simple)[1] == 1
    tricky = "theorem x : let n := 0; n = n := by\n  rfl\n"
    assert skeleton(tricky)[1] == 0
    print("drift guard self-test passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prepared", "candidate", "built-lean", "report"): parser.add_argument("--" + name)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test: self_test(); return 0
    if not all((args.prepared, args.candidate, args.built_lean, args.report)): parser.error("all four path arguments are required")
    start = time.monotonic()
    try: report = run(args)
    except (Rejected, OSError, subprocess.CalledProcessError, UnicodeError, ValueError) as exc: report = {"ok": False, "reason": str(exc)}
    report["seconds"] = round(time.monotonic() - start, 2)
    pathlib.Path(args.report).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "checks"}, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
