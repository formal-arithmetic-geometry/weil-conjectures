#!/usr/bin/env python3
"""2026-10-15: compile side-project files singly; live source/build are read-only.

nt_compile.py FILE.lean or --json with {files: {path/under/lean.lean: text}} on stdin.
Every process has nice 19, two Lean threads and a hard 60 second per-file timeout.
Sibling modules, side-only imports and explicit side interface overrides compile
first into a private temporary directory.
No lake invocation, build request, or artifact is written into the live project.
"""
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time

from nt_source_overlay import load_overrides, source_for_import

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIVE = pathlib.Path(os.environ.get("SHEAF_LIVE_LEAN") or str(ROOT / "lean" if (ROOT / "lean/.lake/build").is_dir() else pathlib.Path.home() / "weil-conjectures-sheaf/lean")).resolve()   # 2026-10-19: this repository's published build
# 2026-10-17 (churn): every call recompiled all side overrides and the whole chain of side-only imports (dozens of modules, each up to 60 s at nice 19) before
# its own files; under load 160 one stage-2 review compile took 12-18 minutes and the reviews timed out at $0.
# Override artifacts are reused from this cache, keyed by the source text, the Lean options and binary, and the
# artifacts each import resolves to (a published .olean by path, size and mtime; a private one by its own key).
OVERRIDE_CACHE = pathlib.Path("/dev/shm/nt-tmp/override-cache")
COMPANIONS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def main():
    os.nice(max(0, 19 - os.getpriority(os.PRIO_PROCESS, 0)))
    if sys.argv[1:] == ["--json"]:
        files = json.load(sys.stdin)["files"]
    else:
        f = pathlib.Path(sys.argv[1]).resolve()
        try:
            rel = f.relative_to(ROOT / "lean").as_posix()
        except ValueError:
            raise SystemExit("Compile input must be in the side project's lean tree")
        if rel.startswith(".sandbox/"):
            rel = "Sheaf/Stage2/" + f.stem.replace("-", "_") + ".lean"
        files = {rel: f.read_text()}
    if not files:
        raise SystemExit("No files")
    overrides = load_overrides(ROOT)
    for rel, text in files.items():
        p = pathlib.PurePosixPath(rel)
        if p.is_absolute() or ".." in p.parts or p.suffix != ".lean":
            raise SystemExit("Invalid relative Lean path: " + rel)
    import tomllib
    cfg = tomllib.loads((LIVE / "lakefile.toml").read_text())
    def options(table, prefix=""):
        for k, v in table.items():
            key = prefix + k
            if isinstance(v, dict):
                yield from options(v, key + ".")
            else:
                yield f"-D{key}={str(v).lower() if isinstance(v, bool) else v}"
    opts = list(options(cfg.get("leanOptions", {})))
    published = LIVE / ".lake/build/lib/lean"
    packages = sorted((LIVE / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not published.is_dir():
        raise SystemExit("Live published library is unavailable")
    with tempfile.TemporaryDirectory(prefix="nt-stage2-", dir="/dev/shm/nt-tmp") as tmp:
        tree = pathlib.Path(tmp)
        objects = tree / "objects"
        objects.mkdir()
        # Override only private modules. A link farm for the whole published
        # package created about 85k filesystem entries per request and saturated
        # the journal with hundreds of concurrent fallback requests.
        lp = ":".join(str(p) for p in [published, *packages])
        artifacts = {}
        done, active = set(), set()
        keys = {}
        import hashlib, shutil as _sh
        lean_bin = pathlib.Path.home() / ".elan/bin/lean"
        try:
            lean_id = str(lean_bin.resolve()) + str(lean_bin.resolve().stat().st_mtime_ns)
        except OSError:
            lean_id = str(lean_bin)

        def override_key(rel, text):
            h = hashlib.sha256()
            h.update(json.dumps([rel, text, opts, lean_id]).encode())
            for imp in IMPORT.findall(text):
                dep = imp.replace(".", "/") + ".lean"
                if dep in keys:
                    h.update(("P" + keys[dep]).encode()); continue
                for base in [published, *packages]:
                    f = base / (dep[:-5] + ".olean")
                    if f.is_file():
                        st = f.stat(); h.update(f"O{f}:{st.st_size}:{st.st_mtime_ns}".encode()); break
                else:
                    h.update(("M" + dep).encode())
            return h.hexdigest()

        def from_cache(rel, key):
            d = OVERRIDE_CACHE / key
            if not (d / "ok").is_file():
                return False
            stem = d / pathlib.PurePosixPath(rel).stem
            def have(suffixes):
                paths = []
                for suffix in suffixes:
                    path = pathlib.Path(str(stem) + suffix)
                    if not path.is_file():
                        break
                    paths.append(str(path))
                return paths
            artifacts[rel[:-5].replace("/", ".")] = [have(COMPANIONS[:3]), have(COMPANIONS[3:])]
            print(f"{rel}: cached side override", flush=True)
            return True

        def to_cache(rel, key):
            try:
                OVERRIDE_CACHE.mkdir(parents=True, exist_ok=True)
                tmpd = pathlib.Path(tempfile.mkdtemp(prefix=".tmp-", dir=OVERRIDE_CACHE))
                stem = objects / rel[:-5]
                for suffix in COMPANIONS:
                    f = pathlib.Path(str(stem) + suffix)
                    if f.is_file():
                        _sh.copy2(f, tmpd / (pathlib.PurePosixPath(rel).stem + suffix))
                (tmpd / "ok").write_text(rel + "\n")
                try:
                    os.rename(tmpd, OVERRIDE_CACHE / key)
                except OSError:
                    _sh.rmtree(tmpd, ignore_errors=True)   # another process stored it first
            except OSError:
                pass

        def compile_one(rel, text):
            if rel in done:
                return
            if rel in active:
                raise SystemExit("Import cycle: " + rel)
            active.add(rel)
            for imp in IMPORT.findall(text):
                dep = imp.replace(".", "/") + ".lean"
                if dep in files:
                    compile_one(dep, files[dep])
                    continue
                # Frozen live copies stay on published artifacts; explicitly listed
                # side replacements must expose the interface of the side DAG record.
                side = source_for_import(ROOT, LIVE, dep, overrides)
                if side is not None:
                    compile_one(dep, side.read_text())
            cacheable = rel not in files and all(   # every side-sourced module (overrides and side-only imports)
                d in keys for d in (i.replace(".", "/") + ".lean" for i in IMPORT.findall(text)) if d in done)
            key = override_key(rel, text) if cacheable else None
            if key and from_cache(rel, key):
                keys[rel] = key; done.add(rel); active.remove(rel)
                return
            src = tree / rel
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text(text)
            out = objects / (rel[:-5] + ".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            setup = tree / "setup.json"
            setup.write_text(json.dumps({
                "name": rel[:-5].replace("/", "."), "isModule": False,
                "importArts": artifacts, "dynlibs": [], "plugins": [], "options": {}}))
            upstream = rel.startswith(("WeilConjectures/", "Comparator/"))
            cmd = [str(pathlib.Path.home() / ".elan/bin/lean"), *opts,
                   *([] if upstream else ["-DautoImplicit=false"]),
                   "-R", str(tree), "-o", str(out), "--setup", str(setup), str(src)]
            start = time.monotonic()
            try:
                p = subprocess.run(cmd, cwd=LIVE,
                                   env=dict(os.environ, LEAN_PATH=lp, LEAN_NUM_THREADS="2"),
                                   capture_output=True, text=True, timeout=60)
                output = (p.stdout + p.stderr).replace(str(tree) + "/", "")
                print(output, end="", flush=True)
                print(f"{rel}: {time.monotonic()-start:.1f} s; nice 19; 2 threads; limit 60 s", flush=True)
                if p.returncode:
                    raise SystemExit(p.returncode)
            except subprocess.TimeoutExpired as exc:
                # A later slow declaration must not erase errors from earlier
                # declarations. TimeoutExpired can contain bytes with text=True.
                partial = "".join(
                    value.decode(errors="replace") if isinstance(value, bytes) else value or ""
                    for value in (exc.stdout, exc.stderr))
                print(partial.replace(str(tree) + "/", ""),
                      end="" if not partial or partial.endswith("\n") else "\n", flush=True)
                raise SystemExit(f"{rel}: timeout after 60 s")
            # Lean needs the IR and private/server companions of transitive
            # private imports too, exactly as the launcher's lcompile does.
            stem = objects / rel[:-5]
            def companions(suffixes):
                paths = []
                for suffix in suffixes:
                    path = pathlib.Path(str(stem) + suffix)
                    if not path.is_file():
                        break
                    paths.append(str(path))
                return paths
            artifacts[rel[:-5].replace("/", ".")] = [
                companions((".olean", ".olean.server", ".olean.private")),
                companions((".ir.sig", ".ir"))]
            if key:
                to_cache(rel, key); keys[rel] = key
            done.add(rel)
            active.remove(rel)

        # A published importer can reach an override without visiting its side
        # source. Register every explicit replacement before loading any such
        # artifact, including its transitive private/server/IR companions.
        for rel in sorted(overrides):
            compile_one(rel, files.get(rel, (ROOT / "lean" / rel).read_text()))
        for rel, text in files.items():
            compile_one(rel, text)


if __name__ == "__main__":
    main()
