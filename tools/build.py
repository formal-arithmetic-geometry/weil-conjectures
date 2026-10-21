#!/usr/bin/env python3
"""The global build. Only the agent holding the building function runs it.

It never builds the tree the groups work in. It builds a copy, local/buildtree/, and brings the compiled files back:

  1. Snapshot, under local/tree.lock (seconds): commit the tree, copy the sources into the copy, and for every landing
     still being checked by its group take the previous version of its files. The commit records exactly what is built.
  2. `lake build` in the copy. Landings go on meanwhile; nothing waits for the build.
  3. While it runs, watch local/builds/requests/. When an interface landing arrives (landing.py) and the running build
     contains none, stop the build and start over from a new snapshot, so that the change most likely to break other
     modules is verified first. A build that contains an interface landing is never stopped: what arrives during it
     waits for the next build. So a build is stopped at most once.
  4. Green: the build succeeded. Then publish: copy the changed compiled files into lean/.lake/build, each one written completely before
     it replaces the old one, and close the landings the snapshot contained as verified.
     Red: publish nothing, so the groups keep compiling against the last green build, and list the landings that may
     have caused each failure, interface landings first.

Usage:
  tools/build.py           build until one build completes; exit 0 green or nothing to build, 1 red, 2 cannot start.
                           When nothing has landed, it waits for the next landing (at most SHEAF_BUILD_WAIT seconds,
                           default 600) and builds as soon as it arrives.
  tools/build.py --retry   after a red build: build the same snapshot again with the maintainer's own landings
                           (group M) and without the landings reverted, taking in nothing else that has landed
  tools/build.py --only FILE   build once with exactly the landings whose ids FILE lists (one per line); every other
                           waiting landing is held back (its files at their previous version), no interface restart, no
                           wait. Used by the scheduled upstream sync (~/cc1/upsync-quick.py), run inside ~/cc1/buildloop.sh.
  tools/build.py status    the last result and the landings waiting
Results: local/builds/last.json, the log in local/build.log.

Landings of a batch (tools/batch_land.py; the landing's record carries `batch`) were not compiled one by one on the
server before they landed, so the build checks for them what that compile checked, after `lake build` has succeeded and
before anything is published (batch_checks): every file of theirs compiles alone within SHEAF_FILE_TIMEOUT, no
declaration of their modules uses an axiom beyond propext, Classical.choice and Quot.sound, and none has a `sorry` the
delivery's text check did not see. The time is the one Lake prints for the file in this build; only a file over the
limit there (the build runs many files at once, so its time is an upper bound) is compiled once more, alone, with
tools/lean_file.sh, and fails when that reaches the limit. The axioms and the sorries are read from the compiled modules
by one probe file that imports them. A finding makes the build red, with the module among the failing ones and the
finding in `batch_checks` of last.json.
Options (coord/sheaf.env): SHEAF_BUILD_THREADS (default 3), SHEAF_BUILD_POLL seconds (10).
The packages in lean/.lake/packages are shared with the copy through a link and must never be rebuilt from it: the
build does not start if Lake would rebuild Mathlib. A dependency given by a relative path is not supported.
"""
from __future__ import annotations
import os as _os, sys as _sys
# 2026-10-20: tools/queue.py shadows the stdlib `queue` (the script's directory is sys.path[0]); concurrent.futures
# needs the stdlib one (ThreadPoolExecutor: "module 'queue' has no attribute 'SimpleQueue'"). Import both without
# tools/ on the path; this process never imports tools/queue.py as a module.
_saved = list(_sys.path)
_here = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:] = [p for p in _sys.path if _os.path.abspath(p or ".") != _here]
_sys.modules.pop("queue", None)
import queue as _queue, concurrent.futures  # noqa: E402,F401
_sys.path[:] = _saved
import fcntl, hashlib, json, os, pathlib, re, shutil, signal, subprocess, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
import landing as ld  # noqa: E402
import mergelock  # noqa: E402
from pipeline_guard import alert, clear_alert, source_fingerprint

CFG = li.config()
CLONE = ld.LOCAL / "buildtree"
LOG = ld.B / "build.log"
THREADS = CFG.get("SHEAF_BUILD_THREADS", "3")
POLL = float(CFG.get("SHEAF_BUILD_POLL", "10"))
TOOLS = pathlib.Path(__file__).resolve().parent
LOCK_SECS = float(CFG.get("SHEAF_BUILD_LOCK_TIMEOUT", "900"))  # wait for a running merge to finish


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def commit_tree(inflight: list[dict]):
    """Commit the repository holding the Lean sources, with the previous version of every file of the landings held
    back (newest first, so that the oldest previous version of a file is the one that stays). Called by snapshot()
    with coord/.merge.lock held."""
    top = run(["git", "-C", str(li.LEAN), "rev-parse", "--show-toplevel"])
    if top.returncode != 0:
        return None
    repo = pathlib.Path(top.stdout.strip())
    run(["git", "add", "-A"], cwd=repo)
    for r in inflight:
        for f in r["files"]:
            try:
                rel = str((li.LEAN / f["path"]).relative_to(repo))
            except ValueError:
                continue
            bk = ld.BACKUP / r["id"] / f["path"]
            if f["existed"]:
                h = run(["git", "hash-object", "-w", str(bk)], cwd=repo).stdout.strip()
                run(["git", "update-index", "--add", "--cacheinfo", f"100644,{h},{rel}"], cwd=repo)
            else:
                run(["git", "update-index", "--force-remove", rel], cwd=repo)
    c = run(["git", "commit", "-q", "-m", f"build {ld.now()}"], cwd=repo)
    if c.returncode != 0 and "nothing to commit" not in c.stdout + c.stderr and "nothing added" not in c.stdout + c.stderr:
        print("warning: git commit failed: " + (c.stderr or c.stdout).strip().split("\n")[0])
    return run(["git", "rev-parse", "HEAD"], cwd=repo).stdout.strip() or None


def seed_copy():
    lake = CLONE / ".lake"
    if lake.exists():
        return
    lake.mkdir(parents=True)
    if (li.LEAN / ".lake" / "packages").is_dir():
        (lake / "packages").symlink_to(li.LEAN / ".lake" / "packages")
    if (li.LEAN / ".lake" / "build").is_dir():
        subprocess.run(["cp", "-a", "--reflink=auto", str(li.LEAN / ".lake" / "build"), str(lake / "build")], check=True)


def snapshot(allowed=None):
    """Returns (commit, the landings contained, whether any source changed since the last snapshot).
    Landings still being checked are held back; with `allowed`, so is every waiting landing whose id is not in it.
    The commit and the copy are taken under coord/.merge.lock, as merge_delivery.py writes the tree and commits under
    it: otherwise a build could commit or build a merge's partial tree (2026-10-11 09:58, 2a55d0584). The merge lock is
    taken before local/tree.lock, the order of merge_delivery.py (which runs land.sh under it). None if the merge lock
    is not had within SHEAF_BUILD_LOCK_TIMEOUT."""
    ld.dirs()
    with open(mergelock.LOCK, "a") as lockf:
        try:
            mergelock.acquire(lockf, mergelock.LOCK, LOCK_SECS)
        except mergelock.LockTimeout as e:
            print(f"warning: build skipped, no snapshot taken: {e}")
            return None
        try:
            commit, included, changed = _snapshot(allowed)
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)
    seed_copy()
    return commit, included, changed


def record_unrecorded() -> dict | None:
    """Merge queue: every change of a Lean file since the verified main that no open landing accounts for becomes one
    landing of the writer `U`, so that a red build can drop it like any landing. Called under the merge and tree
    locks. Cost: one `git diff --name-only` against main and a hash of each changed file."""
    repo = li.ROOT
    v = run(["git", "rev-parse", "-q", "--verify", ld.VERIFIED_REF], cwd=repo).stdout.strip()
    if not v:
        return None
    lean_rel = li.LEAN.resolve().relative_to(repo.resolve()).as_posix()
    names = set(run(["git", "diff", "--name-only", v, "--", lean_rel], cwd=repo).stdout.split())
    names |= set(run(["git", "ls-files", "--others", "--exclude-standard", "--", lean_rel], cwd=repo).stdout.split())
    names = {n[len(lean_rel) + 1:] for n in names if n.endswith(".lean") and "/.sandbox/" not in n and "/." not in "/" + n}
    if not names:
        return None
    last, busy = {}, set()
    for r in sorted(ld.records(ld.REQUESTS), key=ld.order_key):
        for f in r["files"]:
            last[f["path"]] = (r, f)
    for r in ld.records(ld.INFLIGHT):
        busy |= {f["path"] for f in r["files"]}
    files = {}
    for rel in sorted(names - busy):
        cur = ld.sha(li.LEAN / rel)
        if rel in last:
            r, f = last[rel]
            if f.get("sha") == cur:
                continue
            st = ld.STAGED / r["id"] / rel
            if not st.is_file() and not f.get("deleted"):
                continue            # a landing from before the merge queue: its own version is not kept
            before = st.read_bytes() if st.is_file() else None
        else:
            b = subprocess.run(["git", "show", f"{v}:{lean_rel}/{rel}"], cwd=repo, capture_output=True)
            before = b.stdout if b.returncode == 0 else None
            if (hashlib.sha256(before).hexdigest() if before is not None else None) == cur:
                continue
        files[rel] = before
    if not files:
        return None
    # one landing per writer commit (the last commit touching the file; uncommitted changes together), oldest first, so
    # that a red build drops only the change at fault (2026-10-19: a probe and a stage-2 batch shared one landing)
    groups = {}
    for rel in files:
        dirty = run(["git", "status", "--porcelain", "--", f"{lean_rel}/{rel}"], cwd=repo).stdout.strip()
        c = "" if dirty else run(["git", "log", "-1", "--format=%ct %h %s", "--", f"{lean_rel}/{rel}"], cwd=repo).stdout.strip()
        groups.setdefault(c, []).append(rel)
    rec = None
    for c in sorted(groups, key=lambda c: (c == "", c)):
        who = c.split(" ", 1)[1] if c else "uncommitted change in the working tree"
        rec = ld.new_record("U", {rel: files[rel] for rel in groups[c]},
                            "unrecorded change of the tree since the verified main; commit: " + who)
        print(f"{ld.now()} merge queue: recorded {len(groups[c])} unrecorded file change(s) as landing {rec['id']} ({who[:80]})", flush=True)
    return rec


def _snapshot(allowed):
    with ld.tree_lock():
        if ld.merge_queue():
            record_unrecorded()
        waiting = ld.records(ld.REQUESTS)
        held = [] if allowed is None else [r for r in waiting if r["id"] not in allowed]
        inflight = sorted(ld.records(ld.INFLIGHT) + held, key=lambda r: r["id"], reverse=True)
        commit = commit_tree(inflight)
        CLONE.mkdir(parents=True, exist_ok=True)
        r = run(["rsync", "-a", "-i", "--delete", "--exclude=/.lake", "--exclude=/.sandbox", "--exclude=/.quarantine",
                 "--exclude=/.git", f"{li.LEAN}/", f"{CLONE}/"])
        if r.returncode != 0:
            raise SystemExit("rsync failed: " + r.stderr.strip())
        changed = any(x and not x.startswith(".d") for x in r.stdout.split("\n"))
        for rec in inflight:
            for f in rec["files"]:
                dst, bk = CLONE / f["path"], ld.BACKUP / rec["id"] / f["path"]
                if f["existed"]:
                    shutil.copy2(bk, dst)
                elif dst.exists():
                    dst.unlink()
        included = [r for r in waiting if allowed is None or r["id"] in allowed]
    return commit, included, changed


def packages_ok() -> bool:
    if not (li.LEAN / ".lake" / "packages" / "mathlib").is_dir():
        return True
    h = hashlib.sha256()
    for n in ("lake-manifest.json", "lean-toolchain", "lakefile.toml", "lakefile.lean"):
        if (CLONE / n).is_file():
            h.update((CLONE / n).read_bytes())
    stamp = CLONE / ".lake" / "sheaf_packages_ok"
    if stamp.is_file() and stamp.read_text() == h.hexdigest():
        return True
    r = run(["lake", "build", "--no-build", "Mathlib"], cwd=CLONE)
    if r.returncode != 0:
        print("Lake would rebuild Mathlib from the build copy, inside the packages directory that lean/ shares with it; "
              "the build was not started.\nRun `lake exe cache get` in lean/ and check that lake-manifest.json and "
              "lean-toolchain are the ones Mathlib was fetched for.\n" + (r.stdout + r.stderr)[-600:])
        return False
    stamp.write_text(h.hexdigest())
    return True


def failing_modules(log: str) -> list[str]:
    out = re.findall(r"^✖ \[\d+/\d+\] \w+ (\S+)", log, re.M)
    m = re.search(r"Some required \w+ logged failures:\n((?:- .*\n?)+)", log)
    if m:
        out += [x[2:].strip() for x in m.group(1).split("\n") if x.startswith("- ")]
    return sorted(set(out))


def suspects(failing: list[str], included: list[dict]) -> list[dict]:
    imports = {}
    for d in li.library_dirs():
        for p in (CLONE / d).rglob("*.lean"):
            imports[".".join(p.relative_to(CLONE).with_suffix("").parts)] = li.imports_of(p.read_text(errors="ignore"))
    memo: dict = {}
    out = []
    for r in included:
        mods = {f["module"] for f in r["files"]}
        hit = [m for m in failing if m in mods or mods & li.closure(m, imports, memo)]
        if hit or not failing:
            out.append({"id": r["id"], "group": r["group"], "kind": r["kind"], "modules": sorted(mods)[:8],
                        "fails": hit[:8], "landed": r.get("landed", "")})
    out.sort(key=lambda s: s["landed"], reverse=True)
    return sorted(out, key=lambda s: s["kind"] != "interface")


def build_times(log: str) -> dict[str, float]:
    """module -> the seconds Lake printed for building it (`✔ [n/N] Built M (9.6s)`; ms, s, and m/h if Lake prints them)."""
    out = {}
    for m, t in re.findall(r"^\S \[\d+/\d+\] Built (\S+) \(([^)]*)\)", log, re.M):
        out[m] = sum(float(v) * {"ms": .001, "s": 1, "m": 60, "h": 3600}[u] for v, u in re.findall(r"([\d.]+)\s*(ms|s|m|h)", t))
    return out


# Appended to a file that imports the modules of the batch: for every constant of each module, its axioms beyond the
# three allowed and sorryAx (transitively), and the constants whose own term uses sorryAx (directly); the probe of
# tools/stage3_delivery.py, read from the compiled modules. Tested on the pinned toolchain (v4.33.1), 2026-10-12.
BATCH_PROBE = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : List Name := [%s]
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  for m in mods do
    let some idx := env.getModuleIdx? m | logInfo m!"SHEAF-MISSING {m}"
    let mut cnt : Nat := 0
    for c in env.header.moduleData[idx.toNat]!.constNames do
      let some ci := env.find? c | continue
      let used := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)
      if used.contains ``sorryAx then logInfo m!"SHEAF-SORRY {m} {c}"
      if c.isInternal then continue
      cnt := cnt + 1
      for a in (← Lean.collectAxioms c) do
        unless ok.contains a do logInfo m!"SHEAF-AXIOM {m} {c} {a}"
    logInfo m!"SHEAF-PROBED {m} {cnt}"
"""


def run_probe(mods: list[str], name: str = "BatchProbe", threads: str | None = None) -> dict[str, dict]:
    """module -> {ran, axioms: [(decl, axiom)], sorry: [constant], out}; one Lean run that imports `mods`."""
    d = CLONE / ".sandbox"
    d.mkdir(exist_ok=True)
    f = d / f"{name}.lean"
    # 2026-10-14: the probe imports Lean.Elab.Command itself (a batch of withdrawn, emptied modules imports nothing)
    f.write_text("import Lean.Elab.Command\n" + "".join(f"import {m}\n" for m in mods) + BATCH_PROBE % ",\n    ".join("`" + m for m in mods))
    r = run(["nice", "-n", "0", "timeout", "600", "lake", "env", "lean", str(f)], cwd=CLONE,
            env=dict(os.environ, LEAN_NUM_THREADS=threads or THREADS))
    out = r.stdout + r.stderr
    try:
        if name != "BatchProbe": f.unlink()
    except OSError:
        pass
    res = {}
    for m in mods:
        res[m] = {"ran": bool(re.search(r"SHEAF-PROBED " + re.escape(m) + r" \d+", out)), "out": out[-1500:],
                  "axioms": re.findall(r"SHEAF-AXIOM " + re.escape(m) + r" (\S+) (\S+)", out),
                  "sorry": re.findall(r"SHEAF-SORRY " + re.escape(m) + r" (\S+)", out)}
    return res


def batch_checks(included: list[dict], log: str) -> list[dict]:
    """What the build checks for the landings of a batch (see the top). [{module, kind: overtime|probe, landing,
    message}]; empty when nothing is found or no landing of a batch is included."""
    mods = {}
    for r in included:
        if r.get("batch"):
            for f in r["files"]:
                # 2026-10-20: a root file that only lists imports (an import line put back by a rework landing,
                # tools/rework.py) is no delivered module: loading the whole library is not its own compile time
                if (CLONE / f["path"]).is_file() and f["module"] not in ("WeilConjectures", "TargetsCheck"):
                    mods[f["module"]] = (r, f["path"])
    if not mods:
        return []
    import stage3_delivery as s3
    limit = float(CFG.get("SHEAF_FILE_TIMEOUT", "60"))
    out = []
    for m, secs in sorted(build_times(log).items()):
        if m in mods and secs > limit:
            env = {k: v for k, v in os.environ.items() if k != "SHEAF_GROUP"}
            alone = run(["bash", str(TOOLS / "lean_file.sh"), str(CLONE / mods[m][1])],
                        env=dict(env, SHEAF_TREE=str(CLONE), SHEAF_FILE_TIMEOUT=f"{limit:g}"))
            if alone.returncode == 124:
                out.append({"module": m, "kind": "overtime", "landing": mods[m][0]["id"],
                            "message": f"{m} took {secs:g} s in the global build and does not compile alone within "
                                       f"{limit:g} s, the limit for one file (SHEAF_FILE_TIMEOUT; tools/lean_file.sh): the "
                                       "cause is a definition the file uses; find it and change it."})
    todo = sorted(m for m in mods if m not in {c["module"] for c in out})
    res = run_probe(todo) if todo else {}
    alone = [m for m in todo if not res[m]["ran"]] if len(todo) > 1 else []
    if alone:
        # one module of the set stopped the common run: each of the others alone, 16 at a time (2026-10-20: one by one,
        # up to 600 s each, they added tens of minutes to a build of ~120 landings)
        import concurrent.futures
        t0 = time.time()
        with concurrent.futures.ThreadPoolExecutor(max_workers=int(CFG.get("SHEAF_PROBE_PARALLEL", "16"))) as ex:
            for m, r1 in zip(alone, ex.map(lambda x: run_probe([x], "BatchProbe_" + x.replace(".", "_"), "2")[x], alone)):
                res[m] = r1
        print(f"batch probe: {len(alone)} module(s) probed alone in parallel in {time.time() - t0:.0f} s", flush=True)
    for m in todo:
        r, (rec, path) = res[m], mods[m]
        if not r["ran"] and ("environment already contains" in r["out"] or re.search(r"BatchProbe\.lean:\d+:\d+: error: unknown (namespace|identifier|constant)", r["out"])):
            # 2026-10-14 (launcher): the probe file is outside the module system, so its plain imports load private
            # declarations too and collide where the module system does not; the global build compiled the module, and
            # deliver3 probed each delivered file at delivery. 82 of 101 take-outs that day were this, not the delivery.
            print(f"note: the batch probe could not import {m} (an import collision of the probe file only); not taken out")
            continue
        if not r["ran"]:
            out.append({"module": m, "kind": "probe", "landing": rec["id"],
                        "message": f"the axiom and sorry probe did not run on {m}: " + " | ".join(r["out"].strip().splitlines()[-8:])})
            continue
        for decl, a in sorted(set(r["axioms"])):
            out.append({"module": m, "kind": "probe", "landing": rec["id"],
                        "message": f"{path}: {decl} uses the axiom {a} (AGENTS.md §4: only {', '.join(s3.OK_AXIOMS)})"})
        table = s3.decl_table((CLONE / path).read_text(errors="ignore"))
        allowed = set((rec.get("sorry_allowed") or {}).get(m) or [])
        extra = sorted({s3.owner(c, table) for c in r["sorry"]} - allowed)
        if extra:
            out.append({"module": m, "kind": "probe", "landing": rec["id"],
                        "message": f"{path}: Lean finds `sorry` in {', '.join(extra)}, which the text check did not "
                                   "(a macro or an elaborator inserted it)"})
    return out


def publish():
    marker = ld.LOCAL / "PUBLISHING"
    marker.write_text(ld.now())
    try:
        dst = li.LEAN / ".lake" / "build"
        dst.mkdir(parents=True, exist_ok=True)
        r = run(["rsync", "-a", "--delete", "--delay-updates", f"{CLONE / '.lake' / 'build'}/", f"{dst}/"])
        if r.returncode != 0:
            raise SystemExit("publishing failed: " + r.stderr.strip())
        lib = dst / "lib" / "lean"
        if lib.is_dir():
            os.utime(lib)
        (ld.B / "published").write_text(ld.now())
    finally:
        marker.unlink(missing_ok=True)


def _mark_verified(included):
    """the human, 2026-10-22: a landing the green build verified marks its item done (tools/queue_mark.py)"""
    try:
        import subprocess as _sp, sys as _sy
        by_stage = {}
        for r in included:
            st = str(r.get("stage") or "-")
            d = r.get("delivery") or {}
            if isinstance(d, dict) and d.get("item") and "." not in str(d.get("item")):
                by_stage.setdefault(st, set()).add(str(d["item"]))
            for c in r.get("changed") or []:
                mod = str(c).split()[0] if str(c).strip() else ""
                if mod and "." in mod:
                    by_stage.setdefault("3" if st == "-" else st, set()).add(mod)
        for st, items in by_stage.items():
            _sp.run([_sy.executable, str(li.ROOT / "tools" / "queue_mark.py"), "done", st, *sorted(items)],
                    capture_output=True, timeout=120)
    except Exception:
        pass


def close_verified(included: list[dict], commit):
    for r in included:
        r.update(result="verified", commit=commit, closed=ld.now())
        ld.write_json(ld.DONE / f"{r['id']}.json", r)
        (ld.REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
        shutil.rmtree(ld.BACKUP / r["id"], ignore_errors=True)
        shutil.rmtree(ld.STAGED / r["id"], ignore_errors=True)
    old = time.time() - 7 * 86400
    for p in ld.DONE.glob("*.json"):
        if p.stat().st_mtime < old:
            p.unlink()


def status() -> int:
    return ld.status(None, None)


def main() -> int:
    if sys.argv[1:] == ["status"]:
        return status()
    wait, retry = True, sys.argv[1:] == ["--retry"]
    only = None
    if len(sys.argv) == 3 and sys.argv[1] == "--only":
        only = {x for x in pathlib.Path(sys.argv[2]).read_text().split() if x and not x.startswith("#")}
        wait = False
    if sys.argv[1:] and not retry and only is None:
        print(__doc__); return 2
    ld.dirs()
    guard = open(ld.B / "build.lock", "w")
    try:
        fcntl.flock(guard, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("Another global build is running."); return 2
    preempted, proc = 0, None

    def stop(*_):
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
        sys.exit(2)
    signal.signal(signal.SIGTERM, stop); signal.signal(signal.SIGINT, stop)

    while True:
        while (ld.LOCAL / 'batch/landing.json').exists():
            # No locks held while the fixed cohort is being committed one delivery
            # at a time. The live loop alone compiles when its journal closes.
            marker = ld.LOCAL / 'batch/landing.json'
            if time.time() - marker.stat().st_mtime > 180:
                alert((ld.read_json(marker) or {}).get('id'), '?', 'partial batch landing', 'finish or withdraw the landing journal')
            time.sleep(POLL)
        last = ld.read_json(ld.B / "last.json")
        allowed = None
        if retry:
            if not last or last["result"] != "red":
                print("--retry follows a red build; the last build was not red."); return 2
            allowed = set(last.get("included", [])) | {r["id"] for r in ld.records(ld.REQUESTS) if r["group"] == "M"}
        if only is not None:
            allowed = only
        snap = snapshot(allowed)
        if snap is None:
            return 1
        commit, included, changed = snap
        if not included and not changed and last and last["result"] == "green":
            deadline = time.time() + float(CFG.get("SHEAF_BUILD_WAIT", "600"))
            while wait and time.time() < deadline and not ld.records(ld.REQUESTS):
                time.sleep(POLL)
            if wait and ld.records(ld.REQUESTS):
                continue
            print("Nothing landed since the last green build."); return 0
        source_id = source_fingerprint(CLONE)
        red_trees = ld.read_json(ld.B / 'red-trees.json') or {}
        cached = red_trees.get(source_id)
        if cached and cached.get('compiler_red'):
            result = dict(cached['result'], time=ld.now(), commit=commit, seconds=0,
                          included=sorted(r['id'] for r in included),
                          suspects=suspects(cached['result'].get('failing', []), included))
            ld.write_json(ld.B / 'last.json', result)
            alert((included[0].get('batch') if included else None), ' '.join(result.get('failing', [])),
                  'same red sources requested; compile skipped', 'batch recovery or maintainer source repair')
            print('Known red source tree: cached compiler failure; no rebuild.', flush=True)
            return 1
        if cached and last and last.get('source_fingerprint') == source_id:
            # Lake succeeded before a probe rejected this very source snapshot.
            # Re-read changed request allowances against its compiled output without
            # running Lake again. A record repair can now publish immediately.
            text = (ld.LOCAL / 'build.log').read_text(errors='ignore')
            return finish_result(included, commit, text, 0, preempted, source_id, red_trees, compiler_ok=True)
        if not packages_ok():
            return 2
        ids = {r["id"] for r in included}
        has_interface = any(r["kind"] == "interface" for r in included)
        print(f"{ld.now()} building commit {(commit or '-')[:10]}: {len(included)} landing(s), "
              f"{sum(r['kind'] == 'interface' for r in included)} of them interface", flush=True)
        t0 = time.time()
        # 2026-10-21: what this build contains, for the pipelined landing of tools/batch_land.py (SHEAF_PIPELINE_BATCHES)
        ld.write_json(ld.B / "current.json", {"time": ld.now(), "commit": commit, "included": sorted(ids),
                                              "has_interface": has_interface, "pid": os.getpid(),
                                              "mode": "retry" if retry else "only" if only is not None else ""})
        with open(LOG, "w") as log:
            proc = subprocess.Popen(["nice", "-n", "0", "lake", "build"], cwd=CLONE, stdout=log, stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_NUM_THREADS=THREADS), start_new_session=True)
            restart = False
            while proc.poll() is None:
                time.sleep(POLL)
                if has_interface or retry or only is not None:
                    continue
                new = [r for r in ld.records(ld.REQUESTS) if r["id"] not in ids and r["kind"] == "interface"]
                if new:
                    os.killpg(proc.pid, signal.SIGTERM)
                    try:
                        proc.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL); proc.wait()
                    preempted += 1; restart = True
                    print(f"{ld.now()} interface landing {new[0]['id']} of {new[0]['group']} arrived: "
                          f"starting over", flush=True)
        if restart:
            continue
        break

    text = LOG.read_text(errors="ignore")
    shutil.copy2(LOG, ld.LOCAL / "build.log")
    try:
        return finish_result(included, commit, text, round(time.time() - t0), preempted, source_id, red_trees,
                             compiler_ok=proc.returncode == 0)
    finally:
        cur = ld.read_json(ld.B / "current.json")
        if cur and cur.get("pid") == os.getpid():
            ld.write_json(ld.B / "current.json", dict(cur, finished=ld.now()))


def finish_result(included, commit, text, elapsed, preempted, source_id, red_trees, *, compiler_ok):
    """Publish or record one live-loop result, including a probe-only record retry."""
    ids = {r['id'] for r in included}
    errors = [x for x in text.split("\n") if x.startswith("error")]
    built = compiler_ok and not errors and "Build completed successfully" in text
    compiler_red = not built
    checks = batch_checks(included, text) if built else []
    if checks:
        built = False
        errors = ["error: " + c["message"] for c in checks]
    result = {"time": ld.now(), "commit": commit, "source_fingerprint": source_id, "seconds": elapsed, "restarts": preempted}
    if built:
        publish()
        close_verified(included, commit)
        _mark_verified(included)
        if commit and ld.merge_queue():
            # the verified main advances to exactly the commit this green build built (merge queue)
            run(["git", "update-ref", ld.VERIFIED_REF, commit], cwd=li.ROOT)
            result["verified_main"] = commit
        result.update(result="green", verified=sorted(ids))
        ld.write_json(ld.B / "last.json", result)
        ld.write_json(ld.B / "published.json", result)
        clear_alert()
        print(f"GREEN in {result['seconds']} s; {len(ids)} landing(s) verified; compiled files published.")
        return 0
    if not built and re.search(r"no space left on device|resource exhausted|Cannot allocate memory|out of memory", text):
        # an infrastructure failure says nothing about the sources: not cached, not attributed, rebuilt by the loop
        print("INFRASTRUCTURE failure (disk or memory); nothing recorded, the same sources will be rebuilt.", flush=True)
        time.sleep(120)
        return 1
    failing = sorted(set(failing_modules(text)) | {c["module"] for c in checks})
    sus = suspects(failing, included)
    result.update(result="red", source_fingerprint=source_id, failing=failing, errors=errors[:30], suspects=sus, included=sorted(ids), batch_checks=checks)
    ld.write_json(ld.B / "last.json", result)
    red_trees[source_id] = {'compiler_red': compiler_red, 'result': result}
    ld.write_json(ld.B / 'red-trees.json', red_trees)
    if not sus or any(c['kind'] == 'probe' and not c.get('landing') for c in checks):
        alert((included[0].get('batch') if included else None), ' '.join(failing), 'unattributed red/probe failure', 'maintainer diagnosis or batch withdrawal')
    print(f"RED in {result['seconds']} s; nothing published. Failing: {' '.join(failing[:12]) or '-'}")
    for x in errors[:12]:
        print("  " + x[:300])
    if sus:
        print("Landings that may have caused it, most likely first:")
        for s in sus[:12]:
            print(f"  {s['id']}  {s['kind']:9} {s['group']:6} {' '.join(s['modules'][:4])}"
                  + (f"  -> fails {' '.join(s['fails'][:3])}" if s["fails"] else ""))
    print("Make it green (roles/maintainer.md §2) and run tools/build.py --retry.")
    if sus:
        print("To give a landing back: tools/landing.py revert <id> <reason>.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
