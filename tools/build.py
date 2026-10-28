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
before anything is published (batch_checks): no declaration of their modules uses an axiom beyond propext,
Classical.choice and Quot.sound, and none has a `sorry` the delivery's text check did not see. Their compile time is not
checked here (2026-10-25, the human: the delivery's own single-file compile is enough; the 60 s re-time at landing ran
at nice 19 under full load and took out two deliveries that compile). The axioms and the sorries are read from the
compiled modules by one probe file that imports them. A finding makes the build red, with the module among the failing ones and the
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
FAILFAST = CFG.get("SHEAF_BUILD_FAILFAST", "1") == "1"
FAILFAST_GRACE = int(CFG.get("SHEAF_BUILD_FAILFAST_GRACE", "90"))
POLL = float(CFG.get("SHEAF_BUILD_POLL", "10"))
TOOLS = pathlib.Path(__file__).resolve().parent
LOCK_SECS = float(CFG.get("SHEAF_BUILD_LOCK_TIMEOUT", "900"))  # wait for a running merge to finish


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def superseded(inflight: list[dict], included: list[dict]) -> set:
    """(record id, path) of the held-back files that a newer included landing wrote. 2026-10-26: a retry holds back the
    landings after the red build; their previous version of a file was put back even when a newer included take-out
    (tools/red_rework.py, group L) had moved the file to quarantine/, so the retry built the importer of a removed module
    again ("bad import" UniformConstructibleExt, retry 5 of 13:20:40). The newer included landing's version stays."""
    last = {}
    for r in included:
        for f in r.get("files") or []:
            last[f["path"]] = max(last.get(f["path"], 0), r.get("seq") or 0)
    # 2026-10-27: not for the root files that only list imports: an included landing's version of them is written on
    # top of the held-back landing's import lines (retry 2 of 16:26:22: TargetsCheck kept the line of
    # WeilConjectures.PoincareDuality.Poincare, whose held-back restore was taken out of the build copy); for those the
    # held-back version is put back as before and clean_root_imports() drops the lines of modules not in the copy
    return {(r["id"], f["path"]) for r in inflight for f in r.get("files") or []
            if last.get(f["path"], 0) > (r.get("seq") or 0) and f["path"] not in ROOT_FILES}


ROOT_FILES = ("WeilConjectures.lean", "TargetsCheck.lean")


def clean_root_imports() -> None:
    """In the build copy, the root files that only list imports lose the lines of project modules the copy does not
    have (a held-back or taken-out module): they would fail the build with "bad import" / "no such file"."""
    for rel in ROOT_FILES:
        f = CLONE / rel
        if not f.is_file():
            continue
        t = f.read_text(errors="ignore"); keep, gone = [], []
        for line in t.split("\n"):
            m = re.match(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)\s*$", line)
            if m and m.group(1).startswith(("Sheaf.", "WeilConjectures.")) and not _clone_file(m.group(1)):
                gone.append(m.group(1)); continue
            keep.append(line)
        if gone:
            f.write_text("\n".join(keep))
            print(f"{ld.now()} build copy: {rel} without the import line(s) of {len(gone)} module(s) not in the copy: "
                  f"{' '.join(gone[:6])}", flush=True)


def _clone_file(m: str) -> bool:
    p = CLONE.joinpath(*m.split(".")).with_suffix(".lean")
    return p.is_file() or CLONE.joinpath("Comparator", *m.split(".")).with_suffix(".lean").is_file()


def blocked_targets() -> list[str]:
    """2026-10-26 (the human): target libraries blocked by a quarantine (tools/red_rework.py) are left out until every
    module they need is back; then local/builds/blocked-targets.json is removed and everything builds again. [] = the
    default targets. 2026-10-27 00:30: computed on the BUILD COPY (local/buildtree), not on lean/: a retry holds back
    landings, so WeilConjectures.Statement was in lean/ (a held-back restore) but not in the build copy; the block was
    released and Solution failed with "no such file" (retries 1-3 of 16:26:22). Also run before the red-tree cache
    lookup, and its result is part of the cache key (source_id), so a cached red of the unblocked targets is not reused
    once the library is blocked."""
    bf = ld.B / "blocked-targets.json"
    bt = ld.read_json(bf) or {}
    try:
        for lib, rel in (("Solution", "Comparator/Weil/Solution.lean"), ("SheafChallenge", "Challenge.lean")):
            rf = CLONE / rel
            if not rf.is_file():
                continue
            seen, st, miss = set(), list(li.imports_of(rf.read_text(errors="ignore"))), []
            while st:
                m = st.pop()
                if m in seen or not m.startswith(("Sheaf.", "WeilConjectures.", "Comparator.", "Weil.")):
                    continue
                seen.add(m)
                fm = CLONE.joinpath(*m.split(".")).with_suffix(".lean")
                if not fm.is_file():
                    fm = CLONE.joinpath("Comparator", *m.split(".")).with_suffix(".lean")
                if fm.is_file():
                    st.extend(li.imports_of(fm.read_text(errors="ignore")))
                else:
                    miss.append(m)
            if miss:
                bt.setdefault("libs", {})[lib] = sorted(set(bt.get("libs", {}).get(lib, [])) | set(miss))
                bt.setdefault("since", ld.now())
                ld.write_json(bf, bt)
    except Exception as e:  # noqa: BLE001
        print(f"{ld.now()} blocked-target scan failed: {e!r}", flush=True)
    if not bt.get("libs"):
        return []
    libs = {lib for lib, mods in bt["libs"].items() if any(not _clone_file(m) for m in mods)}
    if not libs:
        bf.unlink(missing_ok=True)
        print(f"{ld.now()} blocked target libraries released: their modules are back", flush=True)
        return []
    m_ = re.search(r'^defaultTargets\s*=\s*\[([^\]]*)\]', (CLONE / "lakefile.toml").read_text(), re.M)
    targets = [x for x in re.findall(r'"([^"]+)"', m_.group(1)) if x not in libs] if m_ else []
    print(f"{ld.now()} target libraries blocked by quarantined modules (rework first lane): "
          f"{' '.join(sorted(libs))}; building {' '.join(targets)}", flush=True)
    return targets


def commit_tree(inflight: list[dict], skip: set = frozenset(), prune: set = frozenset()):
    """Commit the repository holding the Lean sources, with the previous version of every file of the landings held
    back (newest first, so that the oldest previous version of a file is the one that stays), and without the files of
    `prune` (quarantine_waiters). Called by snapshot() with coord/.merge.lock held."""
    top = run(["git", "-C", str(li.LEAN), "rev-parse", "--show-toplevel"])
    if top.returncode != 0:
        return None
    repo = pathlib.Path(top.stdout.strip())
    run(["git", "add", "-A"], cwd=repo)
    for r in inflight:
        for f in r["files"]:
            if (r["id"], f["path"]) in skip:
                continue
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
    for path in sorted(prune):
        try:
            rel = str((li.LEAN / path).relative_to(repo))
        except ValueError:
            continue
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


QUARANTINE = li.ROOT / "quarantine"


def _module_of_rel(rel: str) -> str:
    return rel[:-len(".lean")].replace("/", ".")


def quarantine_waiters(inflight: list[dict], skip: set) -> set:
    """Paths (relative to lean/) left out of the candidate because the module imports, directly or through modules so
    left out, a module that is still quarantined (its file is in quarantine/ and not in the candidate). They wait for
    their import's fix and the cluster restore; they are not built, so they are neither verified nor failing.
    2026-10-27 (red build 15:04:17Z, retry 1 of 6db8f8a0f6): a held-back landing's previous version put 2747 modules back
    into the candidate (the merge queue had recorded their move to quarantine/ by 11828f6cc28 as an unrecorded change
    U-561877-146, after land_rest had landed the restores that wrote them); their imports (RingedForgetTensorTranspositionData
    and others) were quarantined, so the build failed with "no such file" / "bad import" in ~3000 modules and the
    red handling moved 2747 importers to quarantine/ again. The candidate = lean/ with the held-back landings' previous
    versions (the same order as commit_tree and the copy)."""
    if not QUARANTINE.is_dir():
        return set()
    final = {}                       # path -> backup file of its candidate version, or None (absent)
    for rec in inflight:
        for f in rec["files"]:
            if (rec["id"], f["path"]) in skip:
                continue
            final[f["path"]] = (ld.BACKUP / rec["id"] / f["path"]) if f["existed"] else None

    qrels = {q.relative_to(QUARANTINE).as_posix() for q in QUARANTINE.rglob("*.lean")}
    # a held-back version of a module that is in quarantine/ and not in lean/ does not bring it back: it waits too
    revived = {rel for rel, b in final.items() if b is not None and rel in qrels and not (li.LEAN / rel).is_file()}

    def present(rel: str) -> bool:
        if rel in revived:
            return False
        return final[rel] is not None if rel in final else (li.LEAN / rel).is_file()

    quarantined = {_module_of_rel(rel): rel for rel in qrels if not present(rel)}
    if not quarantined:
        return set()

    def text(rel: str) -> str:
        p = final.get(rel) if rel in final else li.LEAN / rel
        try:
            return p.read_text(errors="ignore") if p is not None else ""
        except OSError:
            return ""

    dirs = [str(li.LEAN / d) for d in li.library_dirs() if (li.LEAN / d).is_dir()]
    waiting, absent = set(), set(quarantined)
    new = set(quarantined)
    for _ in range(64):
        if not new:
            break
        pats = sorted(new)
        r = subprocess.run(["grep", "-rlF", "--include=*.lean", "--exclude-dir=.sandbox", "--exclude-dir=.lake",
                            "-f", "/dev/stdin", *dirs], input="\n".join(pats) + "\n", capture_output=True, text=True)
        hits = {pathlib.Path(x).relative_to(li.LEAN).as_posix() for x in r.stdout.split("\n") if x}
        hits |= {rel for rel, b in final.items() if b is not None}      # the held-back versions are not in lean/
        new = set()
        for rel in hits:
            if rel in waiting or not present(rel):
                continue
            if li.imports_of(text(rel)) & absent:
                waiting.add(rel)
                m = _module_of_rel(rel)
                if m not in absent:
                    absent.add(m); new.add(m)
    return waiting | revived


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
        _hid = {r["id"] for r in held}
        skip = superseded(held, [r for r in waiting if r["id"] not in _hid]) if held else set()
        try:
            prune = quarantine_waiters(inflight, skip)
        except Exception as e:   # noqa: BLE001  (the guard never stops a build)
            prune = set()
            print(f"{ld.now()} quarantine-waiter scan failed: {e!r}"[:300], flush=True)
        if prune:
            print(f"{ld.now()} build copy: {len(prune)} module(s) left out, they import still-quarantined modules (they "
                  f"wait for the restore): {' '.join(sorted(_module_of_rel(x) for x in prune)[:6])}", flush=True)
        commit = commit_tree(inflight, skip, prune)
        CLONE.mkdir(parents=True, exist_ok=True)
        r = run(["rsync", "-a", "-i", "--delete", "--exclude=/.lake", "--exclude=/.sandbox", "--exclude=/.quarantine",
                 "--exclude=/.git", f"{li.LEAN}/", f"{CLONE}/"])
        if r.returncode != 0:
            raise SystemExit("rsync failed: " + r.stderr.strip())
        changed = any(x and not x.startswith(".d") for x in r.stdout.split("\n"))
        for rec in inflight:
            for f in rec["files"]:
                if (rec["id"], f["path"]) in skip:
                    continue
                dst, bk = CLONE / f["path"], ld.BACKUP / rec["id"] / f["path"]
                if f["existed"]:
                    shutil.copy2(bk, dst)
                elif dst.exists():
                    dst.unlink()
        for path in prune:
            (CLONE / path).unlink(missing_ok=True)
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


PROJECT_PREFIXES = ("Sheaf.", "WeilConjectures.", "Comparator.", "Weil.")
_MISSING_IMPORT = re.compile(r"bad import|no such file or directory|object file .* does not exist|unknown module prefix", re.I)


def _own_error(text: str, m: str) -> bool:
    """True when the build log has an error of `m` other than a missing import (its own failure)."""
    path = m.replace(".", "/") + ".lean"
    for line in text.split("\n"):
        if path in line and "error" in line and not _MISSING_IMPORT.search(line):
            return True
    return False


def failing_modules(log: str) -> list[str]:
    out = re.findall(r"^✖ \[\d+/\d+\] \w+ (\S+)", log, re.M)
    m = re.search(r"Some required \w+ logged failures:\n((?:- .*\n?)+)", log)
    if m:
        out += [x[2:].strip() for x in m.group(1).split("\n") if x.startswith("- ")]
    return sorted(set(out))


def clone_imports() -> dict:
    """module -> its imports, for the sources of the build copy (exactly what this build compiled)."""
    imports = {}
    for d in li.library_dirs():
        for p in (CLONE / d).rglob("*.lean"):
            imports[".".join(p.relative_to(CLONE).with_suffix("").parts)] = li.imports_of(p.read_text(errors="ignore"))
    for p in CLONE.glob("*.lean"):
        imports[p.stem] = li.imports_of(p.read_text(errors="ignore"))
    return imports


def save_graph(commit, graph) -> None:
    """The import graph of the build copy, for tools/batch_land.py land_rest (local/builds/last-graph.pkl)."""
    import pickle
    tmp = ld.B / "last-graph.pkl.tmp"
    with open(tmp, "wb") as fh:
        pickle.dump({"commit": commit, "graph": graph}, fh, protocol=pickle.HIGHEST_PROTOCOL)
    os.replace(tmp, ld.B / "last-graph.pkl")


def clean_landings(included, failing, text, checks, graph):
    """2026-10-25 (the human: each build finds what fails, those go out, the rest lands from that same build): the
    landings of a red build none of whose modules failed or imports (transitively) a failing module; they compiled in
    this build. Their batch checks (probe, time) run here as for a green build. Returns (ids, checks, failing)."""
    if not failing or "build cycle detected" in text or not re.search(r"Some required \w+ logged failures", text):
        return [], checks, failing          # an incomplete or unreadable red: nothing lands from it
    def ok(failing):
        blocked = set(failing) | li.downstream(set(failing), graph)
        return [r for r in included if not ({f["module"] for f in r["files"]} & blocked)]
    cand = ok(failing)
    if cand and not checks:
        more = batch_checks(cand, text)
        if more:
            checks = more
            failing = sorted(set(failing) | {c["module"] for c in more})
            cand = ok(failing)
    return sorted(r["id"] for r in cand), checks, failing


def suspects(failing: list[str], included: list[dict], imports: dict | None = None) -> list[dict]:
    if imports is None:
        imports = clone_imports()
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
    # 2026-10-25 (the human): no 60 s re-time at landing; the delivery's own single-file compile already met the
    # limit (a re-time under full load at nice 19 took out files that compile in 15-41 s)
    out = []
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


GEN = ld.B / "publish-gen"
_GEN_N: list = []


def _gen_write(n: int, state: str) -> None:
    tmp = GEN.with_name(GEN.name + f".tmp{os.getpid()}")
    tmp.write_text(f"{n} {state}\n")
    os.replace(tmp, GEN)


def gen_begin() -> None:
    """2026-10-28 (set builds, tools/setbuild.py): local/builds/publish-gen is "N publishing" from before the rsync of
    a publish until published.json and the verified records are written ("N done", gen_done): a set build reads the
    frozen tree's version at its start and refuses its result when the version changed by its end."""
    try:
        n = int(GEN.read_text().split()[0])
    except (OSError, ValueError, IndexError):
        n = 0
    _GEN_N[:] = [n + 1]
    _gen_write(n + 1, "publishing")


def gen_done() -> None:
    if _GEN_N:
        _gen_write(_GEN_N[0], "done")


def publish():
    gen_begin()
    marker = ld.LOCAL / "PUBLISHING"
    marker.write_text(ld.now())
    try:
        dst = li.LEAN / ".lake" / "build"
        dst.mkdir(parents=True, exist_ok=True)
        r = run(["rsync", "-a", "--delete", "--delay-updates", "--exclude=/ir", f"{CLONE / '.lake' / 'build'}/", f"{dst}/"])   # C output: nobody compiles native code from the published copy
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
            # 2026-10-25 (the human: a red round is retried on the same snapshot until green): the landings the red
            # handling itself wrote are take-outs, not new work: the rework move of a failing module no landing wrote
            # (tools/red_rework.py), the public imports the compiler named, an import cycle broken. Held back, they
            # would put the failing module back into the retry.
            allowed |= {r["id"] for r in ld.records(ld.REQUESTS) if r["group"] == "L" and str(r.get("time", "")) >= str(last.get("time", ""))
                        and str(r.get("note", "")).startswith(("red build", "break import cycle"))}
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
        clean_root_imports()
        targets = blocked_targets()
        source_id = source_fingerprint(CLONE) + (('|targets:' + ','.join(targets)) if targets else '')
        red_trees = ld.read_json(ld.B / 'red-trees.json') or {}
        cached = red_trees.get(source_id)
        if cached and cached.get('compiler_red'):
            result = dict(cached['result'], time=ld.now(), commit=commit, seconds=0,
                          included=sorted(r['id'] for r in included),
                          suspects=suspects(cached['result'].get('failing', []), included))
            # 2026-10-25: the clean landings of this snapshot (same sources as the cached red, which ran to the end):
            # none of their modules fails or imports a failing module; tools/batch_land.py land_rest lands them
            result['clean'] = []
            if isinstance(cached['result'].get('clean'), list) and result.get('failing'):
                try:
                    graph = clone_imports()
                    blocked = set(result['failing']) | li.downstream(set(result['failing']), graph)
                    result['clean'] = sorted(r['id'] for r in included if not ({f['module'] for f in r['files']} & blocked))
                    save_graph(commit, graph)
                except Exception as e:   # noqa: BLE001
                    result['clean'] = []
                    print('clean landings not computed:', repr(e)[:300], flush=True)
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
            # 2026-10-26 (the human): the global build runs with transparent huge pages off as the single-file compiles do
            # (tools/thp-off, PR_SET_THP_DISABLE, inherited by lake's lean processes)
            thp = [str(pathlib.Path(__file__).resolve().parent / "thp-off")] if os.access(pathlib.Path(__file__).resolve().parent / "thp-off", os.X_OK) else []
            # 2026-10-26 (the human): target libraries blocked by a quarantine (tools/red_rework.py) are left out until
            # every module they need is back in the library; then the file is removed and everything builds again
            # target libraries: blocked_targets(), computed on the build copy before the red-tree cache lookup
            proc = subprocess.Popen(thp + ["nice", "-n", "0", "lake", "build"] + targets, cwd=CLONE, stdout=log, stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_NUM_THREADS=THREADS), start_new_session=True)
            restart = False
            failed_at, seen = None, 0
            # 2026-10-27 (the human): a module that fails while Lake still runs is dispatched at once (early_poll)
            early = {"pos": 0, "wait": [], "sent": set(), "procs": [], "commit": commit,
                     "bt": (ld.read_json(ld.B / "current.json") or {}).get("time"),
                     "on": CFG.get("SHEAF_EARLY_RED", "1") == "1" and only is None}
            while proc.poll() is None:
                time.sleep(POLL)
                if early["on"]:
                    try:
                        early_poll(early)
                    except Exception as e:  # noqa: BLE001  (never let the early dispatch touch the build)
                        print(f"{ld.now()} early red dispatch: {e!r}"[:300], flush=True)
                # 2026-10-24 (the human: report a failure at once, not with the last module of a 1-2 h build): the
                # first failing module stops the build after FAILFAST_GRACE seconds (failures of the same moment come
                # with it); the red is handled at once (tools/batch_land.py mechanical_red) and the next build goes on
                # from everything compiled so far (Lake keeps it), so a red costs little more than one build in all.
                if FAILFAST:
                    try:
                        with open(LOG, errors="ignore") as fh:
                            fh.seek(seen); chunk = fh.read(); seen = fh.tell()
                    except OSError:
                        chunk = ""
                    if failed_at is None and re.search(r"^\u2716 \[", chunk, re.M):
                        failed_at = time.time()
                        print(f"{ld.now()} a module failed: the build stops in {FAILFAST_GRACE} s", flush=True)
                    if failed_at is not None and time.time() - failed_at >= FAILFAST_GRACE:
                        os.killpg(proc.pid, signal.SIGTERM)
                        try:
                            proc.wait(timeout=30)
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL); proc.wait()
                        print(f"{ld.now()} build stopped after the first failure(s) (fail-fast)", flush=True)
                        break
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


ERRDIR = li.ROOT / "coord" / "build-errors"


def early_poll(st: dict) -> None:
    """2026-10-27 (the human: a module failing in the running build goes to the queue at once, not when a 40-minute
    build ends): reads the new complete lines of the log; a module whose `✖ [n/N] ... M` line appeared in the previous
    poll (its job's messages are printed by then) goes to tools/early_red.py dispatch, a detached process at nice 10
    (build-errors file, the writer's return or a rework item in the queue; it never touches lean/). Each module once."""
    for p in list(st["procs"]):
        if p.poll() is not None:
            st["procs"].remove(p)
    try:
        with open(LOG, "rb") as fh:
            fh.seek(st["pos"]); data = fh.read()
    except OSError:
        return
    found = []
    k = data.rfind(b"\n")
    if k >= 0:
        st["pos"] += k + 1
        found = [m for m in re.findall(r"^\u2716 \[\d+/\d+\] \w+ (\S+)", data[:k + 1].decode(errors="ignore"), re.M)
                 if m not in st["sent"]]
    send = [m for m in dict.fromkeys(st["wait"]) if m not in st["sent"]]
    st["wait"] = found
    if not send or not st.get("bt"):
        return
    st["sent"].update(send)
    with open(ld.B / "early-red.log", "a") as out:
        st["procs"].append(subprocess.Popen(
            ["nice", "-n", "10", sys.executable, str(TOOLS / "early_red.py"), "dispatch", "--build-time", st["bt"],
             "--commit", str(st["commit"] or "-"), *send], cwd=li.ROOT, stdout=out, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True))
    print(f"{ld.now()} failing while the build runs, dispatched now (tools/early_red.py): {' '.join(send[:8])}", flush=True)


def save_errors(text: str, failing: list[str], commit) -> None:
    """2026-10-23 (the human): whoever repairs a failing module gets the compiler's full message, not only its name.
    Lake prints each module's job as one block (`✖ [i/N] Building M` and its output up to the next job line): it is
    kept in coord/build-errors/<module>.txt (the newest failure of that module; trace lines dropped)."""
    want = set(failing)
    blocks, cur = {}, None
    for line in text.split("\n"):
        m = re.match(r"^[✖✔⚠] \[\d+/\d+\] \S+ (\S+)", line)
        if m:
            cur = m.group(1) if line.startswith("✖") and m.group(1) in want else None
            if cur is not None:
                blocks.setdefault(cur, [])
            continue
        if cur is not None and not line.startswith("trace:"):
            blocks[cur].append(line)
    ERRDIR.mkdir(parents=True, exist_ok=True)
    for mod, lines in blocks.items():
        body = "\n".join(lines).strip()
        if len(body) > 20000:
            body = body[:20000] + "\n… (cut)"
        (ERRDIR / f"{mod}.txt").write_text(f"# global build {ld.now()} of {str(commit)[:10]}: {mod} failed\n{body}\n")


def corrupt_artifacts(text: str) -> list[str]:
    """The compiled files of the build copy that Lean could not read (`failed to read file '….olean'`): each is deleted
    with the other files of its module (.ilean, .trace, .hash, …) so that Lake rebuilds it. Only files under
    local/buildtree/.lake/build; a package's file (shared, never rebuilt from the copy) is only reported."""
    out = []
    root = (CLONE / ".lake" / "build").resolve()
    for p in sorted(set(re.findall(r"failed to read file '([^']+\.olean)'", text))):
        f = pathlib.Path(p).resolve()
        if root not in f.parents:
            print(f"note: unreadable compiled file outside the build copy, not deleted: {p}", flush=True)
            continue
        stem = f.name[:-len(".olean")]
        for g in f.parent.glob(stem + ".*"):
            if g.is_file() and g.name.split(".")[0] == stem.split(".")[0]:
                g.unlink(missing_ok=True)
        out.append(str(f))
        print(f"deleted the unreadable compiled file {f} and its module's other files", flush=True)
    return out


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
        gen_done()
        clear_alert()
        print(f"GREEN in {result['seconds']} s; {len(ids)} landing(s) verified; compiled files published.")
        return 0
    if not built and corrupt_artifacts(text):
        # 2026-10-25: a compiled file Lean cannot read (left truncated by a full disk or a killed write) says nothing
        # about the sources: it is deleted from the build copy and rebuilt; nothing recorded
        print("INFRASTRUCTURE failure (unreadable compiled files deleted, they are rebuilt); nothing recorded.", flush=True)
        return 1
    if not built and re.search(r"no space left on device|resource exhausted|Cannot allocate memory|out of memory", text):
        # an infrastructure failure says nothing about the sources: not cached, not attributed, rebuilt by the loop
        print("INFRASTRUCTURE failure (disk or memory); nothing recorded, the same sources will be rebuilt.", flush=True)
        time.sleep(120)
        return 1
    failing = sorted(set(failing_modules(text)) | {c["module"] for c in checks})
    graph, clean = clone_imports(), []
    # 2026-10-27 (retry 1 of the red build 15:04:17Z): a module whose source is not in the build copy ("no such file or
    # directory" for local/buildtree/...) did not fail: something in the candidate imports a module the copy does not
    # have. That module, and the modules whose only failure is a project import missing from the copy ("bad import"), are
    # an infrastructure fault of the candidate, not failures of their own: they are not attributed and nothing is taken
    # out for them (no importer move to quarantine/); they still block their landings from land_rest.
    missing = {m for m in failing if m.startswith(PROJECT_PREFIXES) and not _clone_file(m)}
    infra = set(missing)
    if missing:
        for m in failing:
            if m in infra or not _clone_file(m):
                continue
            imps = graph.get(m) or set()
            if {i for i in imps if i.startswith(PROJECT_PREFIXES) and not _clone_file(i)} and not _own_error(text, m):
                infra.add(m)
    if infra:
        real = [m for m in failing if m not in infra]
        print(f"INFRASTRUCTURE: {len(missing)} module(s) not in the build copy and {len(infra) - len(missing)} importer(s) "
              f"failing only on them; not attributed, nothing taken out for them: {' '.join(sorted(infra)[:8])}", flush=True)
        result["infra_missing"] = sorted(infra)
        if not real:
            red_trees.pop(source_id, None)
            ld.write_json(ld.B / 'red-trees.json', red_trees)
            print("INFRASTRUCTURE failure (the candidate imports modules it does not contain); nothing recorded, the next "
                  "snapshot leaves the importers of quarantined modules out (quarantine_waiters).", flush=True)
            return 1
        failing = real
    try:
        # the infrastructure modules did not compile: their landings do not land from this build (land_rest)
        clean, checks, failing = clean_landings(included, sorted(set(failing) | infra), text, checks, graph)
        failing = sorted(set(failing) - infra)
        if checks:
            errors = errors + ["error: " + c["message"] for c in checks if "error: " + c["message"] not in errors]
        save_graph(commit, graph)
    except Exception as e:   # noqa: BLE001
        clean = []
        print("clean landings not computed:", repr(e)[:300], flush=True)
    try:
        save_errors(text, failing, commit)
    except Exception as e:   # noqa: BLE001  (never let the error copy stop the result)
        print("save_errors failed:", repr(e)[:200], flush=True)
    sus = suspects(failing, included, graph)
    result.update(result="red", source_fingerprint=source_id, failing=failing, errors=errors[:30], suspects=sus, included=sorted(ids), batch_checks=checks,
                  clean=clean)
    ld.write_json(ld.B / "last.json", result)
    red_trees[source_id] = {'compiler_red': compiler_red, 'result': result}
    ld.write_json(ld.B / 'red-trees.json', red_trees)
    if not sus or any(c['kind'] == 'probe' and not c.get('landing') for c in checks):
        alert((included[0].get('batch') if included else None), ' '.join(failing), 'unattributed red/probe failure', 'maintainer diagnosis or batch withdrawal')
    print(f"RED in {result['seconds']} s; nothing published. Failing: {' '.join(failing[:12]) or '-'}; "
          f"{len(clean)} of {len(ids)} landing(s) compiled cleanly and land once the failures are taken out (tools/batch_land.py land_rest)")
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
