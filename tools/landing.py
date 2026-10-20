#!/usr/bin/env python3
"""Landings, and how they reach the global build. Used by land.sh, land_set.sh and build.py.

Every landing is a record that moves through local/builds/, the way a claim is a file in coord/claims/:

  inflight/<id>.json   the files are written, the group is still checking them (single-file compiles, text checks);
                       a build started now takes the previous version of these files
  requests/<id>.json   the landing is complete and waits for a global build to verify it
  done/<id>.json       verified by a green build, or reverted by the maintainer, with the reason
  backup/<id>/…        the previous version of every file of the landing, kept until it is verified

A landing is of kind `interface` when it changes what other modules see: a statement, a definition, an instance or
an attribute, a removed import, a deleted module, or any set landed with land_set.sh. Otherwise it is of kind `proof`.
An interface landing makes the maintainer's build start over at once (build.py), so that it is verified first.

Usage:
  tools/landing.py status [<id>]            all open landings and the last build, or one landing
  tools/landing.py mine <group>             the group's landings that are open or were reverted
  tools/landing.py revert <id> <reason>     (the maintainer) put back the previous version of every file of a landing
                                            that a build showed to be wrong; refused if a file changed since
Called by the landing scripts, not by hand:
  tools/landing.py begin <group> <file>…    files relative to lean/; prints the id
  tools/landing.py finish <id> [--set]      the group's checks passed; prints the kind
  tools/landing.py abort <id>               the group's checks failed: restore the files
  tools/landing.py order <file>…            the files in the order of their imports of each other
Every step that reads or writes the tree holds local/tree.lock, as the build's snapshot does.
"""
from __future__ import annotations
import contextlib, fcntl, hashlib, json, os, pathlib, shutil, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

WORK = li.ROOT / "coord"
LOCAL = li.ROOT / "local"
B = LOCAL / "builds"
INFLIGHT, REQUESTS, DONE, BACKUP = B / "inflight", B / "requests", B / "done", B / "backup"
STAGED = B / "staged"             # merge queue: the content each open landing wrote, kept until it is verified/dropped
VERIFIED_REF = "refs/heads/sheaf-verified"   # merge queue: the last commit a green global build verified (main)


def dirs():
    for d in (INFLIGHT, REQUESTS, DONE, BACKUP, STAGED):
        d.mkdir(parents=True, exist_ok=True)


def merge_queue() -> bool:
    """The merge queue (the human, 2026-10-19; SHEAF_MERGE_QUEUE=1 in coord/sheaf.env). The verified main is the ref
    VERIFIED_REF: build.py advances it to a build commit only when that build is green. The working tree is the
    candidate: main plus the open landings (local/builds/requests, in id order), every one of them a record with the
    previous version (backup/) and its own version (staged/) of each file; build.py records any other change of a
    Lean file since main as a landing of the writer `U` before it snapshots. Taking a landing out of the candidate
    (drop_plan) is a hard restore of its files to their previous version, and every later open landing that changed
    one of those files goes with it: no merge, no conflict."""
    return li.config().get("SHEAF_MERGE_QUEUE") == "1"


@contextlib.contextmanager
def tree_lock():
    # A caller that already holds local/tree.lock on its own descriptor (~/cc1/proof-imports-cycle.sh runs
    # tools/add_proof_imports.py under it) sets SHEAF_TREE_LOCK_HELD=1: a second flock from this process would wait
    # for the parent forever (2026-10-20 20:30-21:10: merge lock held 40 min, every landing and build stalled).
    if os.environ.get("SHEAF_TREE_LOCK_HELD") == "1":
        yield
        return
    LOCAL.mkdir(exist_ok=True)
    with open(LOCAL / "tree.lock", "w") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def now() -> str:
    return time.strftime("%FT%TZ", time.gmtime())


def sha(p: pathlib.Path):
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None


def module(rel: str) -> str:
    return rel[:-5].replace("/", ".")


def write_json(p: pathlib.Path, d: dict):
    tmp = p.with_suffix(".tmp")
    tmp.write_text(json.dumps(d, ensure_ascii=False, indent=1))
    os.replace(tmp, p)


def read_json(p: pathlib.Path):
    try:
        return json.loads(p.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def records(d: pathlib.Path) -> list[dict]:
    return [r for r in (read_json(p) for p in sorted(d.glob("*.json"))) if r]


def log(line: str):
    WORK.mkdir(exist_ok=True)
    with open(WORK / "deliveries.log", "a") as f:
        f.write(now() + " " + line + "\n")


def drop_mirror(group: str, rels: list[str]):
    """Remove from the group's private mirror what it compiled from files that are no longer in the tree."""
    mirror = LOCAL / "build" / group
    shared = li.LEAN / ".lake" / "build" / "lib" / "lean"
    for rel in rels:
        for ext in (".olean", ".ilean", ".olean.server", ".olean.private", ".ir", ".ir.sig"):  # the parts of a `module`
            m = mirror / (rel[:-5] + ext)
            if m.exists() or m.is_symlink():
                m.unlink()
            s = shared / (rel[:-5] + ext)
            if s.exists() and m.parent.is_dir():
                m.symlink_to(s)


def restore(r: dict):
    for f in r["files"]:
        dst, bk = li.LEAN / f["path"], BACKUP / r["id"] / f["path"]
        if f["existed"]:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(bk, dst)
        elif dst.exists():
            dst.unlink()
    drop_mirror(r["group"], [f["path"] for f in r["files"]])
    shutil.rmtree(BACKUP / r["id"], ignore_errors=True)


def begin(group: str, rels: list[str]) -> int:
    dirs()
    rid = f"{time.strftime('%Y%m%dT%H%M%S', time.gmtime())}-{group}-{os.getpid()}"
    with tree_lock():
        busy = {f["path"]: r["id"] for r in records(INFLIGHT) for f in r["files"]}
        clash = [f"{rel} (landing {busy[rel]})" for rel in rels if rel in busy]
        if clash:
            print("Another landing of these files is still being checked: " + ", ".join(clash), file=sys.stderr)
            return 3
        files = []
        for rel in rels:
            src = li.LEAN / rel
            if src.is_file():
                (BACKUP / rid / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, BACKUP / rid / rel)
            files.append({"path": rel, "module": module(rel), "existed": src.is_file()})
        write_json(INFLIGHT / f"{rid}.json", {"id": rid, "group": group, "time": now(), "files": files})
    print(rid)
    return 0


def finish(rid: str, is_set: bool) -> int:
    with tree_lock():
        r = read_json(INFLIGHT / f"{rid}.json")
        if not r:
            print(f"no landing in flight with id {rid}", file=sys.stderr); return 2
        changed = []
        for f in r["files"]:
            dst, bk = li.LEAN / f["path"], BACKUP / rid / f["path"]
            f["sha"] = sha(dst)
            f["deleted"] = f["existed"] and not dst.is_file()
            if f["deleted"]:
                changed.append(f"{f['module']} (deleted)")
            elif f["existed"]:
                changed += li.interface_changes(bk.read_text(errors="ignore"), dst.read_text(errors="ignore"))
        r.update(kind="interface" if (is_set or changed) else "proof", set=is_set, changed=changed[:40], landed=now(),
                 seq=time.time_ns())
        stage_copy(r)
        write_json(REQUESTS / f"{rid}.json", r)
        (INFLIGHT / f"{rid}.json").unlink()
    log(f"{r['group']} landed {' '.join(f['module'] for f in r['files'])} ({r['kind']}, landing {rid})")
    print(r["kind"])
    return 0


def stage_copy(r: dict):
    """Keep the landing's own version of its files (merge queue): the expected content of a file after it."""
    for f in r["files"]:
        src = li.LEAN / f["path"]
        if src.is_file():
            dst = STAGED / r["id"] / f["path"]
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)


def new_record(group: str, files: dict, note: str, kind: str | None = None, extra: dict | None = None) -> dict:
    """A landing record for a change already written to the tree by a writer other than the landing scripts
    (proof-imports cycle, import pruning, maintenance, upstream sync, or `U` from build.py). files: {rel: previous
    bytes or None}. Caller holds local/tree.lock. Returns the record (in requests/)."""
    dirs()
    rid = f"{time.strftime('%Y%m%dT%H%M%S', time.gmtime())}-{group}-{os.getpid()}-{len(records(REQUESTS))}"
    out, changed = [], []
    for rel, before in sorted(files.items()):
        if before is not None:
            bk = BACKUP / rid / rel
            bk.parent.mkdir(parents=True, exist_ok=True)
            bk.write_bytes(before)
        dst = li.LEAN / rel
        f = {"path": rel, "module": module(rel), "existed": before is not None, "sha": sha(dst)}
        f["deleted"] = before is not None and not dst.is_file()
        if f["deleted"]:
            changed.append(f"{f['module']} (deleted)")
        elif before is not None:
            changed += li.interface_changes(before.decode(errors="ignore"), dst.read_text(errors="ignore"))
        else:
            changed.append(f"{f['module']} (new)")
        out.append(f)
    r = {"id": rid, "group": group, "time": now(), "files": out, "note": note[:500], "seq": time.time_ns(),
         "kind": kind or ("interface" if changed else "proof"), "set": len(out) > 1, "changed": changed[:40], "landed": now()}
    r.update(extra or {})
    stage_copy(r)
    write_json(REQUESTS / f"{rid}.json", r)
    log(f"{group} recorded {' '.join(f['module'] for f in out[:6])} ({r['kind']}, landing {rid}): {note[:120]}")
    return r


class Busy(RuntimeError):
    pass


def order_key(r: dict):
    """Landing order: the time a landing was completed (ns, `seq`), else the second in its id."""
    if r.get("seq"):
        return (r["seq"], r["id"])
    try:
        import calendar
        return (calendar.timegm(time.strptime(r["id"][:15], "%Y%m%dT%H%M%S")) * 10**9, r["id"])
    except ValueError:
        return (0, r["id"])


def drop_plan(ids, open_records=None) -> tuple[list[dict], dict, list[str]]:
    """Take landings out of the candidate (merge queue). Returns (dropped records in id order, {rel: bytes or None}
    to write, notes). A later open landing that changed a file of a dropped one is dropped with it (its version was
    made on top of the dropped change); each file goes back to the version before the earliest dropped landing that
    changed it. Reads only the open records; writes nothing. Busy when a landing still being checked touches a file."""
    recs = sorted(open_records if open_records is not None else records(REQUESTS), key=order_key)
    want, first, dropped, notes = set(ids), {}, [], []
    for r in recs:
        paths = [f["path"] for f in r["files"]]
        if r["id"] in want or any(p in first for p in paths):
            if r["id"] not in want:
                by = sorted({first[p]["id"] for p in paths if p in first})
                r = dict(r, chained=by)
                notes.append(f"{r['id']} ({r['group']}) goes with {', '.join(by)}: it changed the same file(s) after it")
            dropped.append(r)
            for f in r["files"]:
                first.setdefault(f["path"], r)
    busy = [x["id"] for x in records(INFLIGHT) if any(f["path"] in first for f in x["files"])]
    if busy:
        raise Busy("landings still being checked touch the files: " + ", ".join(busy))
    restore_to = {}
    for rel, r in first.items():
        f = next(f for f in r["files"] if f["path"] == rel)
        restore_to[rel] = (BACKUP / r["id"] / rel).read_bytes() if f["existed"] else None
        last = [x for x in dropped if any(g["path"] == rel for g in x["files"])][-1]
        cur = sha(li.LEAN / rel)
        exp = next(g.get("sha") for g in last["files"] if g["path"] == rel)
        if cur != exp:
            notes.append(f"{rel}: an unrecorded edit after {last['id']} is discarded with it")
    return dropped, restore_to, notes


def drop_close(dropped: list[dict], reason: str, reasons: dict | None = None):
    """Close the dropped records (merge queue): done/<id>.json with result reverted; their backups go."""
    for r in dropped:
        r = dict(r)
        why = (reasons or {}).get(r["id"]) or (reason if not r.get("chained") else
              f"{reason}; taken out with {', '.join(r['chained'])}: it changed the same file(s) after it")
        r.update(result="reverted", reason=why, closed=now())
        write_json(DONE / f"{r['id']}.json", r)
        (REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
        shutil.rmtree(BACKUP / r["id"], ignore_errors=True)
        shutil.rmtree(STAGED / r["id"], ignore_errors=True)
        drop_mirror(r["group"], [f["path"] for f in r["files"]])


def abort(rid: str) -> int:
    with tree_lock():
        r = read_json(INFLIGHT / f"{rid}.json")
        if not r:
            return 0
        restore(r)
        (INFLIGHT / f"{rid}.json").unlink()
    return 0


def revert(rid: str, reason: str) -> int:
    # Batch records include more than Lean files: route their take-out through
    # the full transaction, including the fallback withdrawal.
    rec = read_json(REQUESTS / f'{rid}.json')
    if rec and rec.get('batch'):
        import batch_land as bl
        b = bl.read_json(bl.OPEN)
        nx = bl.read_json(bl.NEXT)
        if b and nx and any(x['landing'] == rid for x in nx.get('entries', [])):
            b = bl.fold_next(b, lambda *x: print(*x))     # a pipelined batch's landing: one open batch first
        e = next((x for x in (b or {}).get('entries', []) if x['landing'] == rid), None)
        if e:
            try:
                bl.unland(e, reason, reason)
                e['state'] = 'returned'; bl.write_json(bl.OPEN, b)
            except bl.recovery.Conflict as exc:
                bl.withdraw(b, 'take-out conflict: ' + str(exc), lambda *x: print(*x))
            return 0
    dirs()
    if merge_queue():
        return revert_mq(rid, reason)
    with tree_lock():
        r = read_json(REQUESTS / f"{rid}.json")
        if not r:
            print(f"no landing waiting for a build with id {rid}", file=sys.stderr); return 2
        moved = [f["path"] for f in r["files"] if sha(li.LEAN / f["path"]) != f.get("sha")]
        if moved:
            print("Not reverted: these files changed after the landing, so putting back the old version would lose "
                  "that work: " + ", ".join(moved) + ". Repair them through a landing of your own.")
            return 3
        restore(r)
        r.update(result="reverted", reason=reason, closed=now())
        write_json(DONE / f"{rid}.json", r)
        (REQUESTS / f"{rid}.json").unlink()
    log(f"M reverted landing {rid} of {r['group']}: {reason}")
    print(f"Reverted landing {rid} ({len(r['files'])} file(s)) of {r['group']}.")
    return 0


def revert_mq(rid: str, reason: str) -> int:
    """Merge queue: hard restore of the landing's files and of every later landing of the same files; one commit."""
    import mergelock, subprocess
    with mergelock.merge_lock():
        with tree_lock():
            if not read_json(REQUESTS / f"{rid}.json"):
                print(f"no landing waiting for a build with id {rid}", file=sys.stderr); return 2
            dropped, restore_to, notes = drop_plan([rid])
            lean_rel = li.LEAN.resolve().relative_to(li.ROOT.resolve()).as_posix()
            for rel, data in restore_to.items():
                dst = li.LEAN / rel
                if data is None:
                    dst.unlink(missing_ok=True)
                else:
                    dst.parent.mkdir(parents=True, exist_ok=True); dst.write_bytes(data)
            paths = [f"{lean_rel}/{rel}" for rel in restore_to]
            subprocess.run(["git", "add", "-A", "--", *paths], cwd=li.ROOT, capture_output=True)
            subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
                            f"Take out landing {rid}: {reason[:200]}\n\n" + "\n".join(notes) +
                            "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *paths], cwd=li.ROOT, capture_output=True)
            drop_close(dropped, reason)
    for x in notes:
        print(x)
    log(f"M took out landing {rid} ({len(dropped)} landing(s), {len(restore_to)} file(s)): {reason}")
    print(f"Took out landing {rid}: {len(restore_to)} file(s) restored, {len(dropped) - 1} later landing(s) with it.")
    return 0


def order(rels: list[str]) -> int:
    mods = {module(r): r for r in rels}
    imps = {}
    for m, r in mods.items():
        p = li.LEAN / r
        imps[m] = li.imports_of(p.read_text(errors="ignore")) & mods.keys() if p.is_file() else set()
    out, seen = [], set()

    def visit(m, path=()):
        if m in seen:
            return
        if m in path:
            raise SystemExit(f"the set has an import cycle through {m}")
        for i in sorted(imps[m]):
            visit(i, path + (m,))
        seen.add(m); out.append(mods[m])
    for m in sorted(mods):
        visit(m)
    print("\n".join(r for r in out if (li.LEAN / r).is_file()))
    return 0


def line(r: dict, state: str) -> str:
    mods = " ".join(f["module"] for f in r["files"][:4]) + (" …" if len(r["files"]) > 4 else "")
    tail = f": {r['reason']}" if r.get("reason") else ""
    return f"{r['id']}  {state:9} {r.get('kind', '-'):9} {r['group']:6} {mods}{tail}"


def status(rid: str | None, group: str | None) -> int:
    dirs()
    rows = [(r, "checking") for r in records(INFLIGHT)] + [(r, "waiting") for r in records(REQUESTS)]
    rows += [(r, r.get("result", "verified")) for r in records(DONE)[-200:]]
    if rid:
        hit = [(r, s) for r, s in rows if r["id"] == rid]
        if not hit:
            print(f"no landing with id {rid}"); return 2
        r, s = hit[0]
        print(line(r, s))
        print(json.dumps({k: r[k] for k in r if k != "files"}, ensure_ascii=False, indent=1))
        return 0
    if group:
        rows = [(r, s) for r, s in rows if r["group"] == group and s != "verified"]
    else:
        rows = [(r, s) for r, s in rows if s in ("checking", "waiting")]
    for r, s in rows:
        print(line(r, s))
    last = read_json(B / "last.json")
    if last and not group:
        print(f"last build: {last['result']} at {last['time']}, commit {last.get('commit') or '-'}, "
              f"{len(last.get('verified', []))} landing(s) verified" +
              (f", failing: {' '.join(last['failing'][:6])}" if last.get("failing") else ""))
    return 0


def main() -> int:
    a = sys.argv[1:]
    if len(a) >= 3 and a[0] == "begin":
        return begin(a[1], a[2:])
    if len(a) in (2, 3) and a[0] == "finish":
        return finish(a[1], "--set" in a[2:])
    if len(a) == 2 and a[0] == "abort":
        return abort(a[1])
    if len(a) >= 3 and a[0] == "revert":
        return revert(a[1], " ".join(a[2:]))
    if len(a) >= 2 and a[0] == "order":
        return order(a[1:])
    if a and a[0] == "status" and len(a) <= 2:
        return status(a[1] if len(a) == 2 else None, None)
    if len(a) == 2 and a[0] == "mine":
        return status(None, a[1])
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
