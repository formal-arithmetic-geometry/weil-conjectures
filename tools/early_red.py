#!/usr/bin/env python3
"""Early red dispatch (the human, 2026-10-27 01:20 JST): a module that fails while the global build is still running is
handed out at once, not when the build ends (a big build takes ~40 min; 2026-10-26 15:40Z: SpP1RationalPointChern failed
at [40546/42159] and nothing was dispatched until the build closed).

tools/build.py watches its log while Lake runs and starts `early_red.py dispatch M...` (detached, nice 10) for each
newly failing module, ~one poll after its `✖ [n/N] Building M` line. For each module, without touching lean/:
  1. coord/build-errors/<M>.txt gets the compiler's messages so far (the end of the build rewrites it, save_errors).
  2. A delivery of the build that wrote M (a landing record with `delivery`, the records tools/batch_land.py round_red
     and mechanical_red return at the end) goes back to its writer now (merge_delivery.cmd_return), with the message
     that its landing is taken out when the build ends. Recorded in local/builds/early-red.json (`returns`); the end
     of the build does not return it again (batch_land.give_back and _undo_entries ask returned_early).
  3. Otherwise M becomes a rework item now (queue kind `rework`, the dispatcher's first lane; cause = the error): a row
     in local/builds/early-red.json (`rows`) that tools/queue.py lists while that build runs and until the lander has
     handled its result (red-handled.json). Nothing is moved: the quarantine at the end of the build
     (tools/red_rework.py) writes the module's coord/rework.tsv row, and from then on the queue lists that row under the
     same item name (no second item; the claim stays). A module whose restore from quarantine landed in the build (its
     rework.tsv row is "landed") is listed the same way; the take-out at the end puts it back in quarantine and its row
     is the item again. Not listed: a module the compiler only asks to `public import` something (the end adds the
     import), a module failing only on a `bad import` of a module that is in the library again, a maintainer/other
     landing's module that the end of the build takes out without a delivery (it goes back to its previous version).
     coord/queue.tsv and the tag files get the row at once; tools/queue.py write recomputes it at its next refresh.
  A fix of an early item that lands before the build ends is not quarantined by that build's end (fixed_since).

  tools/early_red.py dispatch --build-time T --commit C M...   (tools/build.py)
  tools/early_red.py dry-run [LOG] [LAST]   what an earlier build's log would have dispatched, and when (estimated from
                                            the job times Lake printed); writes nothing
  tools/early_red.py status                 the early rows listed now and the early returns of the last 2 days
"""
from __future__ import annotations
import fcntl, json, os, pathlib, re, subprocess, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
import landing as ld  # noqa: E402

ROOT = li.ROOT
STATE = ld.B / "early-red.json"
LOCK = ld.B / ".early-red.lock"
ERRDIR = ROOT / "coord" / "build-errors"
JOB = re.compile(r"^[✔⚠✖ℹ] \[(\d+)/(\d+)\] \w+ (\S+)(?: \(([^)]*)\))?", re.M)
KEEP_DAYS = 2


def _read() -> dict:
    d = ld.read_json(STATE) or {}
    d.setdefault("rows", {}); d.setdefault("returns", []); d.setdefault("seen", {})
    return d


def _write(d: dict) -> None:
    cut = time.strftime("%FT%TZ", time.gmtime(time.time() - KEEP_DAYS * 86400))
    d["rows"] = {m: r for m, r in d["rows"].items() if r.get("at", "") >= cut}
    d["returns"] = [r for r in d["returns"] if r.get("at", "") >= cut]
    d["seen"] = {k: v for k, v in d["seen"].items() if k >= cut}
    tmp = STATE.with_name(STATE.name + f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(d, indent=1, ensure_ascii=False))
    os.replace(tmp, STATE)


class _locked:
    def __enter__(self):
        self.fh = open(LOCK, "a"); fcntl.flock(self.fh, fcntl.LOCK_EX); return self

    def __exit__(self, *a):
        fcntl.flock(self.fh, fcntl.LOCK_UN); self.fh.close()


# ---------------------------------------------------------------- read by the end of the build and by the queue

def returned_early(group: str, item: str, head: str | None) -> bool:
    """True when this delivery (group, item, head) was already returned to its writer by an early dispatch."""
    try:
        h = str(head or "")
        for r in _read()["returns"]:
            rh = str(r.get("head") or "")
            if r.get("group") == group and r.get("item") == item and h and rh and (rh.startswith(h) or h.startswith(rh)):
                return True
    except Exception:  # noqa: BLE001
        pass
    return False


def _pending(row: dict, cur: dict | None, last: dict | None, handled: dict | None) -> bool:
    """the row's build is running, or it ended red and the lander has not handled that result yet"""
    bt = row.get("build_time")
    if cur and cur.get("time") == bt and not cur.get("finished"):
        return True
    return bool(last and last.get("result") == "red" and last.get("commit") == row.get("commit")
                and str(last.get("time", "")) >= str(bt) and (handled or {}).get("time") != last.get("time"))


def listed(rw_rows: dict | None = None) -> list[tuple[str, str]]:
    """[(module, note)]: the early rework items to list now (tools/queue.py). A module whose coord/rework.tsv row is open
    (in quarantine) is the quarantine's own item and is not listed here."""
    d = _read()
    if not d["rows"] or (ROOT / "local" / "UPSYNC_RUNNING").exists():
        return []
    cur, last, handled = ld.read_json(ld.B / "current.json"), ld.read_json(ld.B / "last.json"), ld.read_json(ld.B / "red-handled.json")
    if rw_rows is None:
        import rework
        rw_rows = rework.load()
    out = []
    for m, r in sorted(d["rows"].items(), key=lambda x: x[1].get("at", "")):
        if not _pending(r, cur, last, handled) or not li.file_of(m).is_file():
            continue
        if m in rw_rows and not (ROOT / ("lean/" + m.replace(".", "/") + ".lean")).is_file():
            continue
        out.append((m, r.get("note") or "failing in the running global build"))
    return out


def fixed_since(m: str) -> bool:
    """an early item whose fix landed after the snapshot of the build that found it (the file differs from that
    build's commit): red_rework.quarantine leaves it in the library, the next build verifies the fix"""
    try:
        r = _read()["rows"].get(m)
        last = ld.read_json(ld.B / "last.json") or {}
        if not r or not r.get("commit") or last.get("commit") != r["commit"]:
            return False
        rel = "lean/" + m.replace(".", "/") + ".lean"
        old = subprocess.run(["git", "show", f"{r['commit']}:{rel}"], cwd=ROOT, capture_output=True)
        f = ROOT / rel
        return old.returncode == 0 and f.is_file() and f.read_bytes() != old.stdout
    except Exception:  # noqa: BLE001
        return False


# ---------------------------------------------------------------- the log

def blocks(text: str) -> dict[str, str]:
    """module -> what Lake printed for its failed job so far (trace lines dropped)"""
    out, hs = {}, list(JOB.finditer(text))
    for k, h in enumerate(hs):
        if not h.group(0).startswith("✖"):
            continue
        end = hs[k + 1].start() if k + 1 < len(hs) else len(text)
        blk = text[h.end():end]
        cut = blk.find("\nSome required")
        blk = blk if cut < 0 else blk[:cut]
        out[h.group(3)] = "\n".join(l for l in blk.split("\n") if not l.startswith("trace:")).strip()
    return out


def first_error(block: str, n: int = 6) -> str:
    errs = [l.strip() for l in block.splitlines() if l.strip().startswith("error")]
    return " | ".join(re.sub(r"\s+", " ", l)[:300] for l in errs[:n])[:1500] or "error: failed in the global build"


# ---------------------------------------------------------------- classification (the end-of-build rules, read early)

def _records(ids) -> dict[str, list[dict]]:
    """module -> the landing records of the build (open or closed) that wrote it"""
    out: dict[str, list[dict]] = {}
    for i in ids:
        r = ld.read_json(ld.REQUESTS / f"{i}.json") or ld.read_json(ld.DONE / f"{i}.json")
        for f in (r or {}).get("files") or []:
            if f.get("module"):
                out.setdefault(f["module"], []).append(r)
    return out


def classify(m: str, block: str, writers: list[dict], rw_rows: dict, open_ids: set, exists=None) -> tuple[str, list[dict]]:
    """(action, deliveries to return): `return` (a delivery of the build wrote m), `rework` (an item now), or a reason
    for doing nothing early ('public import', 'bad import back', 'taken out with its landing', 'not a library module')"""
    import rework
    exists = exists or (lambda x: li.file_of(x).is_file())
    if m in rework.ROOTS_KEPT or m in rework.IMPORT_ROOTS or not exists(m):
        return "not a library module (the end of the build decides)", []
    dels = {}
    for r in writers:
        d = r.get("delivery")
        if isinstance(d, dict) and d.get("group") and d.get("item"):
            dels[(d["group"], d["item"], str(d.get("head") or ""))] = dict(d, landing=r["id"], commit=r.get("commit") or "")
    if dels:
        return "return", list(dels.values())
    if m in rw_rows:     # a restore from quarantine landed in this build: the take-out puts it back, its row is the item
        return "rework", []
    # another writer's open landing that the end takes out (drop_other_writers: not L, not the sync, not a rework move)
    if any(r["id"] in open_ids and r.get("group") != "L" and not r.get("upsync")
           and not str(r.get("note") or "").startswith("red build rework") for r in writers):
        return "taken out with its landing (no delivery to return)", []
    if re.search(r"consider adding `public import [\w.']+`", block):
        return "public import (the end of the build adds it)", []
    errs = [l for l in block.splitlines() if l.lstrip().startswith("error")]
    bad = [re.search(r"bad import '([^']+)'", l) for l in errs]
    if errs and all(bad) and all(exists(x.group(1)) for x in bad):
        return "bad import of a module back in the library (the next build decides)", []
    return "rework", []


# ---------------------------------------------------------------- dispatch

def _queue_insert(mods_notes: list[tuple[str, str]]) -> None:
    """the rows at once in coord/queue.tsv (stage 3, kind rework) and the tag files (`rework`), under the lock of
    tools/queue_mark.py; tools/queue.py write recomputes them at its next refresh"""
    import queue_mark as qm
    if not mods_notes:
        return
    with open(qm.LOCK, "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        if qm.Q.exists():
            lines = qm.Q.read_text().splitlines(True)
            have = {l.split("\t")[0] for l in lines if not l.startswith("#") and len(l.split("\t")) > 4 and l.split("\t")[4] == "rework"}
            new = [m for m, _ in mods_notes if m not in have]
            if new:
                ms = set(new)
                head = [l for l in lines if l.startswith("#")]
                body = [l for l in lines if not l.startswith("#") and l.split("\t")[0] not in ms]
                add = []
                for m, note in mods_notes:
                    if m in ms:
                        try:
                            n = li.sorry_count(li.file_of(m).read_text(errors="ignore"))
                        except OSError:
                            n = ""
                        add.append(f"{m}\t3\t-\t{n}\trework\t{note[:300]}\n")
                k = next((i for i, l in enumerate(body) if l.split("\t")[4:5] != ["retire-first"]), len(body))
                qm._replace(qm.Q, "".join(head + body[:k] + add + body[k:]))
        for t in qm.TAGS:
            if not t.exists():
                continue
            tl = t.read_text().splitlines(True)
            ms = {m for m, _ in mods_notes}
            if ms <= {l.rstrip("\n").split("\t", 1)[0] for l in tl if l.rstrip("\n").endswith("\trework")}:
                continue
            head = [l for l in tl if l.startswith("#")]
            body = [l for l in tl if not l.startswith("#") and l.split("\t", 1)[0].strip() not in ms]
            qm._replace(t, "".join(head + [f"{m}\trework\n" for m in sorted(ms)] + body))
    try:
        p = ROOT / "local" / "stage2" / "queue-requested"
        p.parent.mkdir(parents=True, exist_ok=True); p.touch()
    except OSError:
        pass


def _still_running(build_time: str) -> bool:
    cur = ld.read_json(ld.B / "current.json") or {}
    return cur.get("time") == build_time and not cur.get("finished")


def dispatch(build_time: str, commit: str, mods: list[str], dry: bool = False, text: str | None = None,
             cur: dict | None = None, log=print) -> list[dict]:
    import rework
    if text is None:
        text = (ld.B / "build.log").read_text(errors="ignore")
    cur = cur if cur is not None else (ld.read_json(ld.B / "current.json") or {})
    if not dry and cur.get("time") != build_time:
        log(f"build {build_time} is no longer the current build; nothing early"); return []
    upsync = (ROOT / "local" / "UPSYNC_RUNNING").exists()
    bl = blocks(text)
    writers = _records(cur.get("included") or [])
    open_ids = {r["id"] for r in ld.records(ld.REQUESTS)}
    rw_rows = rework.load()
    exists = None
    if dry and commit:   # the library as the build saw it
        names = subprocess.run(["git", "ls-tree", "-r", "--name-only", commit, "--", "lean"], cwd=ROOT,
                               capture_output=True, text=True).stdout.split()
        have = {n[len("lean/"):-len(".lean")].replace("/", ".") for n in names if n.endswith(".lean")}
        exists = have.__contains__
        open_ids = set(cur.get("included") or [])   # every landing of the build was open while it ran
    out, rows, rets = [], [], []
    with _locked():
        st = _read()
        seen = st["seen"].setdefault(build_time, [])
        for m in mods:
            if m in seen and not dry:
                continue
            blk = bl.get(m, "")
            act, dels = classify(m, blk, writers.get(m, []), rw_rows, open_ids, exists)
            if upsync and act != "return":
                act = "upstream sync running (its own quarantine rounds decide)"
            out.append({"module": m, "action": act, "returns": [f"{d['group']}/{d['item']}" for d in dels],
                        "error": first_error(blk)})
            if dry:
                continue
            seen.append(m)
            try:     # the compiler's messages so far (the end of the build rewrites the file, tools/build.py save_errors)
                ERRDIR.mkdir(parents=True, exist_ok=True)
                body = blk if len(blk) <= 20000 else blk[:20000] + "\n… (cut)"
                (ERRDIR / f"{m}.txt").write_text(f"# global build {ld.now()} of {str(commit)[:10]} (still running): {m} failed\n{body}\n")
            except OSError as e:
                log(f"{m}: build-errors file not written: {e!r}")
            if act == "return":
                for d in dels:
                    if not returned_early(d["group"], d["item"], d.get("head")):
                        rets.append((m, d))
            elif act == "rework":
                note = (f"failing in the running global build of {str(commit)[:10]} ({ld.now()}); fix it in lean/ "
                        f"(it is quarantined when the build ends unless fixed): {first_error(blk, 2)[:200]} "
                        f"(coord/build-errors/{m}.txt)")
                st["rows"][m] = {"build_time": build_time, "commit": commit, "at": ld.now(), "note": note,
                                 "cause": first_error(blk)}
                rows.append((m, note))
        if not dry:
            for m, d in rets:   # recorded before the return, so a concurrent end of the build does not return it again
                st["returns"].append({"group": d["group"], "item": d["item"], "head": d.get("head") or "",
                                      "landing": d["landing"], "module": m, "build_time": build_time, "at": ld.now()})
            _write(st)
    if dry:
        return out
    if rows:
        try:
            _queue_insert(rows)
        except Exception as e:  # noqa: BLE001
            log(f"queue insert failed ({e!r}); tools/queue.py write lists the rows at its next refresh")
    failed = []
    if rets:
        os.environ.setdefault("SHEAF_LEAD", "L-only")
        import merge_delivery as md
        for m, d in rets:
            if not _still_running(build_time):
                failed.append((m, d)); log(f"{d['group']}/{d['item']}: the build ended first; the end of the build returns it")
                continue
            why = (f"(the global build of {str(commit)[:10]}, still running) your landing {d['landing']} fails to compile in "
                   f"{m}: {first_error(bl.get(m, ''), 3)} -- the compiler's full messages: coord/build-errors/{m}.txt. "
                   "When this build ends your landing is taken out of the library (its files go back to the version "
                   "before it)" + (f"; your landed change: `git show {d['commit'][:10]} -- lean`" if d.get("commit") else "")
                   + ". Fix the module and deliver again.")
            try:
                md.cmd_return(d["group"], d["item"], why)
                log(f"RETURNED EARLY {d['group']}/{d['item']} (landing {d['landing']}): {m} failed in the running build")
                subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "rework", "-", d["item"],
                                "--note", "failed in the running global build (tools/early_red.py)"], cwd=ROOT,
                               capture_output=True, timeout=60)
            except Exception as e:  # noqa: BLE001
                failed.append((m, d)); log(f"early return of {d['group']}/{d['item']} failed ({e!r}); the end of the build returns it"[:400])
        if failed:
            with _locked():
                st = _read()
                bad = {(d["group"], d["item"], d.get("head") or "") for _, d in failed}
                st["returns"] = [r for r in st["returns"] if (r["group"], r["item"], r.get("head") or "") not in bad
                                 or r.get("build_time") != build_time]
                _write(st)
    for o in out:
        log(f"EARLY {o['module']}: {o['action']}" + (f" -> {', '.join(o['returns'])}" if o["returns"] else "")
            + f" | {o['error'][:200]}")
    return out


# ---------------------------------------------------------------- dry run over an earlier build

def dry_run(logf: pathlib.Path, lastf: pathlib.Path) -> int:
    text = logf.read_text(errors="ignore")
    last = ld.read_json(lastf) or {}
    secs = float(last.get("seconds") or 0)
    import calendar
    end = calendar.timegm(time.strptime(last["time"], "%Y-%m-%dT%H:%M:%SZ")) if last.get("time") else 0
    start = end - secs

    def dur(s):
        s = (s or "").strip()
        m = re.fullmatch(r"([\d.]+)(ms|s|m|h)", s)
        return float(m.group(1)) * {"ms": .001, "s": 1, "m": 60, "h": 3600}[m.group(2)] if m else 0.0
    jobs = list(JOB.finditer(text))
    tot = sum(dur(j.group(4)) for j in jobs) or 1.0
    cum, fails = 0.0, []
    for j in jobs:
        cum += dur(j.group(4))
        if j.group(0).startswith("✖"):
            fails.append((j.group(3), j.group(1), j.group(2), cum / tot))
    cur = {"time": "dry", "included": last.get("included") or [], "commit": last.get("commit")}
    res = {o["module"]: o for o in dispatch("dry", last.get("commit") or "", [f[0] for f in fails], dry=True, text=text, cur=cur,
                                            log=lambda *a: None)}
    print(f"build {last.get('time')} ({secs:.0f} s, {len(cur['included'])} landing(s)); its end-of-build dispatch came after "
          f"{last.get('time')} (+ the lander's handling)")
    for m, n, N, frac in fails:
        t = start + frac * secs
        o = res[m]
        print(f"[{n}/{N}] {m}\n    seen ~{time.strftime('%H:%M:%SZ', time.gmtime(t))} (est., {(end - t) / 60:.0f} min before the "
              f"build ended) -> {o['action']}" + (f": return to {', '.join(o['returns'])}" if o["returns"] else "")
              + f"\n    {o['error'][:240]}")
    return 0


def main(a: list[str]) -> int:
    if a[:1] == ["dispatch"]:
        bt = a[a.index("--build-time") + 1]; c = a[a.index("--commit") + 1]
        mods = [x for x in a[1:] if not x.startswith("--") and x not in (bt, c)]
        dispatch(bt, c, mods, log=lambda s: print(time.strftime("%FT%TZ", time.gmtime()), s, flush=True))
        return 0
    if a[:1] == ["dry-run"]:
        return dry_run(pathlib.Path(a[1]) if len(a) > 1 else ld.LOCAL / "build.log",
                       pathlib.Path(a[2]) if len(a) > 2 else ld.B / "last.json")
    if a[:1] == ["status"]:
        print(json.dumps({"listed": listed(), "returns": _read()["returns"][-20:]}, indent=1, ensure_ascii=False))
        return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
