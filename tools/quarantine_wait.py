#!/usr/bin/env python3
"""A delivery whose only refusal is "missing import source modules" for modules that are quarantined right now (a red
build moved them to quarantine/, their rework row has not landed back) waits on its branch instead of going back to its
writer (2026-10-28: a red build at 08:56 CST quarantined 684 importers; ~27 finished deliveries were returned in one
hour although they were fine once the restore completed). It is checked again when every such import is back in lean/,
or after SHEAF_QWAIT_HOURS (default 6) since it first waited; then it is returned as before. An import that is neither
quarantined nor in coord/rework.tsv (never existed, deleted) still returns immediately.

State: local/batch/quarantine-waits.json {head: {group, item, since, deps}} (several check processes write it: flock).
Used by tools/batch_land.py (candidates: a waiting head is not checked again while its imports are still quarantined;
every refuse_missing call: wait() decides wait or return).
Usage: tools/quarantine_wait.py status
"""
from __future__ import annotations
import fcntl, json, os, pathlib, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import rework  # noqa: E402

ROOT = rework.ROOT
STATE = ROOT / "local" / "batch" / "quarantine-waits.json"


def cap() -> float:
    try:
        return float(os.environ.get("SHEAF_QWAIT_HOURS") or 6) * 3600
    except ValueError:
        return 6 * 3600.0


def quarantined_now(dep: str, rows: dict | None = None) -> bool:
    """still out of the library: a quarantined copy or a rework row, and no file at the original path"""
    if (ROOT / rework.opath(dep)).is_file():
        return False
    return (ROOT / rework.qpath(dep)).is_file() or dep in (rework.load() if rows is None else rows)


def waitable(dep: str, rows: dict) -> bool:
    """quarantined now, or just restored (in lean/ of the working tree while the checked library tip still lacks it)"""
    return (ROOT / rework.opath(dep)).is_file() or quarantined_now(dep, rows)


def _locked(fn):
    STATE.parent.mkdir(parents=True, exist_ok=True)
    with open(STATE.with_name(STATE.name + ".lock"), "a") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            data = json.loads(STATE.read_text())
        except (OSError, ValueError):
            data = {}
        out, changed = fn(data)
        if changed:
            tmp = STATE.with_name(STATE.name + f".tmp{os.getpid()}")
            tmp.write_text(json.dumps(data, indent=1, sort_keys=True))
            os.replace(tmp, STATE)
        return out


def load() -> dict:
    try:
        return json.loads(STATE.read_text())
    except (OSError, ValueError):
        return {}


def wait(exc, g: str, item: str, head: str, now: float | None = None) -> str | None:
    """exc: import_cycles.MissingImports. A wait message when every missing import is quarantined (or just restored)
    and the delivery has waited less than cap(); None: return it as before (the record is dropped)."""
    now = time.time() if now is None else now
    missing = getattr(exc, "missing", None)
    if not missing:
        return None
    rows = rework.load()
    deps = sorted({d for _, d in missing})
    ok = all(waitable(d, rows) for d in deps)

    def upd(data):
        r = data.get(head)
        if not ok:
            return None, data.pop(head, None) is not None
        if r is None:
            r = data[head] = {"group": g, "item": item, "since": now, "deps": deps}
        else:
            r["deps"] = sorted(set(r.get("deps") or []) | set(deps))
        if now - float(r.get("since") or now) >= cap():
            data.pop(head, None)
            return None, True
        h = (now - float(r["since"])) / 3600
        return f"waits: imports quarantined {', '.join(deps)} (since {h:.1f} h, at most {cap() / 3600:g} h)", True
    return _locked(upd)


def holding(head: str, waits: dict | None = None, rows: dict | None = None, now: float | None = None) -> bool:
    """the head waits and one of its imports is still quarantined (and the cap has not run out): do not check it
    again now. Read-only; a caller looping over candidates passes load() and rework.load() once."""
    r = (load() if waits is None else waits).get(head)
    if not r:
        return False
    now = time.time() if now is None else now
    if now - float(r.get("since") or now) >= cap():
        return False
    rows = rework.load() if rows is None else rows
    return any(quarantined_now(d, rows) for d in r.get("deps") or [])


def prune(live_heads: set[str]) -> None:
    """drop records of heads that are no longer candidates (branch moved, gone, landed)"""
    def upd(data):
        gone = [h for h in data if h not in live_heads]
        for h in gone:
            data.pop(h)
        return None, bool(gone)
    if STATE.exists():
        _locked(upd)


if __name__ == "__main__":
    now = time.time()
    rw = rework.load()
    for h, r in sorted(load().items(), key=lambda kv: kv[1].get("since", 0)):
        still = [d for d in r.get("deps") or [] if quarantined_now(d, rw)]
        print(f"{r.get('group')}\t{r.get('item')}\t{h[:9]}\t{(now - r.get('since', now)) / 3600:.1f}h\t"
              f"{len(still)}/{len(r.get('deps') or [])} still quarantined\t{', '.join(still)[:300]}")
