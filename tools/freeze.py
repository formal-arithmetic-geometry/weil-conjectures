#!/usr/bin/env python3
"""The blocked freeze (the human, 2026-10-28 02:50 CST): when more than SHEAF_FREEZE_BLOCKED (default 100) modules are
blocked, normal landing stops and the blocking roots are fixed first; then landing resumes.

Blocked: tools/rework.py blocked_count(), the modules in quarantine/ that are missing from lean/ (rework rows not landed):
their work cannot be dispatched.

While frozen (local/batch/freeze.json):
  - tools/batch_land.py lands only rework fixes (deliveries whose item is a module of coord/rework.tsv) and the cluster
    restores; every other delivery, stage 2 and stage 3, stays on its branch, neither checked nor returned, and the
    lander logs "frozen: N blocked" in ~/cc1/autoland.log. Maintainer (L-only) landings are direct commits and are not
    affected. The build loop keeps building: every build verifies fixes and restores only.
  - ~/cc1/FREEZE holds one line (since, blocked count, the roots with claimant and age); ~/cc1/freeze.log records the
    changes. The lead session watches FREEZE and sends maintainer subagents to the roots.
Unfreeze: blocked <= the limit now, and a green build whose snapshot descends from the commit at which the count first
fell to the limit has at most the limit blocked in its own tree. FREEZE is then removed.

Usage: tools/freeze.py status | update
"""
from __future__ import annotations
import calendar, json, os, pathlib, subprocess, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import rework  # noqa: E402

ROOT = rework.ROOT
STATE = ROOT / "local" / "batch" / "freeze.json"
LAST = ROOT / "local" / "builds" / "last.json"
CLAIMS = ROOT / "coord" / "claims"
SIGNAL = pathlib.Path(os.environ.get("SHEAF_FREEZE_FILE") or pathlib.Path.home() / "cc1" / "FREEZE")
LOG = pathlib.Path(os.environ.get("SHEAF_FREEZE_LOG") or pathlib.Path.home() / "cc1" / "freeze.log")
SIGNAL_EVERY = 60          # seconds between rewrites of FREEZE while nothing but the ages changed


def limit() -> int:
    try:
        return int(os.environ.get("SHEAF_FREEZE_BLOCKED") or 100)
    except ValueError:
        return 100


def iso(t: float | None = None) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() if t is None else t))


def _read(p: pathlib.Path):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


def _write(p: pathlib.Path, text: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + f".tmp{os.getpid()}")
    tmp.write_text(text)
    os.replace(tmp, p)


def state() -> dict:
    return _read(STATE) or {"frozen": False}


def frozen() -> bool:
    return bool(state().get("frozen"))


def _flog(msg: str) -> None:
    LOG.parent.mkdir(parents=True, exist_ok=True)
    with open(LOG, "a") as fh:
        fh.write(time.strftime("%F %T ") + msg + "\n")


def allowed(c: dict, rows: dict) -> bool:
    """a delivery that may land while frozen: a rework fix (its item is a module of coord/rework.tsv) or a maintainer's"""
    return c.get("item") in rows or str(c.get("group") or "").startswith("L")


def split(cands: list[dict], rows: dict | None = None) -> tuple[list[dict], list[dict]]:
    rows = rework.load() if rows is None else rows
    keep = [c for c in cands if allowed(c, rows)]
    return keep, [c for c in cands if not allowed(c, rows)]


def _age(t: float | None, now: float) -> str:
    if not t:
        return "?"
    h = (now - t) / 3600
    return f"{h:.1f}h" if h >= 1 else f"{max(0, round(h * 60))}m"


def _epoch(s: str) -> float | None:
    try:
        return calendar.timegm(time.strptime(s, "%Y-%m-%dT%H:%M:%SZ"))
    except (ValueError, TypeError):
        return None


def roots(rows: dict | None = None, now: float | None = None) -> list[dict]:
    """the blocking roots (tools/rework.py clusters: quarantined, not landed, importing no other quarantined module),
    most blocked importers first, with their claimant and ages"""
    rows = rework.load() if rows is None else rows
    now = time.time() if now is None else now
    out = []
    try:
        back, seeds = rework.cluster_set(rows)     # what the cluster restore puts back, the confirmed unfixed roots
        back = set(back)
    except Exception:  # noqa: BLE001
        back, seeds = set(), set()
    for c in rework.clusters(rows):
        m = c["item"]
        cause = rows[m].get("cause") or ""
        err = cause.startswith("error:") or "does not compile alone" in cause
        cl = _read(CLAIMS / f"{m}.lock") or {}
        out.append({"module": m, "waiting": c["waiting"],
                    "kind": ("unfixed error" if m in seeds else "restorable" if m in back
                             else "error" if err else "import"),
                    "claimant": cl.get("who") or "unclaimed", "claim_age": _age(cl.get("t"), now) if cl else "-",
                    "age": _age(_epoch(rows[m].get("time") or ""), now)})
    return out


def signal_line(st: dict, n: int, rs: list[dict], unrowed: int) -> str:
    parts = [f"{r['module']} ({r['kind']} root, {r['waiting']} waiting, claim {r['claimant']} {r['claim_age']}, "
             f"quarantined {r['age']})" for r in rs]
    return (f"since {st.get('since')} | blocked {n} > {limit()} (tools/rework.py blocked_count; {unrowed} without a rework row;"
            " restorable: the cluster restore puts it back, unfixed error: its quarantined text failed)"
            f" | {len(rs)} root(s): " + ("; ".join(parts) or "none") + "\n")


def _is_ancestor(a: str, b: str) -> bool:
    return subprocess.run(["git", "merge-base", "--is-ancestor", a, b], cwd=ROOT, capture_output=True).returncode == 0


def _head() -> str:
    return rework.git("rev-parse", "HEAD").strip()


def update(log=None, now: float | None = None) -> dict:
    """one evaluation (every lander step): freeze, refresh the signal, or unfreeze; returns the state"""
    now = time.time() if now is None else now
    log = log or (lambda *a: None)
    T = limit()
    files = rework.blocked_files()
    n = len(files)
    st = state()
    st["limit"] = T
    if not st.get("frozen"):
        if n <= T:
            if st.get("blocked") != n:
                st["blocked"] = n; _write(STATE, json.dumps(st, indent=1))
            return st
        st = {"frozen": True, "since": iso(now), "blocked": n, "limit": T}
        _flog(f"FREEZE on: {n} blocked > {T}; only rework fixes and cluster restores land")
        log(f"frozen: {n} blocked > {T} (tools/freeze.py); only rework fixes, cluster restores and maintainer landings land")
    else:
        if n > T:
            st.pop("low_head", None)
        else:
            if not st.get("low_head"):
                st["low_head"], st["low_since"] = _head(), iso(now)
                _flog(f"blocked {n} <= {T} at {st['low_head'][:10]}; unfreeze after a green build of it")
            last = _read(LAST) or {}
            c = last.get("commit") or ""
            if last.get("result") == "green" and c and _is_ancestor(st["low_head"], c):
                nb = rework.blocked_count(c)
                if nb <= T:
                    _flog(f"FREEZE off: green build {last.get('time')} ({c[:10]}) has {nb} blocked; now {n}; "
                          f"frozen since {st.get('since')}")
                    log(f"unfrozen: green build {last.get('time')} has {nb} blocked <= {T}; ordinary deliveries land again")
                    st = {"frozen": False, "blocked": n, "limit": T, "last_freeze": [st.get("since"), iso(now)]}
                    SIGNAL.unlink(missing_ok=True)
                    _write(STATE, json.dumps(st, indent=1))
                    return st
        if st.get("blocked") != n:
            _flog(f"blocked {st.get('blocked')} -> {n}")
            st["blocked"] = n
    if now - float(st.get("signal_t") or 0) >= SIGNAL_EVERY or not SIGNAL.exists() or st.get("signal_n") != n:
        rows = rework.load()
        live = {rows[m].get("quarantine") or rework.qpath(m) for m in rows}
        _write(SIGNAL, signal_line(st, n, roots(rows, now), sum(1 for f in files if f not in live)))
        st["signal_t"], st["signal_n"] = now, n
    _write(STATE, json.dumps(st, indent=1))
    return st


def main() -> int:
    a = sys.argv[1:]
    cmd = a[0] if a else "status"
    if cmd == "update":
        st = update(lambda *x: print(*x))
    elif cmd == "status":
        st = state()
    else:
        print(__doc__); return 2
    print(json.dumps({k: v for k, v in st.items() if k not in ("signal_t",)}, indent=1))
    print("blocked now:", rework.blocked_count(), "limit:", limit())
    if SIGNAL.exists():
        print("FREEZE:", SIGNAL.read_text().strip()[:2000])
    return 0


if __name__ == "__main__":
    sys.exit(main())
