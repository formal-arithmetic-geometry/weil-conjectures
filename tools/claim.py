#!/usr/bin/env python3
"""Claims: which group is working on which module, so that no two agents work on the same one.

Usage:
  tools/claim.py next <group> [--count N] [--stage S]   claim up to N items from the head of coord/queue.tsv, of stage S only
                                               if given; prints one item per line (a module, or a DAG node in stages 1 and 2)
  tools/claim.py take <group> <module>         claim a given module (also before changing someone else's statement)
  tools/claim.py renew <group> <module>        keep a claim alive during long work
  tools/claim.py done <group> <module> <note>  delivered; if the module still has `sorry`, it goes back to the queue
  tools/claim.py release <group> <module> <reason>   give the item back, stuck or abandoned
  tools/claim.py mine <group> | list           the group's claims | all claims with their age
  tools/claim.py expire                        release every claim not renewed for SHEAF_CLAIM_TTL hours (the maintainer)
  tools/claim.py parked                        the items parked in stage 2 (abandoned by some group), their reasons, resolved or open

Stage-2 parking (launcher's order 2026-10-11 05:50 UTC): an item released with 'abandon:' after stage 2 opened
(2026-10-11T05:05Z) whose stage in coord/queue.tsv is 2 (or which the queue no longer lists) is parked for EVERY
group: `next` skips it and `take` refuses it until coord/stage2-parked.md has a line `- <item> | ...` carrying RESOLVED.

A claim is the file coord/claims/<module>.lock, created atomically, so two agents can never both obtain it.
A group holds at most SHEAF_CLAIMS_PER_GROUP claims (default 10). A claim not renewed for SHEAF_CLAIM_TTL hours
(default 6) may be taken over by anyone; the takeover is serialized so only one agent gets it.
Every `done` and `release` is recorded in coord/deliveries.log.
"""
from __future__ import annotations
import subprocess
import fcntl, json, os, pathlib, re, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

WORK = li.ROOT / "coord"
C = WORK / "claims"
CFG = li.config()
LIMIT = int(CFG.get("SHEAF_CLAIMS_PER_GROUP", "10"))
TTL = float(CFG.get("SHEAF_CLAIM_TTL", "6")) * 3600


RETURNS = WORK / "returns"


def _node_exists(m: str) -> bool:
    return any((li.ROOT / "dag" / "nodes").glob(f"*/{m}.json"))


def open_returns(group: str) -> list[str]:
    """Headings `## <item> (...)` of coord/returns/<group>.md whose <item> is a DAG node: the open entries
    (decision of the human, 2026-10-09 evening: returns are repaired before new work is claimed)."""
    p = RETURNS / f"{group}.md"
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        m = re.match(r"## (\S+) \(", line)
        if m and _node_exists(m.group(1)):
            out.append(line[3:].rstrip())
    return out


def drop_return_entries(group: str, item: str) -> int:
    """Delete every entry of coord/returns/<group>.md headed `## <item> (`; returns how many were dropped."""
    p = RETURNS / f"{group}.md"
    if not p.exists():
        return 0
    parts = re.split(r"(?m)^(?=## )", p.read_text())
    keep = [x for x in parts if not x.startswith(f"## {item} (")]
    n = len(parts) - len(keep)
    if n:
        p.write_text("".join(keep))
    return n


def lock(m): return C / (m.replace("/", "__") + ".lock")


def read(m):
    try:
        return json.loads(lock(m).read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def expired(r) -> bool:
    return r is not None and time.time() - r.get("t", 0) > TTL


def create(m, who):
    fd = os.open(lock(m), os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
    with os.fdopen(fd, "w") as f:
        f.write(json.dumps({"who": who, "t": time.time(), "since": time.strftime("%FT%TZ", time.gmtime())}))


def held_by(who):
    return [p.stem.replace("__", "/") for p in sorted(C.glob("*.lock")) if (read(p.stem.replace("__", "/")) or {}).get("who") == who and not expired(read(p.stem.replace("__", "/")))]


def log(line):
    with open(WORK / "deliveries.log", "a") as f:
        f.write(time.strftime("%FT%TZ", time.gmtime()) + " " + line + "\n")


def sorries(m):
    p = li.file_of(m)
    return li.sorry_count(p.read_text(errors="ignore")) if p.is_file() else None


def repair_note(m):
    try: return json.loads((WORK / 'repair-notes' / (m + '.json')).read_text())
    except (OSError, ValueError): return {}


def handoff_return(who, m):
    """Any next claimant receives the failed repair's full diagnostic handoff."""
    nr = repair_note(m)
    if nr.get('state') != 'released': return
    p = RETURNS / (who + '.md'); p.parent.mkdir(parents=True, exist_ok=True)
    drop_return_entries(who, m)
    with open(p, 'a') as f:
        f.write('\n\n## ' + m + ' (dedicated repair handoff)\n\n'
                + 'The previous worker ended with: ' + nr.get('note', '')
                + '\n\nCompiler messages and attribution:\n' + nr.get('reason', '') + '\n')

def take(who, m, quiet=False) -> bool:
    if stage2_parked(m):   # launcher's order 2026-10-11 05:50 UTC: parked for every group until L resolves it
        if not quiet:
            print(f"{m} is parked in stage 2 (abandoned; see tools/claim.py parked and coord/stage2-parked.md); nothing to claim")
        return False
    if node_finished(m) and repair_note(m).get('state') != 'released':   # launcher's order 2026-10-10 20:55 UTC: refuse a node already split, matched or attached
        if not quiet:
            print(f"{m} is already split, matched or attached; nothing to claim")
        return False
    if len(held_by(who)) >= LIMIT:
        if not quiet:
            print(f"{who} already holds {LIMIT} claims; deliver or release one first")
        return False
    try:
        create(m, who); handoff_return(who, m); print(m); return True
    except FileExistsError:
        pass
    with open(C / ".takeover", "w") as g:
        fcntl.flock(g, fcntl.LOCK_EX)
        r = read(m)
        if expired(r):
            lock(m).unlink(missing_ok=True)
            log(f"{who} took over the expired claim of {r.get('who')} on {m}")
            try:
                create(m, who); handoff_return(who, m); print(m); return True
            except FileExistsError:
                pass
    if not quiet:
        r = read(m) or {}
        print(f"taken by {r.get('who', '?')} since {r.get('since', '?')}")
    return False


def queue_stage(m: str):
    """The stage of an item as coord/queue.tsv lists it (None when the queue does not list it)."""
    q = WORK / "queue.tsv"
    if not q.exists():
        return None
    for l in q.read_text().splitlines():
        r = l.split("\t")
        if r and r[0] == m and len(r) > 1:
            return r[1]
    return None


def node_finished(m: str, stage=None) -> bool:
    """A stage-1 item is finished when its node file is no longer unsplit/imported (the queue may be stale);
    a stage-2 item (stage 2 opened 2026-10-11) when its node already records a Lean declaration (`lean.module`)
    or is a Mathlib leaf: a split node is exactly what stage 2 states, so the stage-1 rule must not refuse it."""
    hits = list((li.ROOT / "dag" / "nodes").glob(f"*/{m}.json"))
    if not hits:
        return False
    try:
        d = json.loads(hits[0].read_text())
    except Exception:
        return False
    if stage is None:
        stage = queue_stage(m)
    if str(stage) == "2":
        l = d.get("lean")
        if isinstance(l, dict) and l.get("module"):
            return True
        if isinstance(l, dict) and l.get("convention"):   # a convention node (L, 2026-10-11): no Lean notion, not an item
            return True
        return d.get("status") in ("mathlib", "merged")
    # launcher's order 2026-10-10 20:55 UTC: a node whose status is split, mathlib or merged is finished whether or not
    # `reviewed` is set (L's own split of lem-pc-ringed-space-module-stalk-tensor at 19:58 carried no `reviewed`, so
    # `next` handed the item to J1 at 20:14 after F1 had abandoned it for the same reason)
    if d.get("status") in ("split", "mathlib", "merged"):
        return True
    # launcher's finding, 2026-10-10 17:30 UTC: a node attached to a sorry-free Lean declaration (lean_audit closed or
    # attached) stays status unsplit but is finished; groups claimed such nodes eight times each
    la = d.get("lean_audit") or {}
    if la.get("state") in ("closed", "attached") or (la.get("slopmaster2") or {}).get("state") in ("closed", "attached"):
        return True
    return False


def attachment_pending(m: str) -> bool:
    """A node with an 'abandon: attachment <node>: ...' release in coord/deliveries.log that L has not yet processed:
    not Lean-closed (node_finished) and no ledger line 'NOT attached' / 'attachment refused' for it after the release.
    Such a node is not handed out to any group until L verifies the attachment (launcher, 2026-10-10 17:30 UTC)."""
    p = WORK / "deliveries.log"
    if not p.exists():
        return False
    last = None
    for line in p.read_text().splitlines():
        mm = re.match(r"(\S+)Z (\S+) abandoned (\S+): abandon: attachment ", line)
        if mm and mm.group(3) == m:
            last = mm.group(1)
    if last is None:
        return False
    led = WORK / "ledger.md"
    if led.exists():
        txt = led.read_text()
        tail = txt[txt.rfind(last[11:16]):] if last[11:16] in txt else ""
        if re.search(rf"{re.escape(m)} NOT attached|attachment refused.*{re.escape(m)}|{re.escape(m)}.*attachment refused", tail):
            return False
    return True


STAGE2_OPEN = "2026-10-11T05:05"
PARKED = WORK / "stage2-parked.md"


def stage2_abandonments() -> dict[str, list[tuple[str, str, str]]]:
    """item -> [(time, group, reason)] of the 'abandon:' releases in coord/deliveries.log after stage 2 opened, for items
    whose stage in coord/queue.tsv is 2 or which the queue no longer lists (an item of stage 1 is not parked)."""
    p = WORK / "deliveries.log"
    out: dict[str, list] = {}
    if not p.exists():
        return out
    q = WORK / "queue.tsv"
    stages = {}
    if q.exists():
        for l in q.read_text().splitlines():
            r = l.split("\t")
            if len(r) > 1 and not l.startswith("#"):
                stages[r[0]] = r[1]
    for line in p.read_text().splitlines():
        mm = re.match(r"(\S+)Z (\S+) abandoned (\S+): (abandon:.*)$", line)
        if not mm or mm.group(1) < STAGE2_OPEN:
            continue
        if "." in mm.group(3) or stages.get(mm.group(3), "2") != "2":
            continue
        out.setdefault(mm.group(3), []).append((mm.group(1), mm.group(2), mm.group(4)))
    return out


def parked_resolved() -> set[str]:
    """Items whose line `- <item> | ...` in coord/stage2-parked.md carries RESOLVED."""
    out = set()
    if PARKED.exists():
        for line in PARKED.read_text().splitlines():
            mm = re.match(r"- (\S+) \|", line)
            if mm and "RESOLVED" in line:
                out.add(mm.group(1))
    return out


def stage2_parked(m: str) -> bool:
    return m in stage2_abandonments() and m not in parked_resolved()


def queue(stage: str | None = None):
    q = WORK / "queue.tsv"
    if not q.exists():
        raise SystemExit("no coord/queue.tsv yet; the maintainer writes it after each build")
    rows = [l.split("\t") for l in q.read_text().splitlines() if l and not l.startswith("#")]
    if stage is not None:
        rows = [r for r in rows if len(r) > 1 and r[1] == stage]
    return [r[0] for r in rows]



def abandoned_recently(who, hours=24):
    """Items `who` released with 'abandon:' in the last `hours` hours (coord/deliveries.log); other groups and L may take them."""
    import datetime as _dt
    out = set()
    p = WORK / "deliveries.log"
    if not p.exists():
        return out
    now = _dt.datetime.now(_dt.timezone.utc)
    for line in p.read_text().splitlines():
        m = re.match(r"(\S+)Z (\S+) abandoned (\S+):", line)
        if m and m.group(2) == who:
            try:
                t = _dt.datetime.fromisoformat(m.group(1)).replace(tzinfo=_dt.timezone.utc)
            except ValueError:
                continue
            if (now - t).total_seconds() <= hours * 3600:
                out.add(m.group(3))
    return out

def main() -> int:
    a = sys.argv[1:]
    if not a or a[0] in ("-h", "--help", "help"):
        print(__doc__); return 0
    C.mkdir(parents=True, exist_ok=True)
    cmd = a[0]
    if cmd == 'note':
        print(json.dumps(repair_note(a[1]), ensure_ascii=False)); return 0
    if cmd == "next":
        who = a[1]; n = int(a[a.index("--count") + 1]) if "--count" in a else 1
        # decision of the human, 2026-10-10 evening: an open return no longer blocks new claims (every open return
        # must have a worker on it first, the remaining slots take new items; the cap of LIMIT claims per group stays)
        stage = a[a.index("--stage") + 1] if "--stage" in a else None
        n = min(n, LIMIT - len(held_by(who)))
        got = 0
        parked = set(stage2_abandonments()) - parked_resolved()
        skip = abandoned_recently(who)   # launcher's finding, 2026-10-10 15:30 UTC: C1 abandoned one item 29 times in half an
        repair_items = [p.stem for p in sorted((WORK / 'repair-notes').glob('*.json'))
                        if repair_note(p.stem).get('state') == 'released'] if stage in (None, '3') else []
        for m in dict.fromkeys(repair_items + queue(stage)):           # hour because next handed it straight back; a group skips its own abandonments for 24 h
            if got >= n:
                break
            if m in skip:
                continue
            if sorries(m) == 0 and m not in repair_items:  # finished since the queue was written
                continue
            if node_finished(m) and repair_note(m).get('state') != 'released':  # a DAG node split, matched or Lean-attached since the queue was written (stale queue.tsv)
                continue
            if attachment_pending(m):  # an attachment release L has not verified yet (launcher, 2026-10-10 17:30 UTC)
                continue
            if m in parked:  # abandoned in stage 2 by any group and not resolved by L (launcher, 2026-10-11 05:50 UTC)
                continue
            r = read(m)
            if (r is None or expired(r)) and take(who, m, quiet=True):
                got += 1
        if got == 0:
            print("nothing to claim" if n > 0 else f"{who} already holds {LIMIT} claims")
    elif cmd == "take":
        return 0 if take(a[1], a[2]) else 1
    elif cmd == "renew":
        r = read(a[2])
        if r and r["who"] == a[1]:
            r["t"] = time.time(); tmp = C / f".{a[2]}.{os.getpid()}"
            tmp.write_text(json.dumps(r)); os.replace(tmp, lock(a[2])); print("renewed")
        else:
            print("not your claim"); return 1
    elif cmd in ("done", "release"):
        who, m, note = a[1], a[2], " ".join(a[3:])
        r = read(m)
        if not r or r["who"] != who:
            print("not your claim"); return 1
        left = sorries(m)
        lock(m).unlink(missing_ok=True)
        if cmd == "done":
            np = WORK / 'repair-notes' / (m + '.json')
            nr = repair_note(m)
            if nr:
                nr['state'] = 'resolved'; np.write_text(json.dumps(nr, ensure_ascii=False))
            log(f"{who} done {m} (sorry left: {left}) {note}")
            print("done" + (f"; {left} sorry left, so the module returns to the queue" if left else ""))
        else:
            if who != "L":
                opened = [e for e in open_returns(who) if e.startswith(f"{m} (")]
                branch = subprocess.run(["git", "rev-parse", "--verify", "-q", f"refs/heads/deliver/{who}/{m}"],
                                        cwd=li.ROOT, capture_output=True, text=True).returncode == 0
                if (opened or branch) and not note.startswith("abandon:"):
                    # the lock was removed above; put it back unchanged
                    tmp = C / f".{m}.{os.getpid()}"; tmp.write_text(json.dumps(r)); os.replace(tmp, lock(m))
                    print(f"refused: {m} has " + (f"an open return entry in coord/returns/{who}.md" if opened else "")
                          + (" and " if opened and branch else "") + (f"a delivery branch deliver/{who}/{m}" if branch else "")
                          + ". Repair the delivery (push it) or abandon the item: give a reason starting with 'abandon:'; "
                          "an abandoned item is released, its delivery branch is deleted by the maintainer and the abandonment is counted for the group.")
                    return 1
                if note.startswith("abandon:"):
                    log(f"{who} abandoned {m}: {note}")
                    if drop_return_entries(who, m):
                        log(f"return entries of {who} for {m} dropped (item abandoned)")
                    print("abandoned; the maintainer deletes the delivery branch" if branch else "abandoned")
                    return 0
            log(f"{who} released {m}: {note}")
            if drop_return_entries(who, m):
                log(f"return entries of {who} for {m} dropped (item released)")
            print("released")
    elif cmd == "mine":
        print("\n".join(held_by(a[1])))
    elif cmd == "list":
        for p in sorted(C.glob("*.lock")):
            r = read(p.stem.replace("__", "/")) or {}
            age = (time.time() - r.get("t", 0)) / 3600
            print(f"{p.stem.replace("__", "/")}\t{r.get('who')}\t{r.get('since')}\t{age:.1f} h" + ("\texpired" if expired(r) else ""))
    elif cmd == "parked":
        res = parked_resolved()
        for m, ab in sorted(stage2_abandonments().items()):
            print(f"{m}\t{'RESOLVED' if m in res else 'OPEN'}\t{len(ab)} abandonment(s)")
            for t, g, why in ab:
                print(f"  {t}Z {g}: {why}")
    elif cmd == "expire":
        for p in sorted(C.glob("*.lock")):
            r = read(p.stem.replace("__", "/"))
            if expired(r):
                p.unlink(missing_ok=True); log(f"expired the claim of {r.get('who')} on {p.stem.replace("__", "/")}"); print(p.stem.replace("__", "/"))
    else:
        print(__doc__); return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
