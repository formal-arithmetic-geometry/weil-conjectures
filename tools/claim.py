#!/usr/bin/env python3
"""Claims: which group is working on which module, so that no two agents work on the same one.

Usage:
  tools/claim.py next <group> [--count N] [--stage S]   claim up to N items from the head of coord/queue.tsv, of stage S only
                                               if given; prints one item per line (a module, or a DAG node in stages 1 and 2)
  tools/claim.py take <group> <module>         claim a given module (also before changing someone else's statement)
  tools/claim.py take-many <g1> <m1> <g2> <m2> ...   take for many pairs; one line per pair: OK|NO, group, item[, reason]
  tools/claim.py take-many --with-stage <g1> <m1> <s1> ...   the same, each item claimed FOR the stage the caller will
                                               work it in: refused when the live node is already finished for that stage
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


def _lock_held_by_ancestor() -> bool:
    """True when coord/.merge.lock is held by one of our ancestors (merge_delivery.py, batch_land.py or a
    `flock coord/.merge.lock ...` running this tool): taking it again would wait for ourselves."""
    import mergelock
    h = mergelock.holder(mergelock.LOCK)
    if not h.startswith("pid ") or not h[4:].split(":")[0].isdigit():
        return False
    holder, pid = int(h[4:].split(":")[0]), os.getppid()
    while pid > 1:
        if pid == holder:
            return True
        try:
            pid = int(pathlib.Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[1])
        except (OSError, ValueError, IndexError):
            return False
    return False


def commit_bookkeeping(paths, msg):
    """Commit coord files this tool wrote (repair handoffs in coord/returns, repair-note states) under
    coord/.merge.lock, like the other tools; an uncommitted returns file blocks tools/retire_stage1.py.
    Under a lock held by the calling tool (merge_delivery.py, batch_land.py) that tool commits them."""
    rels = [pathlib.Path(p).resolve().relative_to(li.ROOT).as_posix() for p in paths if pathlib.Path(p).exists()]
    if not rels or _lock_held_by_ancestor():
        return
    import mergelock
    git = lambda *a: subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", *a],
                                    cwd=li.ROOT, capture_output=True, text=True, env=dict(os.environ, SHEAF_LEAD="L-only"))
    try:
        with mergelock.merge_lock():
            if not git("status", "--porcelain", "--untracked-files=all", "--", *rels).stdout.strip():
                return
            git("add", "--", *rels)
            msg += "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
            r = git("commit", "-q", "--only", "--author=Bin Wu <844524296@qq.com>", "-m", msg, "--", *rels)
            if r.returncode:
                time.sleep(2); r = git("commit", "-q", "--only", "--author=Bin Wu <844524296@qq.com>", "-m", msg, "--", *rels)
            if r.returncode:
                print("warning: bookkeeping commit failed: " + (r.stderr or r.stdout).strip()[:300], file=sys.stderr)
    except mergelock.LockTimeout as e:
        print(f"warning: bookkeeping left uncommitted ({e})", file=sys.stderr)


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
    # Scope the return to the snapshot being handed off. Without a head the
    # dispatcher treats every later push as the same unresolved return.
    ref = f'refs/heads/deliver/{who}/{m}'
    r = subprocess.run(['git', 'rev-parse', '-q', '--verify', ref], cwd=li.ROOT,
                       capture_output=True, text=True)
    head = r.stdout.strip() if r.returncode == 0 else subprocess.check_output(
        ['git', 'rev-parse', '--verify', 'HEAD'], cwd=li.ROOT, text=True).strip()
    p = RETURNS / (who + '.md'); p.parent.mkdir(parents=True, exist_ok=True)
    drop_return_entries(who, m)
    with open(p, 'a') as f:
        f.write('\n\n## ' + m + ' (dedicated repair handoff; head ' + head + ')\n\n'
                + 'The previous worker ended with: ' + nr.get('note', '')
                + '\n\nCompiler messages and attribution:\n' + nr.get('reason', '') + '\n')
    commit_bookkeeping([p], f"repair handoff to {who}: {m}")


def _delivered(who, m):
    import subprocess
    return subprocess.run(["git", "rev-parse", "-q", "--verify", f"refs/heads/deliver/{who}/{m}"], cwd=str(li.ROOT),
                          capture_output=True).returncode == 0


def retire_delivery(who, m):
    """Archive deliver/<who>/<m> at refs/superseded/<who>/<m>/<head> and delete it; the archived head, or None if there
    is no branch. Called when <who> abandons <m> (2026-10-18): the branch of an abandoned item was left to "the
    maintainer", nobody deleted it, and a delivery branch without a claim and without a return entry is dispatched to
    no one (the dispatcher counts every branch as taken), so the item was stuck for hours."""
    ref = f"refs/heads/deliver/{who}/{m}"
    r = subprocess.run(["git", "rev-parse", "-q", "--verify", ref], cwd=li.ROOT, capture_output=True, text=True)
    if r.returncode:
        return None
    head = r.stdout.strip()
    subprocess.run(["git", "update-ref", f"refs/superseded/{who}/{m}/{head}", head], cwd=li.ROOT, check=True)
    subprocess.run(["git", "update-ref", "-d", ref, head], cwd=li.ROOT, check=True)
    log(f"delivery branch of {who} for {m} archived at refs/superseded/{who}/{m}/{head} (item abandoned)")
    return head

_RETIRE = {}


def retire_items() -> set[str]:
    """the Sheaf copies of coord/retire-items.tsv (items of kind `retire`, tools/rework.py)"""
    if "s" not in _RETIRE:
        try:
            _RETIRE["s"] = {l.split("\t")[2] for l in (WORK / "retire-items.tsv").read_text().splitlines()
                            if l.strip() and not l.startswith("#") and len(l.split("\t")) > 2}
        except OSError:
            _RETIRE["s"] = set()
    return _RETIRE["s"]


def _withdrawn(m: str) -> bool:
    """the module is gone from lean/ or is the stub deliver3.py leaves when it withdraws a module (tools/rework.py _present)"""
    f = li.file_of(m)
    if not f.is_file():
        return True
    try:
        t = f.read_text(errors="ignore")
    except OSError:
        return False
    return len(t) < 200 and "Withdrawn: no declarations remain." in t


def take(who, m, quiet=False, stage=None) -> bool:
    """`stage`: the stage the caller will work the item in (take-many --with-stage). 2026-10-19 (stale dispatch): the
    dispatcher claimed from its copy of coord/queue.tsv, a merge rewrote the queue meanwhile (stage 1 -> 2), and the
    stage-blind check below then judged a just-merged, reviewed split by the stage-2 rule (no Lean yet: open) and granted
    the claim; the worker was started with the stage-1 brief and answered BLOCKED "already split and reviewed"
    (~40-100 sessions an hour). Judged for the caller's stage, such a claim is refused."""
    claim_stage = str(stage or queue_stage(m) or
                      ("3" if "." in m or li.file_of(m).is_file() else "1"))
    if claim_stage in ("1", "2") and not node_published(m):
        if not quiet:
            print(f"{m} has no published DAG node in the live sources; nothing to claim")
        return False
    if stage is not None and node_finished(m, stage) and repair_note(m).get('state') != 'released':
        if not quiet:
            print(f"{m} is already completed for stage {stage} (live node); nothing to claim for that stage")
        return False
    if li.file_of(m).is_file() and sorries(m) == 0 and repair_note(m).get('state') != 'released' \
            and not any(l.split()[:1] == [m] for l in (WORK / 'repairs.txt').read_text().splitlines()) \
            and m not in retire_items():   # 2026-10-20: a `retire` item (coord/retire-items.tsv) has no sorry to prove
        # launcher, 2026-10-16: a module proved on the main branch is not claimable even while the queue still lists it
        # (between a landing and the next queue refresh groups claimed just-proved modules and ended BLOCKED)
        if not quiet:
            print(f"{m} has no sorry on the main branch; nothing to claim")
        return False
    if m in retire_items() and _withdrawn(m):
        # 2026-10-21: a retire item whose retirement landed (the module is the withdrawn stub, or gone) is no work; between
        # the landing and the next queue refresh it was claimed again and the worker answered BLOCKED (~30-80 runs an hour)
        if not quiet:
            print(f"{m} is already retired (withdrawn stub on the main branch); nothing to claim")
        return False
    if stage2_parked(m):   # launcher's order 2026-10-11 05:50 UTC: parked for every group until L resolves it
        if not quiet:
            print(f"{m} is parked in stage 2 (abandoned; see tools/claim.py parked and coord/stage2-parked.md); nothing to claim")
        return False
    # node_finished is stage-aware: a stage-2 split is open until it has a Lean
    # record. Recheck even queued stage-2 items: queue.tsv can predate a landing.
    if node_finished(m) and repair_note(m).get('state') != 'released':
        if not quiet:
            print(f"{m} is already completed for its queued stage; nothing to claim")
        return False
    # 2026-10-16: a held item already delivered (its branch waits for review) does not count toward the cap, so a
    # group keeps working while its deliveries wait; the cap limits items in work, not deliveries in review
    if len([x for x in held_by(who) if not _delivered(who, x)]) >= LIMIT:
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



def take_many(pairs, stages=None):
    """`take` for many (group, item) pairs in one call (launcher, 2026-10-17: the dispatcher claimed one item per ssh
    call, about 12 starts a minute). Prints one line per pair, `OK<TAB>group<TAB>item` or `NO<TAB>group<TAB>item<TAB>reason`,
    and returns. The repair handoffs written meanwhile are committed afterwards in one bookkeeping commit by a detached
    child, so a busy coord/.merge.lock no longer delays the answer."""
    import contextlib, io
    deferred, msgs = [], []
    real = globals().get("commit_bookkeeping")
    if real is not None:
        globals()["commit_bookkeeping"] = lambda paths, msg: (deferred.extend(paths), msgs.append(msg))
    try:
        for k, (who, m) in enumerate(pairs):
            buf = io.StringIO()
            try:
                with contextlib.redirect_stdout(buf):
                    ok = take(who, m, stage=stages[k] if stages else None)
            except Exception as e:   # one bad pair never costs the others their answer
                ok = False; buf.write(f"error: {e!r}")
            reason = " ".join(buf.getvalue().split())
            print(f"OK\t{who}\t{m}" if ok else f"NO\t{who}\t{m}\t{reason[:300]}")
    finally:
        if real is not None:
            globals()["commit_bookkeeping"] = real
    sys.stdout.flush()
    if real is not None and deferred:
        if os.fork() == 0:
            try:
                os.setsid()
                fd = os.open(os.devnull, os.O_RDWR)
                for k in (0, 1, 2): os.dup2(fd, k)
                real(list(dict.fromkeys(deferred)), "repair handoffs (take-many): " + "; ".join(x.split(": ", 1)[-1] for x in msgs)[:400])
            finally:
                os._exit(0)
    return 0


def queue_stage(m: str):
    """Return the highest queued stage (duplicate rows can represent a keep-plan re-split)."""
    q = WORK / "queue.tsv"
    if not q.exists():
        return None
    stages = []
    for l in q.read_text().splitlines():
        r = l.split("\t")
        if r and r[0] == m and len(r) > 1 and r[1].isdigit():
            stages.append(int(r[1]))
    # A released keep-plan node can have its stage-1 repair row beside the
    # stage-2 formalization row.  The first-match result dispatched stage 1
    # repeatedly, although the handoff explicitly required stage-2 evidence.
    return str(max(stages)) if stages else None


def node_file(m: str):
    """The node file the queue reads: dag_queue.nodes_dir() (SHEAF_DAG in coord/sheaf.env, the live DAG for this
    isolated project since 2026-10-16), else the project's own dag/nodes. 2026-10-18: claim.py read only the project's
    own copy, which the sync keeps a side-owned split's `reviewed` in; the queue read the live node without it."""
    import dag_queue
    for base in dict.fromkeys((dag_queue.nodes_dir(), li.ROOT / "dag" / "nodes")):
        hits = list(base.glob(f"*/{m}.json"))
        if hits:
            return hits[0]
    return None


def node_published(m: str) -> bool:
    """A DAG assignment needs a readable node committed in the repository supplying it.

    A queue can briefly include new nodes from a provisional landing that is later rolled back.
    Neither that queue row nor a file staged by the landing makes an assignment available to
    workers reading the committed branch. Check HEAD in the node's own repository so configured
    external DAGs still work. Stage-3 rework items can lack DAG nodes and do not use this check.
    """
    hit = node_file(m)
    if hit is None:
        return False
    return subprocess.run(
        ["git", "cat-file", "-e", f"HEAD:./{hit.name}"], cwd=hit.parent,
        capture_output=True, text=True,
    ).returncode == 0


def node_finished(m: str, stage=None) -> bool:
    """A stage-1 item is finished when its node file is no longer unsplit/imported (the queue may be stale);
    a stage-2 item (stage 2 opened 2026-10-11) when its node already records a Lean declaration (`lean.module`)
    or is a Mathlib leaf: a split node is exactly what stage 2 states, so the stage-1 rule must not refuse it."""
    hit = node_file(m)
    if hit is None:
        return False
    try:
        d = json.loads(hit.read_text())
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
    # 2026-10-18 (s1loop): stage-1 claimability is dag_queue.stage1_completed, the predicate stage1() and the stage-1
    # landing (tools/retire_stage1.py) use, read on the node the queue reads (node_file). It holds the earlier rules: the
    # recorded first-task completions and the closed audit (finished), a split whose review stands (unfolded; a split
    # whose review was withdrawn is claimable again, the human 2026-10-18), Mathlib leaves and merged nodes; and it adds
    # that a released stage-1 repair note keeps a split open until its repair lands. Before, an attached node whose audit
    # was closed_part and a split with an owed repair note were judged differently here, in stage1() and at the landing,
    # and such items were dispatched, delivered and archived as already completed over and over (thm-sf-pf-proetale ~60
    # times, lem-sfb-modobj-abelian). The raw lean_audit 'closed'/'attached' test of 2026-10-10 is covered by finished().
    import dag_queue
    return dag_queue.stage1_completed(d)


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
    return False and m in stage2_abandonments() and m not in parked_resolved()


def queue(stage: str | None = None):
    q = WORK / "queue.tsv"
    if not q.exists():
        raise SystemExit("no coord/queue.tsv yet; the maintainer writes it after each build")
    rows = [l.split("\t") for l in q.read_text().splitlines() if l and not l.startswith("#")]
    if stage is not None:
        rows = [r for r in rows if len(r) > 1 and r[1] == stage]
    return [r[0] for r in rows]



def abandoned_recently(who, hours=24):
    return set()   # human, 2026-10-16: no dispatch restrictions
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
        rp = WORK / 'repairs.txt'
        listed_repairs = {l.split()[0] for l in rp.read_text().splitlines() if l.strip() and not l.lstrip().startswith('#')} if rp.exists() else set()
        # the human, 2026-10-14: no lockout of a group from an item it gave up; every attempt is a fresh worker, so the
        # same group taking it again is no different from another group (groups now keep their items; stalls are inspected)
        skip = set()   # launcher's finding, 2026-10-10 15:30 UTC: C1 abandoned one item 29 times in half an
        repair_items = [p.stem for p in sorted((WORK / 'repair-notes').glob('*.json'))
                        if repair_note(p.stem).get('state') == 'released'] if stage in (None, '3') else []
        for m in dict.fromkeys(repair_items + queue(stage)):           # hour because next handed it straight back; a group skips its own abandonments for 24 h
            if got >= n:
                break
            if m in skip:
                continue
            if sorries(m) == 0 and m not in repair_items and m not in listed_repairs and m not in retire_items():  # finished since the queue was written
                # (an item of coord/repairs.txt is a repair even without a `sorry`: a false statement, a duplicate,
                # undetermined data; 2026-10-14 all 25 queued repairs were skipped here and nobody could claim them)
                continue
            # Recheck the node even for stage 2; a stale queue may list a landed statement.
            if node_finished(m) and repair_note(m).get('state') != 'released':
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
    elif cmd == "take-many":
        rest = a[1:]
        if rest[:1] == ["--with-stage"]:
            rest = rest[1:]
            return take_many(list(zip(rest[0::3], rest[1::3])), stages=list(rest[2::3]))
        return take_many(list(zip(rest[0::2], rest[1::2])))
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
                commit_bookkeeping([np], f"repair note resolved: {m} ({who})")
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
                          "an abandoned item is released, its delivery branch is archived under refs/superseded and the abandonment is counted for the group.")
                    return 1
                if note.startswith("abandon:"):
                    log(f"{who} abandoned {m}: {note}")
                    if drop_return_entries(who, m):
                        log(f"return entries of {who} for {m} dropped (item abandoned)")
                        commit_bookkeeping([RETURNS / f"{who}.md"], f"return entries of {who} for {m} dropped (abandoned)")
                    head = retire_delivery(who, m)
                    print(f"abandoned; the delivery branch is archived at refs/superseded/{who}/{m}/{head} and the item is open" if head else "abandoned")
                    return 0
            log(f"{who} released {m}: {note}")
            if drop_return_entries(who, m):
                log(f"return entries of {who} for {m} dropped (item released)")
                commit_bookkeeping([RETURNS / f"{who}.md"], f"return entries of {who} for {m} dropped (released)")
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
