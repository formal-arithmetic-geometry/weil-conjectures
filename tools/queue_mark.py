#!/usr/bin/env python3
"""Marks on the task list at the moment of the event (the human, 2026-10-22: an item is marked reviewed as soon as its
review verdict lands it, done as soon as its landing succeeds, rework when the landing is dropped).

  tools/queue_mark.py reviewed <stage|-> <item>...   a review verdict landed the delivery
  tools/queue_mark.py done <stage|-> <item>...       the landing succeeded (stage 1: merged; stage 2: the statement's
                                                     commit is on live; stage 3: the proof's commit is on live, again
                                                     when the global build verifies it). A stage-3 module that still
                                                     holds a `sorry` is marked `landed` instead and stays on the list.
  tools/queue_mark.py rework <stage|-> <item>...     the landing was dropped on a red build; the item is work again

Every mark is appended to coord/queue-states.tsv (item, stage, state, time, note). `done` also removes the item's rows
(of that stage, or all with `-`) from coord/queue.tsv and from the tags files (coord/queue-batches.tsv,
coord/queue-batches-all.tsv) at once, so no claim of a finished task is granted between the event and the next
`tools/queue.py write`, which recomputes the list from the live sources and remains the authority.

The human, 2026-10-25: a delivery leaves the queue at the moment it lands (its commit reaches live), not when the
global build verifies it; tools/batch_land.py and tools/stage2_batch.py call `done` right after the landing commit.
A `tools/queue.py write` that started before a `done` mark computed its list from the tree before that landing; it
drops the items marked done since it started (done_since), under the same lock (coord/.queue-mark.lock)."""
import fcntl, os, pathlib, re, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
Q = ROOT / "coord" / "queue.tsv"
TAGS = (ROOT / "coord" / "queue-batches.tsv", ROOT / "coord" / "queue-batches-all.tsv")
STATES = ROOT / "coord" / "queue-states.tsv"
LOCK = ROOT / "coord" / ".queue-mark.lock"
_COMMENTS = re.compile(r"--[^\n]*|/-.*?-/", re.S)


def has_sorry(module: str) -> bool:
    f = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    try:
        return "sorry" in _COMMENTS.sub("", f.read_text(errors="ignore"))
    except OSError:
        return False


def _replace(path: pathlib.Path, text: str):
    """written whole, then renamed: readers (claim.py, the dispatcher's ssh read) never see a half-written file"""
    tmp = path.with_name(f".{path.name}.qm{os.getpid()}.tmp")
    tmp.write_text(text)
    os.replace(tmp, path)


def drop_rows(lines, gone):
    """the lines of queue.tsv without the rows of `gone` ({(item, stage)}; stage `-` means every stage)"""
    keep = []
    for l in lines:
        c = l.rstrip("\n").split("\t")
        if not l.startswith("#") and l.strip() and len(c) > 1 and ((c[0], c[1]) in gone or (c[0], "-") in gone):
            continue
        keep.append(l)
    return keep


def _drop_locked(gone):
    """remove the rows of `gone` from queue.tsv and, for items no longer listed at any stage, from the tags files.
    Caller holds LOCK."""
    if not gone or not Q.exists():
        return
    lines = Q.read_text().splitlines(True)
    keep = drop_rows(lines, gone)
    if len(keep) != len(lines):
        _replace(Q, "".join(keep))
    listed = {l.split("\t", 1)[0] for l in keep if not l.startswith("#") and l.strip()}
    items = {it for it, _ in gone} - listed
    for t in TAGS:
        if not items or not t.exists():
            continue
        tl = t.read_text().splitlines(True)
        tk = [l for l in tl if l.startswith("#") or l.split("\t", 1)[0].strip() not in items]
        if len(tk) != len(tl):
            _replace(t, "".join(tk))


def mark(state: str, stage: str, items, note: str = ""):
    stamp = time.strftime("%FT%TZ", time.gmtime())
    with open(LOCK, "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        out = []
        for it in items:
            st = "landed" if state == "done" and "." in it and has_sorry(it) else state
            out.append((it, st))
        with open(STATES, "a") as f:
            for it, st in out:
                f.write(f"{it}\t{stage}\t{st}\t{stamp}\t{note}\n")
        _drop_locked({(it, stage) for it, st in out if st == "done"})
        return out


def done_since(t0: float, tail: int = 4 << 20):
    """{(item, stage)} whose last mark at or after t0 (epoch seconds) is `done` (a later `rework` or `landed` of the
    item cancels it). Reads the end of coord/queue-states.tsv only."""
    since = time.strftime("%FT%TZ", time.gmtime(int(t0) - 1))
    last = {}
    try:
        with open(STATES, "rb") as f:
            f.seek(0, 2); n = f.tell(); f.seek(max(0, n - tail))
            data = f.read().decode(errors="replace")
    except OSError:
        return set()
    for l in data.splitlines():
        c = l.split("\t")
        if len(c) < 4 or c[3] < since:
            continue
        if c[2] in ("rework", "landed"):   # a later rework/landed mark of the item reopens every stage marked done
            for k in [k for k in last if k[0] == c[0]]:
                last[k] = c[2]
        if c[2] in ("done", "rework", "landed"):
            last[(c[0], c[1])] = c[2]
    return {k for k, v in last.items() if v == "done"}


def main():
    a = sys.argv[1:]
    note = ""
    if "--note" in a:
        i = a.index("--note"); note = a[i + 1]; a = a[:i] + a[i + 2:]
    if len(a) < 3 or a[0] not in ("reviewed", "done", "rework"):
        print(__doc__); return 2
    for it, st in mark(a[0], a[1], a[2:], note):
        print(f"{st}\t{a[1]}\t{it}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
