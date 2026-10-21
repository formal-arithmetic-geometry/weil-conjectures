#!/usr/bin/env python3
"""Marks on the task list at the moment of the event (the human, 2026-10-22: an item is marked reviewed as soon as its
review verdict lands it, done as soon as its landing succeeds, rework when the landing is dropped).

  tools/queue_mark.py reviewed <stage|-> <item>...   a review verdict landed the delivery
  tools/queue_mark.py done <stage|-> <item>...       the landing succeeded (stage 1: merged; stage 2 and 3: verified by the
                                                     global build). A stage-3 module that still holds a `sorry` is marked
                                                     `landed` instead and stays on the list.
  tools/queue_mark.py rework <stage|-> <item>...     the landing was dropped on a red build; the item is work again

Every mark is appended to coord/queue-states.tsv (item, stage, state, time, note). `done` also removes the item's rows
(of that stage, or all with `-`) from coord/queue.tsv at once, so no claim of a finished task is granted between the event
and the next `tools/queue.py write`, which recomputes the list from the live sources and remains the authority."""
import fcntl, os, pathlib, re, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
Q = ROOT / "coord" / "queue.tsv"
STATES = ROOT / "coord" / "queue-states.tsv"
LOCK = ROOT / "coord" / ".queue-mark.lock"
_COMMENTS = re.compile(r"--[^\n]*|/-.*?-/", re.S)


def has_sorry(module: str) -> bool:
    f = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    try:
        return "sorry" in _COMMENTS.sub("", f.read_text(errors="ignore"))
    except OSError:
        return False


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
        gone = {it for it, st in out if st == "done"}
        if gone and Q.exists():
            lines = Q.read_text().splitlines(True)
            keep = []
            for l in lines:
                c = l.rstrip("\n").split("\t")
                if l.startswith("#") or not l.strip() or c[0] not in gone or (stage != "-" and len(c) > 1 and c[1] != stage):
                    keep.append(l)
            if len(keep) != len(lines):
                tmp = Q.with_name("queue.tsv.tmp")
                tmp.write_text("".join(keep))
                os.replace(tmp, Q)
        return out


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
