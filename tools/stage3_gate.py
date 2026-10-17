#!/usr/bin/env python3
"""The mechanical gate of a stage-3 delivery (decision of the human, 2026-10-17: stage-3 deliveries need no reader;
check mechanically that nothing cycles, no axiom or sorry slips in, no used statement changes).

gate(D, group, item) -> (verdict, reasons), verdict one of
  REFUSE  the delivery goes back to its group with the reasons (tools/review_class.py puts them into D["fails"], and
          tools/batch_land.py returns a delivery with failed static checks);
  READER  the gate cannot decide: the statement of an existing declaration that a DAG node records, or that
          SHEAF_GATE_WIDE or more other modules use, is changed or removed, or the import of a unit-route module is
          removed. The cc review service (~/weil-review-svc, lane S3) reads it;
  AUTO    landed by ~/cc1/autoland3.py through tools/batch_land.py; the global build verifies it.

What the gate refuses, besides the static checks a-e of tools/stage3_delivery.py (paths a delivery may change,
ownership of adapted modules, target statements, new axiom/unsafe/extern/opaque/sorryAx, a sorry only as a named
theorem with its node, change records):
  1. an import cycle: the delivered modules' imports against the library's import graph (tools/import_cycles.py, as
     ~/cc1/proof-imports-cycle.sh and tools/batch_land.py check it);
  2. `sorry` put into a declaration that had none (a proved result replaced by sorry);
  3. `sorry` added while no sorried declaration is proved and the sorry count of the delivered modules does not fall
     (a stage-3 delivery claims proof progress).
The global build (tools/build.py) then enforces compile, the axiom probe (only propext, Classical.choice, Quot.sound;
no sorryAx outside the declarations the landing may leave with sorry) and 60 s per file; a red build takes the
delivery at fault out again (tools/batch_land.py triage).
"""
from __future__ import annotations
import collections, os, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import stage2_delivery as s2  # noqa: E402
import stage3_delivery as s3  # noqa: E402

ROOT = s3.ROOT
WIDE = int(os.environ.get("SHEAF_GATE_WIDE", "3"))      # modules using a changed declaration: a reader from this many
_DMAP = {}


def declaration_map(base: str) -> dict[str, str]:
    git = s2.Git(ROOT)
    tree = git.run("rev-parse", f"{base}:dag/nodes").strip()
    if tree not in _DMAP:
        if len(_DMAP) >= 4:
            _DMAP.pop(next(iter(_DMAP)))
        _DMAP[tree] = s2.declaration_map(s2.nodes_at(git, base))
    return _DMAP[tree]


def short(names, k=3):
    names = list(names)
    return ", ".join(names[:k]) + (f" (+{len(names) - k})" if len(names) > k else "")


def import_cycle(D: dict, graph=None) -> list[str] | None:
    import import_cycles as cycles, leanindex as li
    g = graph if graph is not None else cycles.graph(li.LEAN)
    return cycles.closing_cycle(g, {m["module"]: m["text"] for m in D["modules"]})


def gate(D: dict, group: str, item: str, graph=None, cycle_check: bool = True) -> tuple[str, list[str]]:
    refuse, reader = [], []
    if cycle_check:
        try:
            cyc = import_cycle(D, graph)
        except Exception as e:  # noqa: BLE001   batch_land checks the cycle again under its own snapshot
            cyc = None; D.setdefault("notes", []).append("gate: import-cycle check skipped: " + repr(e)[:120])
        if cyc:
            refuse.append("import cycle: " + " -> ".join(cyc))
    before = after = 0
    proved, new_sorry = [], []
    for m in D["modules"]:
        d = m["diff"]
        old = d["old"]
        hollowed = [k for k in d["new_sorry"] if k in old and not old[k]["sorry"]]
        if hollowed:
            refuse.append(f"{m['module']}: puts `sorry` into {short(hollowed)}, proved before the delivery "
                          "(a proved declaration keeps its proof)")
        before += len(d["sorry_before"]); after += len(d["sorry_after"])
        proved += [k for k in d["sorry_before"] if k in d["new"] and k not in d["sorry_after"]]
        new_sorry += d["new_sorry"]
    # the human, 2026-10-17 (upstream sync e47efb5a5): statements in the adopted source library stay verbatim; a
    # delivery may fill proof bodies of existing theorems there and add private helpers, nothing else
    UPNOTE = "upstream statements are verbatim; prove it or state the needed variant in a `Sheaf` module"
    for m in D["modules"]:
        if not m["file"].startswith("lean/WeilConjectures/"):
            continue
        d = m["diff"]
        if m["role"] == "new" or m.get("old") is None:
            refuse.append(f"{m['module']}: new module in the source library tree ({UPNOTE})"); continue
        bad = []
        if d["statement_changed"]: bad.append("changes the statement of " + short(d["statement_changed"]))
        if d["removed"]: bad.append("removes " + short(d["removed"]))
        if d["public_added"]: bad.append("adds public declaration(s) " + short(d["public_added"]))
        data = [k for k in d["body_changed"] if d["old"][k]["kw"] not in ("theorem", "lemma")]
        if data: bad.append("changes the body of non-theorem declaration(s) " + short(data))
        attrs = [k for k in d["new"] if k in d["old"] and d["old"][k].get("head") != d["new"][k].get("head")]
        if attrs: bad.append("changes attributes of " + short(attrs))
        # a private `import Sheaf.*` is allowed: proofs of upstream sorries use our lemmas, and the integration agent sends
        # the imported modules upstream with the closer (human, 2026-10-17); public import changes stay refused below
        if d["public_imports_changed"]: bad.append("changes public imports " + short(d["public_imports_changed"]))
        if bad:
            refuse.append(f"{m['module']}: " + "; ".join(bad) + f" ({UPNOTE})")
    if new_sorry and not proved and after >= before:
        refuse.append(f"adds `sorry` ({short(new_sorry)}) but proves no declaration that had one, and the sorry count of "
                      f"the delivered modules does not fall ({before} -> {after})")
    if refuse:
        return "REFUSE", refuse
    repair = s3.repair_job(group, item) is not None
    users = collections.Counter()
    for mod, names in (D.get("users") or {}).items():
        for n in set(names):
            users[n] += 1
    dmap = None
    for m in D["modules"]:
        if m["role"] == "new":
            continue
        d = m["diff"]
        touched = [k for k in d["statement_changed"] + d["removed"] if not d["old"].get(k, {}).get("private")]
        if not touched:
            continue
        if dmap is None:
            dmap = declaration_map(D["base"])
        def full(k):
            return k if k in dmap else next((x for x in dmap if x.endswith("." + k)), k)
        recorded = [k for k in touched if full(k) in dmap]
        wide = [k for k in touched if max(users.get(k, 0), users.get(full(k), 0),
                                         max((c for n, c in users.items() if n.endswith("." + k)), default=0)) >= WIDE]
        if (recorded or wide) and not repair:
            what = "changes the statement of" if any(k in d["statement_changed"] for k in recorded + wide) else "removes"
            reader.append(f"{what} " + short(dict.fromkeys(recorded + wide)) + f" in {m['module']}: "
                          + ("recorded by DAG node(s) " + short(sorted({dmap[full(k)] for k in recorded})) if recorded else "")
                          + ("; " if recorded and wide else "") + (f"used by {WIDE}+ other modules" if wide else ""))
    removed_routes = [r for r in (s3.classify(D, group, item)) if r.startswith("removes the import of unit-route")]
    reader += removed_routes
    return ("READER", reader) if reader else ("AUTO", [])


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) != 2:
        print(__doc__); sys.exit(2)
    g, item = a
    git = s2.Git(ROOT)
    br = f"deliver/{g}/{item}"
    base = git.run("merge-base", "sheaf-dag", br).strip()
    D = s3.read_delivery(git, br, base, g, item)
    v, why = gate(D, g, item)
    if D["fails"]:
        v, why = "REFUSE", [f"({L}) {x}" for L, x in D["fails"][:6]] + why
    print(v + ("" if not why else ": " + "; ".join(why)))
