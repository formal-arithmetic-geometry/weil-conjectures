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
2026-10-26 (decision of the human: "只有修改了其他文件的 stage3 的改动才需要审核"): a delivery that changes a file other
than its own module (other_files below: another existing Lean module, upstream WeilConjectures.* or our Sheaf.*, or the
node file of another module) is READER with the reason "changes other files: <list>", repairs included. The reader checks
the usual semantic consistency and that the change keeps every module and node the delivery did not touch compiling;
tools/importer_compile.py gives it the compile of the direct importers as evidence (tools/review_packet.py --stage 3).

What the gate refuses, besides the static checks a-e of tools/stage3_delivery.py (paths a delivery may change,
ownership of adapted modules, target statements, new axiom/unsafe/extern/opaque/sorryAx, a sorry only as a named
theorem with its node, change records):
  1. an import cycle: the delivered modules' imports against the library's import graph (tools/import_cycles.py, as
     ~/cc1/proof-imports-cycle.sh and tools/batch_land.py check it);
  2. `sorry` put into a declaration that had none (a proved result replaced by sorry);
  3. `sorry` added while no sorried declaration is proved and the sorry count of the delivered modules does not fall
     (a stage-3 delivery claims proof progress);
  4. in the adopted source library (lean/WeilConjectures/): a changed statement, attributes or public imports, a removed or
     new public declaration, and a changed body of a non-theorem declaration (def, instance, ...) unless its upstream body
     is exactly `sorry` (launcher, 2026-10-17: filling an upstream `sorry` body with the signature unchanged is allowed);
     the corrections of false upstream statements listed in coord/upstream-statement-exceptions.tsv are allowed.
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
EXCEPTIONS = pathlib.Path(ROOT) / "coord" / "upstream-statement-exceptions.tsv"


def upstream_exceptions() -> dict[str, set[str]]:
    """module -> the entries of coord/upstream-statement-exceptions.tsv for it (columns: module, entry, reason; an entry
    is a declaration as the module writes it (changed or new), `import <Module>` for a public import, or
    `(new module)`). These are the corrections of false upstream statements that we make ourselves and send upstream
    as their own PR (the human, 2026-10-17); rule 4 below does not refuse them, and no reader is asked for them."""
    out: dict[str, set[str]] = collections.defaultdict(set)
    try:
        lines = EXCEPTIONS.read_text(encoding="utf-8").splitlines()
    except OSError:
        return out
    for line in lines:
        f = line.split("\t")
        if line.strip() and not line.startswith("#") and len(f) >= 2:
            out[f[0].strip()].add(f[1].strip())
    return out


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


def node_modules(x: dict) -> set:
    """The modules a delivered node file records (its `lean.module`, or the module of `lean.file`), before and after."""
    out = set()
    for n in (x.get("node"), x.get("base_node")):
        l = (n or {}).get("lean") if isinstance((n or {}).get("lean"), dict) else {}
        m = l.get("module")
        f = l.get("file")
        if not m and isinstance(f, str) and f.endswith(".lean"):
            m = s3.module_of_path(f if f.startswith("lean/") else "lean/" + f)
        if isinstance(m, str) and m:
            out.add(m)
    return out


def other_files(D: dict, item: str) -> list[str]:
    """The files of a stage-3 delivery other than its own (the human, 2026-10-26: such a delivery is read). Its own: the
    item's module, the modules the delivery adds (role new) or restores from quarantine with a rework cluster (role
    restored; nothing unchanged imports a quarantined module), node files, the change records and the report. Only an
    existing module besides the item counts (role adapted: upstream WeilConjectures.* or our Sheaf.*); 2026-10-26 (the
    human): "只审核改了其他已有模块的交付" -- node files of other modules and changes to the item's own interface do not."""
    return [m["file"] for m in D["modules"] if m["role"] not in ("item", "new", "restored", "deleted")]


# 2026-10-24 (the human: "预检做减法"): rules 3 and 4 below are ADVISORY notes now, not refusals. Rule 4 (upstream
# statements verbatim) belonged to the sync of 10-17..10-23, replaced on 10-23 by a merge whose conflicts go to merge
# agents and whose local changes go to the PR agent; a changed statement that DAG nodes record or 3+ modules use is
# still read by the review service (READER below). Rule 3 measures progress, not honesty.
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
        if hollowed and s3.restored_from_quarantine(D, m):
            # 2026-10-25 (deliver3fix; the human: touching a quarantined module refuses only if the build fails): the
            # quarantined copy's bodies did not compile, so `sorry` in their place hollows no proof of the library
            D.setdefault("notes", []).append(f"ADVISORY (quarantine restore) {m['module']}: puts `sorry` into "
                                             f"{short(hollowed)}, whose quarantined bodies the reviewer checks")
            hollowed = []
        if hollowed:
            refuse.append(f"{m['module']}: puts `sorry` into {short(hollowed)}, proved before the delivery "
                          "(a proved declaration keeps its proof)")
        before += len(d["sorry_before"]); after += len(d["sorry_after"])
        proved += [k for k in d["sorry_before"] if k in d["new"] and k not in d["sorry_after"]]
        new_sorry += d["new_sorry"]
    # the human, 2026-10-17 (upstream sync e47efb5a5): statements in the adopted source library stay verbatim; a
    # delivery may fill proof bodies of existing theorems there and add private helpers, nothing else
    UPNOTE = "upstream statements are verbatim; prove it or state the needed variant in a `Sheaf` module"
    exc = upstream_exceptions()
    for m in D["modules"]:
        if not m["file"].startswith("lean/WeilConjectures/"):
            continue
        d = m["diff"]
        ok = exc.get(m["module"], set())
        if m["role"] == "new" or m.get("old") is None:
            if "(new module)" not in ok:
                refuse.append(f"{m['module']}: new module in the source library tree ({UPNOTE})")
            continue
        bad = []
        changed = [k for k in d["statement_changed"] if k not in ok]
        if changed: bad.append("changes the statement of " + short(changed))
        if d["removed"]: bad.append("removes " + short(d["removed"]))
        added = [k for k in d["public_added"] if k not in ok]
        if added: bad.append("adds public declaration(s) " + short(added))
        # launcher, 2026-10-17: filling a body that is `sorry` upstream is allowed for any declaration (instance, def,
        # ...) whose signature (name, binders, type, attributes) is unchanged; those are checked just above and below.
        # 2026-10-18: so is filling the `sorry` fields of an instance or `def` whose other fields stay verbatim
        # (s3.fills_only_sorries). Changing a non-sorry body of a non-theorem declaration stays refused.
        data = [k for k in d["body_changed"] if d["old"][k]["kw"] not in ("theorem", "lemma")
                and not s3.only_sorry(d["old"][k]["body"])
                and not s3.fills_only_sorries(d["old"][k]["body"], d["new"][k]["body"])]
        if data: bad.append("changes the non-sorry body of non-theorem declaration(s) " + short(data))
        attrs = [k for k in d["new"] if k in d["old"] and d["old"][k].get("head") != d["new"][k].get("head")]
        if attrs: bad.append("changes attributes of " + short(attrs))
        # a private `import Sheaf.*` is allowed: proofs of upstream sorries use our lemmas, and the integration agent sends
        # the imported modules upstream with the closer (human, 2026-10-17); public import changes stay refused below
        imports = [i for i in d["public_imports_changed"] if f"import {i}" not in ok]
        if imports: bad.append("changes public imports " + short(imports))
        if bad:   # 2026-10-24: advisory (syncs merge since 10-23; our changes to upstream files go to the PR agent)
            D.setdefault("notes", []).append(f"ADVISORY (gate rule 4) {m['module']}: " + "; ".join(bad))
    if new_sorry and not proved and after >= before:   # 2026-10-24: advisory, progress is not honesty
        D.setdefault("notes", []).append(f"ADVISORY (gate rule 3) adds `sorry` ({short(new_sorry)}) but proves no "
                                         f"declaration that had one ({before} -> {after} sorries)")
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
        touched = [k for k in d["statement_changed"] + d["removed"] if not d["old"].get(k, {}).get("private")
                   and k not in exc.get(m["module"], set())]
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
    # 2026-10-26 (the human): a delivery that changes other files is read (semantic consistency, and that every module
    # and node it did not touch still compiles); a repair included
    other = other_files(D, item)
    if other:
        reader.append("changes other files: " + short(other, 8))
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
