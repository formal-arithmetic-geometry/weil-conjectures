#!/usr/bin/env python3
"""Batch landing of stage-3 deliveries (decision of the human, 2026-10-12): deliveries land together, without a compile
on the server, and the global build is the judge.

A group's delivery tool compiles every module of a delivery with the probe on the group's machine before it pushes
the branch. The server does not compile the delivery again. One cycle:

  1. Take every delivery branch deliver/<G>/<module> that needs no reader (tools/review_class.py: AUTO, including
     `compiler-only`) and every delivery a reader passed (tools/merge_delivery.py <G> <module> --stage 3 ... records the
     pass in local/batch/passed/; this tool lands it).
  2. Without any lock, several deliveries at once: the static checks a-e of tools/stage3_delivery.py, the class again
     for reviewer AUTO, the base's age, the commit of the delivery tool (`Prove <module> (<G>)`: the tool pushes only
     what it compiled), every delivered file unchanged in the library since the delivery's base, and
     tools/import_prune_check.py for every module against the library with the delivery's files in place.
     A delivery the checks refuse goes back to its group with the message (coord/returns/<G>.md).
  3. Two deliveries that write the same file do not land in one batch: the later one waits for the next cycle.
  4. Under coord/.merge.lock, held only for the writes: for each delivery, the head and the library files are compared
     with what was checked (a difference: the delivery waits and is checked again), then the files are written and
     registered as one landing (tools/landing.py; several modules are one set), the node records, change records,
     report, claim, ledger line are written as tools/merge_delivery.py --stage 3 wrote them, and one commit
     `Prove <module> (<G>, reviewed by <ID>)` is made. The queue is rewritten once.
  5. The global build (tools/build.py) verifies the whole batch. For the landings of a batch it also enforces what the
     compile of each delivery enforced before: no file slower than SHEAF_FILE_TIMEOUT, no axiom beyond the three, no
     `sorry` the text check did not see (one probe over the compiled modules of the batch).
  6. Green: the batch is verified. Red: `triage` maps every failure to the deliveries of the batch that wrote the
     failing module or changed a module it imports. A failure with one possible cause is decided here; more than three suspects go to
     an independent Codex agent on the groups' machine (local/batch/triage/<batch>-r<n>/request.md -> verdict.json),
     which says for each failure whether the delivered module is wrong, or correct and broken by another delivery of
     the batch. The deliveries at fault are taken out (tools/landing.py revert, their records put back) and returned
     with the compiler's message and the reason; the build runs again. Suspects and their batch dependents are removed together, then survivors are rebuilt, at most four rounds.
     No suspects or the round limit: ALERT and defer the failing import closures; never bisect.
     Repeated red source trees are never compiled again; unresolved states write ~/cc1/ALERT.

Usage (maintainer; SHEAF_LEAD=L-only):
  tools/batch_land.py step                      one step of the cycle (~/cc1/autoland3.py calls this in a loop)
  tools/batch_land.py status                    the open batch, the passed deliveries waiting
  tools/batch_land.py pass <G> <module> --head SHA --reviewer ID [--spot-checked NOTE] [--verdict PASS|FIX]
                                                record a reader's pass (what merge_delivery.py --stage 3 does)
  tools/batch_land.py take-out <G> <module> REASON   take a landed delivery of the open batch out and return it
"""
from __future__ import annotations
import calendar, json, os, pathlib, pickle, re, subprocess, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import merge_delivery as md  # noqa: E402
import leanindex as li  # noqa: E402
import landing as ld  # noqa: E402
import stage2_delivery as s2  # noqa: E402
import stage3_delivery as s3  # noqa: E402
import review_class as rc  # noqa: E402
import sorry_ledger as sl  # noqa: E402
import batch_recovery as recovery
import import_cycles as cycles
import repair_queue as repairs
from pipeline_guard import alert, clear_alert

ROOT = md.ROOT
BD = ROOT / "local" / "batch"
PASSED, OPEN, CLOSED, TRIAGE = BD / "passed", BD / "open.json", BD / "closed", BD / "triage"
CLONE = ld.LOCAL / "buildtree"
STOP_REQUESTED = lambda: False


def stop_checkpoint():
    if STOP_REQUESTED(): raise Wait("stop requested between operations")


ROUNDS = 4
POOL = int(os.environ.get("SHEAF_BATCH_POOL", "4"))
TRIAGE_WAIT = float(os.environ.get("SHEAF_TRIAGE_WAIT", "1500"))     # seconds for the Codex agent's verdict
NOTE_AUTO = ("AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the "
             "group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by "
             "a reviewer (stage 3, decision of the human 2026-10-12)")


class Refuse(Exception):
    """The delivery goes back to its group with this message."""


class Wait(Exception):
    """The delivery stays for a later cycle."""


def key(e) -> str:
    return f"{e['group']}/{e['item']}"


def read_json(p):
    try:
        return json.loads(pathlib.Path(p).read_text())
    except (OSError, ValueError):
        return None


def write_json(p, d):
    p = pathlib.Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + ".tmp"); tmp.write_text(json.dumps(d, ensure_ascii=False, indent=1)); os.replace(tmp, p)


def marker(g, item) -> pathlib.Path:
    return PASSED / f"{g}__{item}.json"


# ---------------------------------------------------------------- a reader's pass

def cmd_pass(o) -> int:
    """tools/merge_delivery.py <G> <module> --stage 3: the static checks now, the landing by the next batch."""
    g, item = o.group, o.item
    br = md.branch_of(g, item)
    if not o.head:
        raise md.Fail("--stage 3 needs --head SHA (the commit the reviewer read)")
    if not md.has_ref(f"refs/heads/{br}"):
        raise md.Fail(f"no branch {br}")
    head = md.git("rev-parse", br)
    if not head.startswith(o.head):
        raise md.Fail(f"the branch head is {head[:9]}, not {o.head}: review the new head")
    over = {}
    if o.apply_fixes:
        over = fixes(pathlib.Path(o.apply_fixes).resolve(), g, item, head)
    c = {"group": g, "item": item, "head": head, "reviewer": o.reviewer, "overrides": over}
    try:
        plan = check(c, classify=False)
    except (Refuse, Wait) as e:
        raise md.Fail(str(e))
    if o.dry_run:
        print(f"DRY RUN {item} (stage 3): the static checks pass; {len(plan['D']['modules'])} module(s); nothing changed")
        return 0
    verdict = (o.verdict or ("FIX" if over else "PASS")).upper()
    write_json(marker(g, item), {"group": g, "item": item, "head": head, "reviewer": o.reviewer, "verdict": verdict,
                                 "note": o.spot_checked, "overrides": over, "time": ld.now()})
    print(f"QUEUED {item} {head[:9]}: passed by {o.reviewer}; the next batch lands it (tools/batch_land.py)")
    return 0


def fixes(fixdir: pathlib.Path, g, item, head) -> dict:
    base = md.git("merge-base", md.MAIN, head)
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item)
    by = {pathlib.PurePosixPath(m["file"]).name: m["file"] for m in D["modules"]}
    by.update({f"{n}.json": x["path"] for n, x in D["nodes"].items()})
    by.update({pathlib.PurePosixPath(p).stem + ".change.md": p for p in D["changes"]})
    by[f"{item}.report.md"] = D["report_path"]
    over = {}
    for fp in sorted(fixdir.iterdir()):
        if fp.name not in by:
            raise md.Fail(f"--apply-fixes: {fp.name} is not a file of the delivery")
        over[by[fp.name]] = fp.read_text()
    return over


# ---------------------------------------------------------------- the checks, without a lock

def returned_head(g, head) -> bool:
    p = ROOT / "coord" / "returns" / f"{g}.md"
    try:
        return head[:9] in p.read_text()
    except OSError:
        return False


def candidates(cache: dict) -> list[dict]:
    """The deliveries a batch may take: passed by a reader (marker with the branch's head), or of class AUTO."""
    out = []
    live = set()
    for g, item in rc.branches():
        if not s3.is_stage3_item(item):
            continue
        head = rc.git("rev-parse", f"deliver/{g}/{item}").strip()
        if not head:
            continue
        live.add(marker(g, item).name)
        try:
            if json.loads((ROOT / "coord" / "claims" / f"{item}.lock").read_text()).get("who") != g:
                continue
        except (OSError, ValueError):
            continue
        if g.startswith('XR'):
            job = repairs.read(repairs.JOBS / (g[2:] + '.json'))
            if job.get('state') != 'delivered' or job.get('repaired_head') != head:
                continue  # dedicated reader/result has not accepted this exact repair
        if returned_head(g, head):
            continue        # this head was returned; the group pushes a new one
        mk = read_json(marker(g, item))
        if mk and mk.get("head") == head:
            if mk.get("not_before", 0) > time.time(): continue
            out.append({"group": g, "item": item, "head": head, "reviewer": mk["reviewer"], "note": mk.get("note"),
                        "verdict": mk.get("verdict") or "PASS", "overrides": mk.get("overrides") or {}, "passed": True})
            continue
        if mk:
            marker(g, item).unlink(missing_ok=True)     # the branch moved after the pass: the new head is classified
        if cache.get(head, "AUTO") != "AUTO":
            continue
        out.append({"group": g, "item": item, "head": head, "reviewer": None, "note": NOTE_AUTO, "verdict": "PASS",
                    "overrides": {}, "passed": False})
    if PASSED.is_dir():
        for p in PASSED.glob("*.json"):
            if p.name not in live:
                p.unlink(missing_ok=True)               # the branch is gone
    out.sort(key=lambda c: (not bool((read_json(marker(c["group"], c["item"])) or {}).get("repair_priority")), c["group"], c["item"]))
    return out


def inflight_files() -> set[str]:
    return {"lean/" + f["path"] for r in ld.records(ld.INFLIGHT) for f in r["files"]}


def prune_check(D: dict) -> str | None:
    """tools/import_prune_check.py for every module, against the library with the delivery's files in place (what
    land.sh and land_set.sh check after writing). None, or the findings."""
    if os.environ.get("SHEAF_SKIP_PRUNE") == "1":
        # the human, 2026-10-13 17:55 +08: land the waiting deliveries at once and let the global build judge;
        # what breaks it is taken out and repaired (repair_queue) - faster than a per-delivery library scan
        return None
    with tempfile.TemporaryDirectory(prefix="sheaf-batch-") as td:
        td = pathlib.Path(td); ov = td / "lean"; ov.mkdir()
        src = [str(li.LEAN / d) for d in li.library_dirs() if (li.LEAN / d).is_dir()] + [str(p) for p in li.LEAN.glob("*.lean")]
        subprocess.run(["cp", "-as", *src, str(ov)], check=True, capture_output=True)
        for m in D["modules"]:
            p = ov / m["file"][len("lean/"):]
            p.parent.mkdir(parents=True, exist_ok=True)
            if p.is_symlink() or p.exists():
                p.unlink()
            p.write_text(m["text"])
        code = ("import sys, pathlib; sys.path.insert(0, sys.argv[1]); import leanindex as li; "
                "li.LEAN = pathlib.Path(sys.argv[2]); import import_prune_check as c; "
                "sys.argv = ['import_prune_check.py'] + sys.argv[3:]; sys.exit(c.main())")
        for m in D["modules"]:
            old = td / "old.lean"
            if m["old"] is None:
                oldp = "/dev/null"
            else:
                old.write_text(m["old"]); oldp = str(old)
            r = subprocess.run([sys.executable, "-c", code, str(ROOT / "tools"), str(ov), m["module"], oldp,
                                str(ov / m["file"][len("lean/"):])], cwd=ROOT, capture_output=True, text=True)
            if r.returncode != 0:
                return f"refused by tools/import_prune_check.py for {m['file']}: " + " | ".join(
                    (r.stdout + r.stderr).strip().splitlines()[-25:])
    return None


IMPORT_LINE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")


def imports_added(old: str | None, now: str | None) -> list[str] | None:
    """The import lines `now` has and `old` lacks, when that is their only difference; None otherwise."""
    if old is None or now is None or old == now:
        return None
    ol = old.split("\n")
    have = {l.strip() for l in ol}
    added, rest = [], []
    for l in now.split("\n"):
        (added if IMPORT_LINE.match(l) and l.strip() not in have else rest).append(l)
    return added if added and rest == ol else None


def merge_imports(text: str, added: list[str]) -> str:
    """`text` with the import lines `added` that it lacks, after its last import (after `module` if it has none)."""
    L = text.split("\n")
    mods = {IMPORT_LINE.match(l).group(1) for l in L if IMPORT_LINE.match(l)}
    add = [l for l in added if IMPORT_LINE.match(l).group(1) not in mods]
    ks = [i for i, l in enumerate(L) if IMPORT_LINE.match(l)] or [i for i, l in enumerate(L) if l.strip() == "module"]
    k = ks[-1] + 1 if ks else 0
    return "\n".join(L[:k] + add + L[k:])


def check(c: dict, classify: bool = True) -> dict:
    """Every check that needs no lock. Returns the plan of the landing; Refuse or Wait otherwise."""
    g, item, head = c["group"], c["item"], c["head"]
    reviewer = c.get("reviewer")
    base = md.git("merge-base", md.MAIN, head)
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item, overrides=c.get("overrides") or None)
    if classify and not c.get("passed"):
        cl, why, h = rc.classify(g, item, D)
        if h != head:
            raise Wait("the branch moved during the checks")
        if cl != "AUTO":
            raise Wait(f"class {cl}: {why[:200]}")       # a reader's; not this tool's
        reviewer = "COMPILER" if why.startswith("compiler-only") else "AUTO"
    if time.time() - int(md.git("show", "-s", "--format=%ct", base)) > md.MAX_AGE:
        raise Refuse(f"base {base[:7]} is too far behind {md.MAIN}: pull, rebase, push again")
    if D["fails"]:
        raise Refuse("; ".join(f"({L}) {x}" for L, x in D["fails"][:6]))
    # stage3_delivery already refuses ordinary definition holes and new forbidden
    # keyword kinds. Supplement only its admit, quoted-name and data-field gaps.
    for module in D["modules"]:
        missing = sl.missing_gate(module["old"], module["text"])
        if missing:
            raise Refuse(module["file"] + ": " + "; ".join(missing[:6]))
    why3 = s3.classify(D, g, item)
    if reviewer == "AUTO" and why3:
        raise Refuse("not AUTO: " + "; ".join(why3))
    subject = md.git("show", "-s", "--format=%s", head)
    if subject != f"Prove {item} ({g})":
        raise Refuse(f"the commit of the delivery is `{subject[:80]}`, not `Prove {item} ({g})`: nothing shows that the "
                     "group's delivery tool compiled its modules with the probe, and the server does not compile a "
                     "delivery again; deliver with the delivery tool")
    busy = inflight_files()
    cur, write = {}, []
    for m in D["modules"]:
        p = ROOT / m["file"]
        now = p.read_text() if p.is_file() else None
        cur[m["file"]] = now
        if now == m["text"]:
            continue
        if m["file"] in busy:
            raise Wait(f"{m['file']} is in a landing that is still being checked")
        added = imports_added(m["old"], now)
        if added is not None:
            # the library's file differs from the delivery's base only by added import lines (the proof imports written
            # into the modules on 2026-10-12, tools/add_proof_imports.py): the delivery keeps its content and gets them
            m["text"], m["old"] = merge_imports(m["text"], added), now
            D["notes"].append(f"{m['file']}: {len(added)} import line(s) added on {md.MAIN} since the base were merged in")
            if now == m["text"]:
                continue
        elif now != m["old"]:
            raise Refuse(f"{m['file']} changed on {md.MAIN} after the delivery's base {base[:9]} (another landing wrote "
                         "it): take the file as it is now, make your change in it, compile and deliver again")
        write.append(m["file"])
    if not write:
        raise Refuse("every module of the delivery is in the library already, with the same text")
    if reviewer == "AUTO":
        m0 = D["modules"][0]
        ch = li.interface_changes(m0["old"] or "", m0["text"] or "") if m0["old"] else ["(new module)"]
        if len(D["modules"]) > 1 or (ch and not set(ch) <= {"(imports removed)"}):
            raise Refuse("the landing would be of kind interface, not proof: the delivery is CODEX")
    graph_file = c.get("_import_graph_file")
    if graph_file:
        with open(graph_file, "rb") as f:
            import_graph = pickle.load(f)
    else:
        import_graph = cycles.graph(li.LEAN)
    texts = {m["module"]: m["text"] for m in D["modules"]}
    try:
        cycles.refuse_missing(texts, cycles.source_modules(ROOT, pathlib.Path(graph_file).name.split("-imports")[0] if graph_file else "HEAD"), cycles.source_roots(ROOT))
    except RuntimeError as exc:
        raise Refuse(str(exc)) from exc
    cycle = cycles.closing_cycle(import_graph, texts)
    if cycle: raise Refuse("import cycle: " + " -> ".join(cycle))
    bad = prune_check(D)
    if bad:
        raise Refuse(bad)
    paths = {m["file"] for m in D["modules"]} | {x["path"] for x in D["nodes"].values()} | set(D["changes"]) | {D["report_path"]}
    return dict(c, reviewer=reviewer, base=base, D=D, cur=cur, write=write, paths=sorted(paths))


def _check(c):
    try:
        return "ok", check(c)
    except Refuse as e:
        return "refuse", str(e)
    except Wait as e:
        return "wait", str(e)
    except Exception as e:  # noqa: BLE001   a delivery the tools cannot read stays for a reader
        return "error", repr(e)[:300]


class Pre:
    """The checks, POOL deliveries at a time, each in a process of its own (tools/queue.py hides the standard module
    `queue`, so neither multiprocessing nor concurrent.futures can be imported from tools/). The loop calls pump()
    while a batch waits for its build, so the next batch is checked by the time it may land; a result is kept by the
    head it was computed for, and the landing compares the head and the library files with it again under the lock."""

    def __init__(self):
        self.dir = pathlib.Path(tempfile.mkdtemp(prefix="sheaf-batch-"))
        self.running, self.done = {}, {}
        self.import_graph, self.graph_tip, self.graph_file = None, None, None

    def snapshot(self):
        """One graph scan, then update only modules changed at an external tip."""
        tip = md.git('rev-parse', 'HEAD')
        if self.import_graph is None:
            self.import_graph = cycles.graph(li.LEAN)
        elif tip != self.graph_tip:
            paths = md.git('diff', '--name-only', self.graph_tip, tip, '--', 'lean/').splitlines()
            texts = {}
            for path in paths:
                if path.endswith('.lean'):
                    data = recovery.blob(ROOT, tip, path)
                    texts[path[5:-5].replace('/', '.')] = data.decode() if data is not None else None
            self.import_graph = cycles.overlay(self.import_graph, texts)
        if tip != self.graph_tip or self.graph_file is None:
            self.graph_file = self.dir / (tip + '-imports.pkl')
            with self.graph_file.open('wb') as f: pickle.dump(self.import_graph, f, protocol=pickle.HIGHEST_PROTOCOL)
            self.graph_tip = tip
        return self.import_graph

    def pump(self, cands: list[dict]) -> None:
        for h, (p, out) in list(self.running.items()):
            if p.poll() is None:
                continue
            del self.running[h]
            try:
                self.done[h] = pickle.loads(out.read_bytes())
            except Exception:  # noqa: BLE001
                self.done[h] = ("error", f"the check process ended with exit code {p.returncode}")
            out.unlink(missing_ok=True)
        if cands:
            self.snapshot()
            for c in cands: c['_import_graph_file'] = str(self.graph_file)
        live = {c["head"] for c in cands}
        for h in [h for h in self.done if h not in live]:
            del self.done[h]
        for c in cands:
            h = c["head"]
            if len(self.running) >= POOL:
                break
            if h in self.done or h in self.running:
                continue
            out = self.dir / f"{h}.pkl"
            p = subprocess.Popen([sys.executable, str(pathlib.Path(__file__).resolve()), "check-one", str(out)], cwd=ROOT,
                                 stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            p.stdin.write(json.dumps(c).encode()); p.stdin.close()
            self.running[h] = (p, out)

    def results(self, cands: list[dict]) -> list[tuple]:
        while True:
            stop_checkpoint()
            self.pump(cands)
            if all(c["head"] in self.done for c in cands):
                return [self.done[c["head"]] for c in cands]
            time.sleep(0.2)


# ---------------------------------------------------------------- the landing, under the lock

def land_one(plan: dict, batch_id: str) -> dict:
    """Write, register and commit one delivery. Called with coord/.merge.lock held."""
    if (BD / 'proof-imports.json').exists(): raise Wait('proof-import cycle is committing')
    g, item, head, D, reviewer = plan["group"], plan["item"], plan["head"], plan["D"], plan["reviewer"]
    br = md.branch_of(g, item)
    if not md.has_ref(f"refs/heads/{br}") or md.git("rev-parse", br) != head:
        raise Wait("the branch moved after the checks")
    for m in D["modules"]:
        p = ROOT / m["file"]
        if (p.read_text() if p.is_file() else None) != plan["cur"][m["file"]]:
            raise Wait(f"{m['file']} changed in the library after the checks")
    for nid, x in D["nodes"].items():
        if x["role"] == "new" and (ROOT / x["path"]).exists():
            raise Refuse(f"the new node {nid} exists on {md.MAIN} now (another delivery created it)")
    if plan.get("cycle_tip") and md.git("rev-parse", "HEAD") != plan["cycle_tip"]:
        raise Wait("the library moved after the import-cycle check; retry on the new tip")
    mods = D["modules"]
    rels = [f[len("lean/"):] for f in plan["write"]]
    is_set = len(mods) > 1
    r = subprocess.run([sys.executable, "tools/landing.py", "begin", "L", *rels], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise Wait("landing.py begin: " + (r.stderr or r.stdout).strip()[:300])
    landing = r.stdout.strip().splitlines()[-1]
    tree, book, done = md.Tree(), {"group": g, "item": item}, False
    try:
        for m in mods:
            if m["file"] in plan["write"]:
                p = ROOT / m["file"]; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(m["text"])
        r = subprocess.run([sys.executable, "tools/landing.py", "finish", landing] + (["--set"] if is_set else []),
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            raise md.Fail("landing.py finish: " + (r.stderr or r.stdout).strip()[:300])
        done = True
        kind = r.stdout.strip().splitlines()[-1]
        req = ld.REQUESTS / f"{landing}.json"
        rec = ld.read_json(req) or {}
        if reviewer == "AUTO" and kind != "proof" and set(rec.get("changed") or ["?"]) <= {"(imports removed)"}:
            kind = "proof"      # a removed public import in a module nobody imports: the one interface landing of AUTO
        allowed = {m["module"]: sorted(set(m["diff"]["sorry_before"]) - set(m["diff"]["body_changed"]) | set(m["diff"]["new_sorry"]))
                   for m in mods}
        rec.update(batch=batch_id, delivery={"group": g, "item": item, "head": head}, sorry_allowed=allowed)
        ld.write_json(req, rec)
        rv = {"date": md.today(), "by": "L", "reviewer": reviewer, "group": g, "result": plan["verdict"].lower(),
              "landing": landing, "kind": kind}
        if plan.get("note"):
            rv["note"] = plan["note"]
        paths = []
        for nid, x in D["nodes"].items():
            if x["role"] == "new":
                nd = dict(x["node"])
                nd["reviewed"] = dict(rv, note="new node of a stage-3 delivery, read against its source by the reviewer")
            else:
                nd = json.loads((ROOT / x["path"]).read_text())
                for k in s3.STAGE3_OWNS + s3.STAGE3_STATEMENT:   # only what the delivery changed against its base
                    if (x["base_node"] or {}).get(k) == x["node"].get(k):
                        continue
                    if k in x["node"]:
                        nd[k] = x["node"][k]
                    else:
                        nd.pop(k, None)
            nd["reviewed_proof"] = rv
            tree.write(x["path"], md.dump(nd)); paths.append(x["path"])
        for p in plan["item_nodes"]:                             # the node(s) of the item's module
            if p in paths:
                continue
            nd = json.loads((ROOT / p).read_text())
            m0 = next(m for m in mods if m["role"] == "item")
            nd["reviewed_proof"] = dict(rv, sorry_before=m0["diff"]["sorry_before"], sorry_after=m0["diff"]["sorry_after"])
            tree.write(p, md.dump(nd)); paths.append(p)
        for p, t in D["changes"].items():
            t2 = re.sub(r"(?m)^(## Status\n+)open\b.*$", f"\\1landed {landing} {md.today()} (merge of {br})", t)
            tree.write(p, t2); paths.append(p)
        tree.write(D["report_path"], D["report"]); paths.append(D["report_path"])
        rp, rtext, parts = md.return_entries(g, item)
        keep = [x for x in parts if not x.startswith(f"## {item} (")]
        returned = rtext is not None and len(keep) != len(parts)
        book["returns"] = (rp, rtext)
        if returned:
            rp.write_text("".join(keep)); paths.append(rp.relative_to(ROOT).as_posix())
        claim = ROOT / "coord" / "claims" / (item.replace("/", "__") + ".lock")
        claim_text = claim.read_text() if claim.exists() else None
        book["claim"] = (claim, claim_text)
        dlog = ROOT / "coord" / "deliveries.log"
        book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
        subprocess.run([sys.executable, "tools/claim.py", "done", g, item,
                        f"delivered by {g} on {br}, merged by L (reviewer {reviewer})"], cwd=ROOT, capture_output=True)
        book["ledger"] = md.ledger_line(
            f"merged {br} (stage 3; reviewer {plan['verdict']}; {'after a return' if returned else 'first push'}; "
            f"landing {landing} ({kind}); batch {batch_id}; modules {len(mods)}; new nodes "
            f"{sum(1 for x in D['nodes'].values() if x['role'] == 'new')}"
            + (f"; change records: {', '.join(D['changes'])}" if D["changes"] else "") + ")")
        paths += [m["file"] for m in mods] + ["coord/ledger.md", "coord/deliveries.log"]
        if claim_text is not None and md.exists_at("HEAD", claim.relative_to(ROOT).as_posix()):
            paths.append(claim.relative_to(ROOT).as_posix())
        author = md.git("show", "-s", "--format=%an <%ae>", D["commits"][-1]) if D["commits"] else "L"
        md.git_retry("add", "-A", "--", *paths)
        md.git_retry("commit", "-q", f"--author={author}", "-m",
                     f"Prove {item} ({g}, reviewed by {reviewer})\n\nDelivered by group {g} ({br}); landing "
                     f"{landing} ({kind}); batch {batch_id}, which the global build verifies; merged by "
                     "tools/batch_land.py for L.", "--", *paths)
    except BaseException:
        tree.restore(); md.unbook(book)
        subprocess.run([sys.executable, "tools/landing.py", "revert" if done else "abort", landing]
                       + (["the batch landing did not commit"] if done else []), cwd=ROOT, capture_output=True)
        raise
    sha = md.git("rev-parse", "HEAD")
    md.git("branch", "-D", br, check=False)
    marker(g, item).unlink(missing_ok=True)
    if g.startswith('XR'):
        jp = repairs.JOBS / (g[2:] + '.json'); job = repairs.read(jp)
        if job:
            job['repair_landing'] = landing; repairs.write(jp, job)
    return {"group": g, "item": item, "head": head, "reviewer": reviewer, "landing": landing, "kind": kind,
            "commit": sha, "overrides": plan.get("overrides", {}), "modules": [m["module"] for m in mods], "claim": claim_text, "state": "landed"}


def land_batch(cache: dict, log) -> dict | None:
    """Steps 1-4. Returns the batch (also written to local/batch/open.json), or None when nothing landed."""
    if (BD / 'proof-imports.json').exists(): return None
    cands = candidates(cache)
    if not cands:
        return None
    t0 = time.time()
    pre = cache.setdefault("_pre", Pre())
    # The source tree is fixed for this batch's checks. Scanning all library
    # files in every check worker costs about 16 seconds per delivery. Share
    # one snapshot with the workers; the in-process graph below is overlaid as
    # each delivery is accepted.
    import_graph = pre.snapshot()
    for c in cands: c['_import_graph_file'] = str(pre.graph_file)
    res = pre.results(cands)
    pre.snapshot()
    base_modules = cycles.source_modules(ROOT, pre.graph_tip)
    package_roots = cycles.source_roots(li.LEAN)
    plans, taken = [], {}
    for c, (st, x) in zip(cands, res):
        g, item, head = c["group"], c["item"], c["head"]
        if st == "ok":
            x = dict(x)
            clash = [p for p in x["paths"] if p in taken]
            if clash:
                log("waits for the next batch", g, item, head[:9], "|", f"{clash[0]} is written by {taken[clash[0]]} in this batch")
                continue
            texts = {m["module"]: m["text"] for m in x["D"]["modules"]}
            try:
                cycles.refuse_missing(texts, base_modules, package_roots)
            except RuntimeError as exc:
                pre.done.pop(head, None)
                give_back(g, item, head, str(exc), log)
                continue
            cycle = cycles.closing_cycle(import_graph, texts)
            if cycle:
                log("waits for the next batch", g, item, head[:9], "| import cycle:", " -> ".join(cycle))
                pre.done.pop(head, None)
                continue
            import_graph = cycles.overlay(import_graph, texts)
            for p in x["paths"]:
                taken[p] = key(c)
            plans.append(x)
        elif st == "refuse":
            pre.done.pop(head, None)
            give_back(g, item, head, x, log)
        elif st == "wait":
            pre.done.pop(head, None)
            if x.startswith("class "):
                cache[head] = "READER"
            else:
                log("not in this batch", g, item, head[:9], "|", x[:300])
        else:
            pre.done.pop(head, None)
            cache[head] = "ERROR"
            log("check error, left for a reader", g, item, head[:9], "|", x)
    if not plans:
        return None
    t1 = time.time()
    if md.git("symbolic-ref", "-q", "--short", "HEAD", check=False) != md.MAIN:
        raise md.Fail(f"the working tree is not on {md.MAIN}")
    batch_id = time.strftime("%Y%m%dT%H%M%S", time.gmtime())
    entries, back, held = [], [], 0.0
    landing_marker = BD / 'landing.json'
    write_json(landing_marker, {'id': batch_id, 'started': ld.now()})
    tl = time.time()
    by_module = {}
    for nid, d in s2.nodes_at(s2.Git(ROOT), md.MAIN).items():
        l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
        if l.get("module"):
            by_module.setdefault(l["module"], []).append(nid)
    import_graph = pre.snapshot()
    expected_tip = pre.graph_tip
    base_modules = cycles.source_modules(ROOT, expected_tip)
    for plan in plans:
        g, item, head = plan["group"], plan["item"], plan["head"]
        pre.done.pop(head, None)     # landed, or checked again
        ids = [n for n in by_module.get(item, []) if n not in plan["D"]["nodes"]]
        plan["item_nodes"] = [p for p in (md.node_path(n) for n in ids) if p]
        try:
            # The graph is updated after each accepted delivery. The tip
            # records the previous delivery in this batch, so those known
            # commits do not invalidate the cycle check.
            current_tip = md.git('rev-parse', 'HEAD')
            if current_tip != expected_tip:
                # External source edits are overlaid outside the write lock.
                pre.import_graph, pre.graph_tip = import_graph, expected_tip
                import_graph = pre.snapshot(); expected_tip = pre.graph_tip
            try:
                cycles.refuse_missing({m["module"]: m["text"] for m in plan["D"]["modules"]}, base_modules, package_roots)
            except RuntimeError as exc:
                raise Refuse(str(exc)) from exc
            plan["cycle_tip"] = expected_tip
            cycle = cycles.closing_cycle(import_graph, {m["module"]: m["text"] for m in plan["D"]["modules"]})
            if cycle: raise Wait("import cycle: " + " -> ".join(cycle))
            lock_started = time.time()
            with md.merge_lock():
                e = land_one(plan, batch_id)
            held += time.time() - lock_started
            write_json(landing_marker, {"id": batch_id, "started": ld.now(), "entries": entries + [e]})
        except Wait as w:
            log("not in this batch", g, item, head[:9], "|", str(w)[:300]); continue
        except Refuse as f:
            back.append((g, item, head, str(f))); continue
        except md.Fail as f:
            log("landing failed, nothing changed; tried again in the next cycle", g, item, head[:9], "|", str(f)[:300]); continue
        entries.append(e)
        import_graph = cycles.overlay(import_graph,
                                      {m["module"]: m["text"] for m in plan["D"]["modules"]})
        expected_tip = e["commit"]
        pre.import_graph, pre.graph_tip = import_graph, expected_tip
        pre.graph_file = None
        log("landed", g, item, head[:9], "stage 3", f"batch {batch_id} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
    if entries:
        refresh_recovery_queue()
    for g, item, head, why in back:
        give_back(g, item, head, why, log)
    if not entries:
        landing_marker.unlink(missing_ok=True)
        return None
    b = {"id": batch_id, "time": ld.now(), "round": 0, "handled": [], "entries": entries,
         "check_seconds": round(t1 - t0, 1), "lock_seconds": round(held, 1)}
    write_json(OPEN, b)
    landing_marker.unlink(missing_ok=True)
    log(f"batch {batch_id}: {len(entries)} landed (checks {b['check_seconds']} s without a lock, lock held "
        f"{b['lock_seconds']} s); the global build verifies it")
    return b


def give_back(g, item, head, why, log):
    """A delivery the tools refuse goes back to its group with their message (the human, 2026-10-12)."""
    try:
        md.cmd_return(g, item, f"(the landing tools, head {head[:9]}) the delivery did not land: {why[:3000]}")
        log("RETURNED by the tools", g, item, head[:9], "|", " ".join(why.split())[:300])
    except Exception as e:  # noqa: BLE001
        if "merge.lock held" in str(e):
            log("lock busy, will retry", g, item, head[:9])
        else:
            log("RETURN FAILED", g, item, head[:9], "|", repr(e)[:200], "|", " ".join(why.split())[:200])


# ---------------------------------------------------------------- taking a landed delivery out

def undo_entries(entries, message, *, returned=False, repair_jobs=None):
    """Retry a stale preparation immediately, without another build or triage round."""
    for attempt in range(20):
        try:
            return _undo_entries(entries, message, returned=returned, repair_jobs=repair_jobs)
        except recovery.TipMoved:
            if attempt == 19: raise


def _undo_entries(entries, message, *, returned=False, repair_jobs=None):
    """Prepare outside locks; restore delivery records and sources in a single commit.

    See batch_recovery's docstring for the records derived from land_one and
    merge_delivery. Substantive later edits request whole-batch withdrawal.
    """
    if not entries: return
    tip = md.git("rev-parse", "HEAD")
    prepared = recovery.inverse(ROOT, [e["commit"] for e in entries], imports_only=bool(returned))
    # Audits/proved flags computed after landing describe the removed source.
    # Restore those fields from the pre-landing node; keep independent metadata.
    for e in entries:
        for path in recovery.git(ROOT, 'diff-tree', '--no-commit-id', '--name-only', '-r', e['commit']).decode().splitlines():
            if not path.startswith('dag/nodes/') or path not in prepared or prepared[path] is None: continue
            old = recovery.blob(ROOT, e['commit'] + '^', path)
            if old is None: continue
            a, cur = json.loads(old), json.loads(prepared[path])
            for field in ('lean_audit', 'proved', 'proved_proof'):
                if field in a: cur[field] = a[field]
                else: cur.pop(field, None)
            prepared[path] = (json.dumps(cur, ensure_ascii=False, indent=2) + '\n').encode()
    recs = []
    for e in entries:
        rid = e["landing"]
        r = ld.read_json(ld.REQUESTS / f"{rid}.json") or ld.read_json(ld.DONE / f"{rid}.json")
        if r:
            r = dict(r)
            r.update(result="reverted" if returned else "withdrawn", reason=message, closed=ld.now())
            r["sorry_allowed"] = {}
            for f in r['files']:
                path = 'lean/' + f['path']
                data = prepared.get(path)
                if path not in prepared:
                    p = ROOT / path; data = p.read_bytes() if p.is_file() else None
                r['sorry_allowed'][f['module']] = sorted(k for k, d in s3.decl_table((data or b'').decode()).items() if d['sorry'])
                f['sha'] = __import__('hashlib').sha256(data).hexdigest() if data is not None else None
            recs.append(r)
        claim = 'coord/claims/' + e['item'].replace('/', '__') + '.lock'
        if e.get('claim'):
            p = ROOT / claim
            if not p.exists(): prepared[claim] = e['claim'].encode()
        entry_returned = returned is True or isinstance(returned, dict) and key(e) in returned
        entry_message = returned.get(key(e), message) if isinstance(returned, dict) else message
        if recs and recs[-1]["id"] == rid:
            recs[-1]["result"] = "reverted" if entry_returned else "withdrawn"
            recs[-1]["reason"] = entry_message
        if entry_returned:
            p, before, parts = md.return_entries(e['group'], e['item'])
            if p.relative_to(ROOT).as_posix() in prepared:
                parts = re.split(r'(?=^## )', prepared[p.relative_to(ROOT).as_posix()].decode(), flags=re.M)
            kept = ''.join(x for x in parts if not x.startswith(f"## {e['item']} ("))
            prepared[p.relative_to(ROOT).as_posix()] = (kept.rstrip() + f"\n\n## {e['item']} ({ld.now()}, head {e['head'][:9]})\n\n{entry_message}\n").encode()
    # Reserve repairs atomically with take-out; local outbox requests become
    # runnable only when this dedicated claim appears. No original-group return.
    for e in entries:
        job = (repair_jobs or {}).get(key(e))
        if not job: continue
        cp = repairs.claim_path(e['item'])
        current = repairs.read(cp)
        if current and current.get('who') not in (e['group'], job['group']):
            raise recovery.Conflict('repair claim already held by ' + current['who'])
        prepared[cp.relative_to(ROOT).as_posix()] = json.dumps(dict(
            who=job['group'], t=time.time(), since=ld.now(), repair=job['id'])).encode()
        rp, before, parts = md.return_entries(e['group'], e['item'])
        rel = rp.relative_to(ROOT).as_posix()
        text = (prepared.get(rel) or (before or '').encode()).decode()
        prepared[rel] = ''.join(x for x in re.split(r'(?=^## )', text, flags=re.M)
                               if not x.startswith(f"## {e['item']} (")).encode()
    ledger = prepared.get('coord/ledger.md', (ROOT / 'coord/ledger.md').read_bytes()) or b''
    prepared['coord/ledger.md'] = ledger + f"\n- {time.strftime('%H:%M')} L: {message[:180]}\n".encode()
    with md.merge_lock():
        with ld.tree_lock():
            recovery.commit_inverse(ROOT, prepared, tip, 'Take out batch deliveries' if returned else 'Withdraw unverified batch')
            for r in recs:
                ld.write_json(ld.DONE / f"{r['id']}.json", r)
                (ld.REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
                ld.drop_mirror(r['group'], [f['path'] for f in r['files']])
    # Queue calculation is source-only and deliberately outside both write locks.
    refresh_recovery_queue()


def refresh_recovery_queue():
    r = subprocess.run([sys.executable, 'tools/queue.py', 'write'], cwd=ROOT, capture_output=True)
    if r.returncode:
        raise md.Fail('queue refresh after take-out failed: ' + r.stderr.decode(errors='replace')[-300:])
    paths = ['coord/queue.tsv', 'coord/queue.md', 'coord/blueprint-index.tsv']
    with md.merge_lock():
        if md.git('status', '--porcelain', '--', *paths):
            md.git_retry('add', '--', *paths)
            md.git_retry('commit', '-q', '-m', 'Queue after batch recovery' + recovery.TRAILER, '--', *paths)


def unland(e: dict, reason: str, ledger: str) -> None:
    undo_entries([e], reason, returned=True)


def withdraw(b, reason, log):
    """Last resort only: transactional restoration cannot remove a smaller set."""
    alert(b['id'], '?', reason, 'restore batch transaction; no bisection')
    active = [e for e in b['entries'] if e['state'] in ('landed', 'stuck')]
    undo_entries(active, f"batch {b['id']} withdrawn: {reason}")
    defer_entries(active)
    b.pop('triage', None)
    b['await_recovery'] = True
    write_json(OPEN, b)
    log(f"batch {b['id']} withdrawn transactionally; no halves; build restored tree")


def defer_entries(entries):
    for e in entries:
        br = md.branch_of(e['group'], e['item'])
        if not md.has_ref('refs/heads/' + br): md.git('branch', br, e['head'])
        e['state'] = 'waiting'
        write_json(marker(e['group'], e['item']), {**e, 'overrides': e.get('overrides', {}),
                   'verdict': 'PASS', 'time': ld.now()})


# ---------------------------------------------------------------- a red build

HEADER = re.compile(r"^[✔⚠✖ℹ] \[\d+/\d+\] \w+ (\S+)", re.M)


def log_blocks(text: str) -> dict[str, str]:
    """module -> what Lake printed for its failed job."""
    out = {}
    hs = list(HEADER.finditer(text))
    for k, h in enumerate(hs):
        if not h.group(0).startswith("✖"):
            continue
        end = hs[k + 1].start() if k + 1 < len(hs) else len(text)
        blk = text[h.start():end]
        cut = blk.find("\nSome required")
        blk = blk if cut < 0 else blk[:cut]
        out[h.group(1)] = "\n".join(l for l in blk.split("\n") if not l.startswith("trace: ")).strip()
    return out


def library_imports() -> dict:
    # Attribution must use the current batch tree, never a stale buildtree.
    return cycles.graph(li.LEAN)


def chain(src: str, dst: set, imports: dict) -> list[str]:
    """One import path from `src` to a module of `dst`."""
    prev, todo = {src: None}, [src]
    while todo:
        m = todo.pop(0)
        if m in dst and m != src:
            out = []
            while m is not None:
                out.append(m); m = prev[m]
            return out[::-1]
        for i in sorted(imports.get(m, ())):
            if i not in prev:
                prev[i] = m; todo.append(i)
    return []


def triage(b: dict, last: dict, imports=None) -> dict:
    """The mechanical part: {decisions: [{failure, case, return: [G/item], reason, message}], open: [{failure,
    suspects: [G/item], message, others}], unattributed: [module]}."""
    entries = [e for e in b['entries'] if e['state'] == 'landed']
    text = (ld.LOCAL / 'build.log').read_text(errors='ignore') if (ld.LOCAL / 'build.log').exists() else ''
    blocks = log_blocks(text)
    if imports is None: imports = library_imports()
    failures = list(dict.fromkeys(list(last.get('failing') or []) +
                                  [c['module'] for c in last.get('batch_checks') or []]))
    messages = {m: blocks.get(m) or '\n'.join(last.get('errors') or []) for m in failures}
    messages.update({c['module']: c['message'] for c in last.get('batch_checks') or []})
    deltas = {}
    def changes(e, m):
        stop_checkpoint()
        k = (e["commit"], m)
        if k in deltas: return deltas[k]
        path = s3.path_of_module(m)
        a, z = recovery.blob(ROOT, e['commit'] + '^', path), recovery.blob(ROOT, e['commit'], path)
        deltas[k] = recovery.interface_delta(a.decode() if a is not None else None,
                                               z.decode() if z is not None else None)
        return deltas[k]
    T = {'decisions': [], 'open': [], 'unattributed': [] if failures else ['?']}
    for o in recovery.select(entries, failures, imports, changes, messages, checkpoint=stop_checkpoint):
        suspects = [key(e) for e in o['suspects']]
        if not suspects:
            T['unattributed'].append(o['failure'])
        elif len(suspects) <= 3:
            T['decisions'].append({'failure': o['failure'], 'case': o['case'],
                'return': suspects, 'reason': '', 'message': o['message']})
        else:
            T['open'].append({'failure': o['failure'], 'writer': None, 'suspects': suspects,
                'message': o['message'], 'others': [],
                'chains': {key(e): chain(o['failure'], set(e['modules']), imports) for e in o['suspects']}})
    return T


PROMPT = """You are the triage agent of a red global build of the Lean project weil-conjectures-sheaf. You READ and DECIDE; you
change nothing: no file write outside this directory, no git command that changes anything. A script acts on your answer.

A batch of deliveries was written into the library together, and the build of the whole library failed. Each delivery
was compiled by its group against the library as it was BEFORE the batch. For each failure below, the tools could not
tell which delivery of the batch is at fault. Decide it from the compiler's message, the diffs and the imports.

For each failing module choose one case:
  "own-fault"         the failing module was delivered in this batch and its own delivered text is wrong (the error does
                      not come from another delivery's change). Return the delivery that wrote it.
  "breaker"           the failing module is correct against the library before the batch and fails because another
                      delivery of the batch changed something it uses, and that change is NOT one the rest of the
                      library has to follow (an accident: a renamed or removed declaration, a changed signature or
                      instance that the delivery did not have to change, a name it now declares twice). Return the
                      delivery that made the change.
  "dependent-adapts"  as "breaker", but the other delivery's change is a legitimate change of an interface (a corrected
                      statement or definition, with its change record) and stays; the failing module was delivered in
                      this batch and has to be adapted to it. Return the delivery that wrote the failing module, and say
                      in the reason exactly what it has to adapt to. If the failing module was NOT delivered in this
                      batch, this case is not available: the delivery that changed the interface did not adapt its
                      user and is returned ("breaker").
  "not-the-batch"     allowed ONLY when the failing module and all its imports are byte-identical to the last green commit, mechanically checked by the tools. Return nothing.
Return as few deliveries as make the build pass. Only suspects listed for a failure may be returned for it.

{failures}

The diffs of the suspect deliveries (the Lean files only):

{diffs}

Your answer ends with ONE line of JSON and nothing after it:
{{"decisions": [{{"failure": "<failing module>", "case": "own-fault" | "breaker" | "dependent-adapts" | "not-the-batch", "return": ["<G>/<module>", ...], "reason": "<two or three sentences for the group that gets the delivery back: what is wrong and what to change>"}}, ...]}}
One entry per failing module listed above."""


def write_request(b: dict, T: dict) -> pathlib.Path:
    d = TRIAGE / f"{b['id']}-r{b['round'] + 1}"
    d.mkdir(parents=True, exist_ok=True)
    ent = {key(e): e for e in b["entries"]}
    fl, sus = [], []
    for o in T["open"]:
        s = [f"## Failing module {o['failure']}"
             + (f" (delivered in this batch by {o['writer']})" if o["writer"] else " (not delivered in this batch)"),
             "Suspects: " + ", ".join(o["suspects"])]
        for k, ch in o["chains"].items():
            s.append(f"Imports reaching the modules of {k} ({', '.join(ent[k]['modules'])}): " + (" -> ".join(ch) or "(indirect)"))
        if o["others"]:
            s.append("Other landings in the same build that it also depends on (not of this batch, not yours to return): " + "; ".join(o["others"]))
        s.append("Compiler message:\n```\n" + o["message"][:8000] + "\n```")
        fl.append("\n".join(s))
        sus += [k for k in o["suspects"] if k not in sus]
    diffs = []
    for k in sus:
        e = ent[k]
        t = md.git("show", "--format=", e["commit"], "--", "lean/", check=False)
        diffs.append(f"### {k} (modules {', '.join(e['modules'])}; reviewer {e['reviewer']}; landing kind {e['kind']})\n```diff\n"
                     + t[:60000] + ("\n... (cut)" if len(t) > 60000 else "") + "\n```")
    (d / "meta.json").write_text(json.dumps({"batch": b["id"], "open": T["open"]}, ensure_ascii=False, indent=1))
    tmp = d / "request.tmp"
    tmp.write_text(PROMPT.format(failures="\n\n".join(fl), diffs="\n\n".join(diffs)))
    os.replace(tmp, d / "request.md")
    return d


def verdict_decisions(T: dict, v) -> list[dict]:
    """The agent's decisions, checked; a failure without a usable decision returns all its suspects."""
    got = {}
    for x in (v or {}).get("decisions") or [] if isinstance(v, dict) else []:
        if isinstance(x, dict) and isinstance(x.get("failure"), str):
            got[x["failure"]] = x
    out = []
    for o in T["open"]:
        x = got.get(o["failure"])
        ret = [k for k in (x or {}).get("return") or [] if k in o["suspects"]] if x else None
        case = (x or {}).get("case")
        if x and ret and case in ("own-fault", "breaker", "dependent-adapts") and not (case == "dependent-adapts" and ret != [o["writer"]]):
            out.append({"failure": o["failure"], "case": case, "return": ret, "reason": str(x.get("reason") or ""), "message": o["message"], "by": "codex"})
        else:
            out.append({"failure": o["failure"], "case": "undecided", "return": list(o["suspects"]),
                        "reason": "the triage gave no usable decision for this failure, so every delivery of the batch that may have caused it is returned",
                        "message": o["message"], "by": "fallback"})
    return out


def execute(b: dict, decisions: list[dict], log, deferred=(), imports=None) -> None:
    ent = {key(e): e for e in b["entries"]}
    per = {}
    for d in decisions:
        for k in d["return"]:
            per.setdefault(k, []).append(d)
        if not d["return"]:
            log(f"batch {b['id']} triage: {d['failure']} {d['case']} ({d.get('by', 'tools')}); nothing returned |", d.get("reason", "")[:200])
    active = [e for e in b['entries'] if e['state'] == 'landed']
    suspects = [e for e in active if key(e) in per]
    if imports is None: imports = library_imports()
    waiting = [e for e in active if set(e['modules']) & set(deferred) and e not in suspects]
    deps = waiting + recovery.dependents(active, suspects + waiting, imports)
    messages = {}
    for e in suspects:
        parts = []
        for d in per[key(e)]:
            modules = set(e['modules']) & (li.closure(d['failure'], imports, {}) | {d['failure']})
            parts.append(d.get('message', '') + '\n' + d.get('reason', ''))
            for m in sorted(modules):
                parts.append(f"your change of {m} broke its importer {d['failure']}: adapt the importers in the same delivery or do not change what they use")
        messages[key(e)] = '\n\n'.join(parts)
    chosen = [e for e in active if e in suspects or e in deps]
    if not chosen:
        b['await_recovery'] = True
        b.pop('triage', None)
        write_json(OPEN, b)
        return
    tip = (ld.read_json(ld.B / 'last.json') or {}).get('commit') or md.git('rev-parse', 'HEAD')
    repair_jobs = {key(e): repairs.stage(e, tip, per[key(e)], messages[key(e)]) for e in suspects}
    try:
        undo_entries(chosen, f"batch {b['id']} dependency take-out", returned=messages, repair_jobs=repair_jobs)
    except recovery.Conflict as x:
        withdraw(b, 'take-out conflict: ' + str(x), log); return
    for e in suspects:
        e['state'] = 'returned'; e['why'] = messages[key(e)]
        e['repair'] = repair_jobs[key(e)]['id']
        log('TAKEN OUT; REPAIR QUEUED', key(e), repair_jobs[key(e)]['group'], '|', messages[key(e)][:300])
    defer_entries(deps)
    b['round'] += 1
    b['await_recovery'] = True
    b.pop('triage', None)
    write_json(OPEN, b)


def closure_fallback(b, last, log, imports=None):
    """Alert and defer all closure-touching deliveries; leave independent work in place."""
    failures = list(last.get('failing') or []) + [c['module'] for c in last.get('batch_checks') or []]
    alert(b['id'], ' '.join(failures) or '?', 'no suspect or four recovery rounds', 'repair failing import closure')
    if imports is None: imports = library_imports()
    closure = set()
    for m in failures: closure |= li.closure(m, imports, {}) | {m}
    # At the no-suspect boundary, independently attributed failures still
    # return their suspects, in the same transaction as deferred closures.
    T = triage(b, last, imports) if b['round'] < ROUNDS else {'decisions': [], 'open': []}
    decisions = T['decisions'] + verdict_decisions({'open': T['open']}, None)
    execute(b, decisions, log, deferred=closure, imports=imports)
    b['fallback'] = True
    write_json(OPEN, b)
    chosen = [e for e in b['entries'] if e['state'] == 'waiting']
    log(f"batch {b['id']}: ALERT; {len(chosen)} closure deliveries waiting; build remaining tree")


def step(cache: dict, log) -> str:
    """One step of the cycle; returns what it did (idle, landed, waiting, verified, triage, returned)."""
    repairs.reconcile()
    stats = repairs.counts()
    if cache.get('_repair_stats') != stats:
        log('REPAIR statistics', json.dumps(stats, sort_keys=True))
        cache['_repair_stats'] = stats
    b = read_json(OPEN)
    if not b:
        return "landed" if land_batch(cache, log) else "idle"
    for e in b["entries"]:
        if e["state"] != "landed":
            continue
        r = ld.read_json(ld.DONE / f"{e['landing']}.json")
        if r and r.get("result", "verified") == "verified":
            e["state"] = "verified"; e["build"] = r.get("commit")
        elif r:
            e["state"] = "reverted"; e["why"] = r.get("reason")
            log("reverted by the maintainer", e["group"], e["item"], e["head"][:9], "|", str(r.get("reason"))[:200])
    pend = [e for e in b["entries"] if e["state"] == "landed"]
    if b.get('await_recovery'):
        last = ld.read_json(ld.B / 'last.json') or {}
        removed = {e['landing'] for e in b['entries'] if e['state'] in ('returned', 'waiting', 'reverted')}
        fresh = last.get('time') not in b['handled'] and not removed & set(last.get('included') or [])
        if not fresh: return 'waiting'
        if last.get('result') == 'green': b.pop('await_recovery', None)
        elif not pend: return 'waiting'
    if not pend:
        n = sum(e["state"] == "verified" for e in b["entries"])
        b["closed"] = ld.now()
        b["cycle_seconds"] = round(time.time() - calendar.timegm(time.strptime(b["time"], "%Y-%m-%dT%H:%M:%SZ")))
        write_json(CLOSED / f"{b['id']}.json", b); OPEN.unlink(missing_ok=True)
        log(f"batch {b['id']} closed: {n} verified by the global build, {len(b['entries']) - n} not "
            f"({', '.join(key(e) + ' ' + e['state'] for e in b['entries'] if e['state'] != 'verified') or '-'}); "
            f"cycle {b['cycle_seconds']} s, {b['round']} round(s) of triage")
        clear_alert()
        return "verified"
    write_json(OPEN, b)
    if "_pre" in cache:
        cache["_pre"].pump(candidates(cache))
    if b.get("triage"):
        t = b["triage"]
        v = read_json(pathlib.Path(t["dir"]) / "verdict.json")
        if v is None and time.time() < t["deadline"]:
            return "triage"
        if v is None:
            log(f"batch {b['id']}: no verdict from the triage agent in time; every suspect of an undecided failure is returned")
        ds = t["decisions"] + verdict_decisions(t["T"], v)
        for d in ds:
            log(f"batch {b['id']} triage: {d['failure']} -> {d['case']} ({d.get('by', 'tools')}), return {', '.join(d['return']) or 'nothing'}")
        pre = cache.get('_pre')
        imports = pre.snapshot() if hasattr(pre, 'snapshot') else library_imports()
        execute(b, ds, log, imports=imports)
        return "returned"
    # a red build is this batch's to handle when it contains landings of the batch that are still in the library and
    # none that was taken out since (a snapshot from before the last round), and was not handled already
    last = ld.read_json(ld.B / "last.json")
    inc = set((last or {}).get("included") or [])
    if not last or last.get("result") != "red" or last.get("time") in b["handled"]:
        return "waiting"
    if not {e["landing"] for e in pend} & inc or {e["landing"] for e in b["entries"] if e["state"] in ("returned", "reverted", "waiting")} & inc:
        return "waiting"
    pre = cache.get('_pre')
    imports = pre.snapshot() if hasattr(pre, 'snapshot') else library_imports()
    T = triage(b, last, imports)
    # Source attribution can outlive a build or a manual take-out. Discard its
    # decision before writing records/ALERT or taking anything out.
    if read_json(OPEN) != b or ld.read_json(ld.B / "last.json") != last:
        return "waiting"
    log(f"batch {b['id']}: RED build (round {b['round'] + 1}); failing {' '.join((last.get('failing') or [])[:8])}")
    b["handled"].append(last.get("time"))
    if T['unattributed'] or b['round'] >= 4:
        closure_fallback(b, last, log, imports)
        return 'returned'
    if T['open']:
        d = write_request(b, T)
        b["triage"] = {"dir": str(d), "deadline": time.time() + TRIAGE_WAIT, "decisions": T["decisions"], "T": {"open": T["open"]}}
        write_json(OPEN, b)
        log(f"batch {b['id']}: {len(T['open'])} failure(s) with several possible causes handed to the triage agent ({d.relative_to(ROOT)})")
        return "triage"
    for d in T["decisions"]:
        log(f"batch {b['id']} triage: {d['failure']} -> {d['case']} (tools), return {', '.join(d['return'])}")
    execute(b, T["decisions"], log, imports=imports)
    return "returned"


def main(a: list[str]) -> int:
    def out(*x):
        print(time.strftime("%F %T"), *x, flush=True)
    if len(a) == 2 and a[0] == "check-one":      # run_checks
        pathlib.Path(a[1]).write_bytes(pickle.dumps(_check(json.load(sys.stdin)))); return 0
    if a == ["step"]:
        print(step({}, out)); return 0
    if a == ["status"]:
        b = read_json(OPEN)
        if b:
            print(f"open batch {b['id']} (round {b['round']}{', waiting for the triage agent' if b.get('triage') else ''}):")
            for e in b["entries"]:
                print(f"  {e['state']:9} {key(e)} {e['head'][:9]} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
        else:
            print("no open batch")
        for p in sorted(PASSED.glob("*.json")) if PASSED.is_dir() else []:
            m = read_json(p) or {}
            print(f"  passed, waiting for a batch: {m.get('group')}/{m.get('item')} {str(m.get('head'))[:9]} by {m.get('reviewer')}")
        return 0
    if len(a) >= 4 and a[0] in ("unland", "take-out"):
        b = read_json(OPEN) or {"entries": []}
        e = next((e for e in b["entries"] if e["group"] == a[1] and e["item"] == a[2] and e["state"] == "landed"), None)
        if not e:
            print(f"{a[1]}/{a[2]} is not a landed delivery of the open batch"); return 1
        reason = " ".join(a[3:])
        try:
            unland(e, f"(the batch landing, head {e['head'][:9]}) taken out of the library again by the maintainer: {reason}", reason)
        except recovery.Conflict as exc:
            withdraw(b, 'take-out conflict: ' + str(exc), out)
            return 0
        e["state"] = "returned"; e["why"] = reason; write_json(OPEN, b)
        return 0
    if a and a[0] == "pass":
        import argparse
        ap = argparse.ArgumentParser(prog="batch_land.py pass")
        ap.add_argument("group"); ap.add_argument("item"); ap.add_argument("--head"); ap.add_argument("--reviewer", default="reviewer")
        ap.add_argument("--spot-checked"); ap.add_argument("--verdict"); ap.add_argument("--apply-fixes"); ap.add_argument("--dry-run", action="store_true")
        try:
            return cmd_pass(ap.parse_args(a[1:]))
        except md.Fail as e:
            print(f"NOT MERGED {a[2] if len(a) > 2 else '?'}: {e}"); return 1
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
