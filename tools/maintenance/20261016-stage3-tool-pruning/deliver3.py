#!/usr/bin/env python3
"""Deliver a stage-3 item (a module, proved in whole or in part) from its sandbox.   deliver3.py <group> <module> [--no-push]

Sandbox /home/ubuntu/weil-sandbox/<group>/<module>/ mirrors the repository: Lean files under lean/, node files under
dag/nodes/, change records under coord/changes/, and report.md. Builds one commit on origin/sheaf-dag in the group's clone
(the Lean files; new nodes whole, existing nodes only in the fields a stage-3 delivery owns; the change records; the
report), compiles locally, runs the maintainer's preflight (--stage 3), pushes deliver/<group>/<module>.
"""
import fcntl, json, os, pathlib, re, subprocess, sys, tempfile, time
H = pathlib.Path.home(); KEY = str(H / "weil_formal.pem")
ENV = dict(os.environ, GIT_SSH_COMMAND=f"ssh -i {KEY} -o StrictHostKeyChecking=no -o ServerAliveInterval=10")
sys.path.insert(0, str(H / "weil-launcher")); import scompile, lcompile
OWN = {"lean", "proof", "proof_deps", "proof_origin"}; OWN_CHANGE = {"statement", "stmt_deps", "statement_change"}
SECTIONS = ["## What changed", "## Proved and sorry left", "## No longer needed", "## Where the brief, the DAG or earlier work was wrong"]
BAD = re.compile(r"^\s*(axiom|unsafe|opaque)\b|implemented_by|@\[extern", re.M)
def sh(*a, cwd, check=True, timeout=300, env=None):
    p = subprocess.run(a, cwd=cwd, capture_output=True, text=True, env=env or ENV, timeout=timeout)
    if check and p.returncode: raise SystemExit(f"FAILED: {' '.join(a)}\n{p.stdout}{p.stderr}")
    return p
def scrub(t):
    t = re.sub(r"\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b", "the project server", t)
    t = re.sub(r"\S*(weil_formal|formal3)\.pem", "the key", t); return re.sub(r"ubuntu@\S+", "the project server", t)
def forced_adaptations(clone, sb, item, mods, group=None, compile_one=None):
    """Worker-side counterfactual single-file checks; no claim acquisition or server build.

    The delivered dependencies are already compiled into sb/.lbuild. Compile each
    original against that overlay without writing output or changing the sandbox.
    Semantic necessity/minimality remains the independent CODEX reader's check.
    """
    compile_one = compile_one or lcompile.run
    import stage3_delivery as s3
    rows = []
    for m in mods:
        rel = m.relative_to(sb); old = clone / rel
        name = lcompile.modname(m)
        if name == item or not old.exists() or old.read_text() == m.read_text():
            continue
        job = getattr(s3, 'repair_job', lambda *_: None)(group, item) if group else None
        if job and name in set(job['modules'] + job['failures']):
            continue  # independently read repair uses the recorded global failure
        if group and s3.claim_holder(name) in (group, None):
            continue   # 2026-10-14: a module nobody holds may be changed like a held one (the reader reviews it)
        d = s3.diff_module(old.read_text(), m.read_text())
        # All adaptations are reviewed. The preflight applies the claim exception
        # and signature guard from the exact fetched delivery base.
        with tempfile.TemporaryDirectory(prefix="forced-adaptation-") as tmp:
            root = pathlib.Path(tmp); src = root / rel
            src.parent.mkdir(parents=True, exist_ok=True); src.write_text(old.read_text())
            baseline_rc, baseline_out = compile_one(src)
            if baseline_rc:
                raise SystemExit(f"FAILED: original {name} already fails against the compiled baseline; "
                                 "cannot attribute its failure to your change: " + baseline_out[-1200:])
            (root / ".lbuild").symlink_to(sb / ".lbuild", target_is_directory=True)
            rc, out = compile_one(src)
        if rc == 0:
            raise SystemExit(f"FAILED: {name} compiles unchanged against your changed dependencies; "
                             "its adaptation is not forced. Remove it from this delivery.")
        if rc == 124 or not re.search(r"error:|error\[|error\(", out) or re.search(
                r"unknown module prefix|object file .* does not exist|No such file", out):
            raise SystemExit(f"FAILED: cannot establish forced adaptation of {name}: " + out[-1200:])
        rows.append(f"### {name}\nOriginal against changed dependencies failed:\n```\n" +
                    scrub(out[-2000:]) + "\n```\nAdapted module compiled in the delivered set. "
                    "Explain the forced changed lines in the change record; CODEX verifies them.\n")
    return "\n".join(rows)


def check_import_sources(clone, sb, mods, ref='origin/sheaf-dag'):
    from import_cycles import refuse_missing, source_roots
    paths = sh('git', 'ls-tree', '-r', '--name-only', ref, '--', 'lean', cwd=clone).stdout.splitlines()
    library = {p[5:-5].replace('/', '.') for p in paths if p.endswith('.lean')}
    texts = {'.'.join(m.relative_to(sb / 'lean').with_suffix('').parts): m.read_text() for m in mods}
    try:
        refuse_missing(texts, library, source_roots(H / 'weil-lean'))
    except RuntimeError as exc:
        raise SystemExit('FAILED: ' + str(exc) + '; nothing pushed') from exc


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 2: raise SystemExit(__doc__)
    g, item = args; push = "--no-push" not in sys.argv
    sys.path.insert(0, "/home/ubuntu/weil-launcher-all"); import sharedrepo   # 2026-10-16: no clone per group
    clone = sharedrepo.worktree("weil-conjectures-sheaf"); sb = H / "weil-sandbox" / g / item
    sys.path.insert(0, str(clone / "tools")); import stage3_delivery as s3
    mods = sorted((sb / "lean").rglob("*.lean")) if (sb / "lean").exists() else []
    nodes = sorted(sb.glob("dag/nodes/*/*.json")); changes = sorted(sb.glob("coord/changes/*.md")); rep = sb / "report.md"
    own = sb / "lean" / (item.replace(".", "/") + ".lean")
    # deletions (the human, 2026-10-14: a reviewer may require withdrawing a landed module, e.g. a false split; the delivery
    # deletes it and changes the rest at once). sandbox file deleted.txt: one repository path per line, lean/**/*.lean only
    # (DAG nodes are never deleted).
    deleted = []
    if (sb / "deleted.txt").exists():
        for l in (sb / "deleted.txt").read_text().splitlines():
            l = l.strip()
            if not l or l.startswith("#"): continue
            if not (l.startswith("lean/") and l.endswith(".lean")) or ".." in l:
                raise SystemExit(f"FAILED: deleted.txt may list only lean/**/*.lean files: {l}")
            if not (clone / l).is_file(): raise SystemExit(f"FAILED: deleted.txt lists {l}, which is not on sheaf-dag")
            if (sb / l).exists(): raise SystemExit(f"FAILED: {l} is listed in deleted.txt but still present in the sandbox")
            deleted.append(l)
    own_deleted = str(own.relative_to(sb)) in deleted
    if not own.exists() and not own_deleted: raise SystemExit(f"FAILED: the item's module is not in the sandbox at {own.relative_to(sb)} (to withdraw it, list it in deleted.txt)")
    if deleted:
        gone = {x[len("lean/"):-len(".lean")].replace("/", ".") for x in deleted}
        users = []
        for f in (clone / "lean").rglob("*.lean"):
            rel = str(f.relative_to(clone))
            if rel in deleted or "/.lake/" in rel or "/.sandbox/" in rel: continue
            t = (sb / rel).read_text() if (sb / rel).exists() else f.read_text()
            hit = [m for m in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", t, re.M) if m in gone]
            if hit: users.append(f"{rel} imports {hit[0]}")
        for m in mods:
            rel = str(m.relative_to(sb))
            if not (clone / rel).exists():
                hit = [x for x in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", m.read_text(), re.M) if x in gone]
                if hit: users.append(f"{rel} imports {hit[0]}")
        if users: raise SystemExit("FAILED: deleted modules are still imported (change these files in the delivery too): " + "; ".join(users[:8]))
    if not rep.exists(): raise SystemExit("FAILED: report.md is missing")
    rt = rep.read_text(); miss = [s for s in SECTIONS if s not in rt]
    if miss: raise SystemExit(f"FAILED: report.md lacks the section(s) {miss} (coord/brief-stage3.md §6)")
    if push and not (sb / ".check").exists(): raise SystemExit("NOT PUSHED: the second reader delivers. Your dry run is your last step: answer READY.")
    if push and f"## Second reading by {g}" not in rt: raise SystemExit(f"FAILED: report.md has no '## Second reading by {g}' section")
    for m in mods:
        t = m.read_text()
        if BAD.search(t): raise SystemExit(f"FAILED: {m.relative_to(sb)} contains axiom / unsafe / opaque / implemented_by / extern")
        if not re.search(r"^module\s*$", t, re.M): raise SystemExit(f"FAILED: {m.relative_to(sb)} is not a file of Lean's module system (`module` before the imports; a new module: `module`, the imports, `@[expose] public section`)")
    mods = [m for m in mods if not m.name.endswith("__probe.lean")]
    # the delivery proves something: a declaration of the item's module that had `sorry` on sheaf-dag has none now
    base = clone / "lean" / (item.replace(".", "/") + ".lean")
    if base.exists() and not own_deleted:
        d = s3.diff_module(base.read_text(), own.read_text())
        closed = sorted(set(d["sorry_before"]) - set(d["sorry_after"]))
        # ... and not by handing the whole statement to one new theorem that is left `sorry` (a restatement)
        left = set()
        for m in mods:
            if m != own and not (clone / m.relative_to(sb)).exists():
                left |= {k.split(".")[-1] for k, x in s3.decl_table(m.read_text()).items() if x["sorry"]}
        left |= {k.split(".")[-1] for k in d["new_sorry"]}
        restated = []
        for k in closed:
            # A declaration retired by a repair has no replacement body.
            if k not in d["new"]:
                continue
            b = re.sub(r"^:=\s*(by\s+)?(exact\s+)?", "", d["new"][k]["body"].strip())
            head = (b.split() or [""])[0].lstrip("@(").split(".")[-1]
            if head in left and len(b) < 300 and not re.search(r"\b(fun|by|have|intro|rw|simp|apply|refine|obtain|calc|show|let)\b|;|<;>|\n", b): restated.append((k, head))
        if restated:
            raise SystemExit("FAILED: a restatement, not a proof: " + "; ".join(f"{k} is one application of the new statement {h}, which is left `sorry`" for k, h in restated) +
                             ". Moving a statement to another module under another name proves nothing. A reduction proves the statement from statements each of which is strictly a PART of the "
                             "argument: steps of the node's plan (the existing declarations of the nodes the steps use, in lean/Sheaf and lean/WeilConjectures, or intermediate theorems you state), "
                             "combined by a real proof written in the item's module.")
        try:   # an item of coord/repairs.txt is a repair: a duplicate removed, a statement corrected, data made concrete;
               # it need not close a `sorry` (2026-10-14: such repairs were refused here 30-40 times each)
            listed_repair = any(l.split()[:1] == [item] for l in (clone / 'coord' / 'repairs.txt').read_text().splitlines())
            # 2026-10-14: so is the repair of a return to this group (a reviewer's requested fix on a module that is already
            # sorry-free: TensorBicomplex, KInjectiveProducts, AffineGlobalHomBaseChangeMap were refused 13-16 times each)
            rf = clone / 'coord' / 'returns' / f'{g}.md'
            listed_repair = listed_repair or (rf.is_file() and f'## {item} (' in rf.read_text())
        except Exception:
            listed_repair = False
        if not closed and not d["disputed_new"] and not d["statement_changed"] and not listed_repair and not getattr(s3, 'repair_job', lambda *_: None)(g, item):
            raise SystemExit("FAILED: nothing is proved. The declarations of the module that have `sorry` on sheaf-dag (" + ", ".join(d["sorry_before"]) + ") all still have it; "
                             "a changed proof of a declaration that was already proved, or an added lemma, is not a delivery. Prove at least one of them: from the stated declarations "
                             "of the nodes its plan uses (import their modules; `sorry` there is intended), or from intermediate theorems you state (new modules, nodes).")
    # 2026-10-14 (launcher): a first worker that splits off new `sorry` early hands the hard part to the next group, which
    # starts from nothing (one chain was split 22 times in 2.5 days, a different group each time). Until 60 % of the budget
    # is used, a delivery that adds `sorry` is refused: prove the split-off theorems in this session first.
    bf = sb / ".budget"
    if bf.exists() and not (sb / ".check").exists():
        try:
            bj = json.loads(bf.read_text()); used = time.time() - bj["start"]; budget = bj["budget"]
        except Exception:
            used, budget = 1e9, 1
        def _n(t): return len(re.findall(r"\bsorry\b", re.sub(r"--[^\n]*|/-.*?-/", "", t, flags=re.S)))
        added = 0
        for m in mods:
            o = clone / m.relative_to(sb)
            added += max(0, _n(m.read_text()) - (_n(o.read_text()) if o.exists() else 0))
        if added and used < 0.6 * budget and not bj.get("repair"):
            raise SystemExit(f"FAILED: not yet: this delivery adds {added} `sorry` (split-off theorems) after {int(used // 60)} of your "
                             f"{int(budget // 60)} minutes. They are in your sandbox: prove them now, in this session, from Mathlib, the "
                             "library and further intermediate theorems of your own, and run this dry run again. A split-off `sorry` is "
                             f"delivered only after {int(0.6 * budget // 60)} minutes, when what is left really needs another session.")
    # Refuse a cycle in the library plus all delivered sources, before compiling/pushing.
    from import_cycles import refuse as refuse_import_cycle
    try:
        sys.path.insert(0, str(clone / "tools"))
        import leanindex  # configuration belongs to this clone, including new items
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / "cache-tools"))
        from delivery_cache import cycle_graph
        from import_cycles import closing_cycle
        cached = cycle_graph(clone)
        texts = {'.'.join(m.relative_to(sb / 'lean').with_suffix('').parts): m.read_text() for m in mods}
        if cached is None:
            refuse_import_cycle(clone / 'lean', texts)
        else:
            cycle = closing_cycle(cached, texts)
            if cycle: raise RuntimeError('import cycle: ' + ' -> '.join(cycle))
    except RuntimeError as exc:
        raise SystemExit('FAILED: ' + str(exc) + '; nothing pushed')
    check_import_sources(clone, sb, mods)
    # local: every module, in import order (a module that imports a new module of the delivery finds it in <sandbox>/.lbuild)
    src = (clone / "tools" / "stage3_delivery.py").read_text(); pm = re.search(r'^PROBE = """(.*?)"""', src, re.M | re.S)
    probed = {}
    if own_deleted and not mods:
        rc, out, per = 0, "", []   # only a withdrawal: nothing left in the sandbox to compile
    elif len(mods) == 1 and pm and own.exists():
        # one compile instead of two (2026-10-13: the probe recompiled every delivered file and doubled the compile load):
        # the probe only appends a run_cmd that logs, so the probed copy compiles exactly when the file does
        rc, out = lcompile.run(own, probe=pm.group(1)); per = []; probed[own] = (rc, out)
        # messages about the appended probe's own lines (e.g. its 107-character line, 2026-10-13 21:57) are not the
        # worker's: drop every message located after the delivered file's last line
        nlines = len(own.read_text().split("\n"))
        errs = [l for l in out.split("\n") if re.search(r"__probe\.lean:\d+:\d+: error", l)]
        out = "\n".join(l for l in out.split("\n")
                         if not ((m := re.search(r"__probe\.lean:(\d+):\d+:", l)) and int(m.group(1)) > nlines))
        if rc != 0 and errs and all(int(re.search(r"__probe\.lean:(\d+):", l).group(1)) > nlines for l in errs):
            # 2026-10-14: only the appended probe failed (the file no longer imports what the probe's commands need, e.g.
            # after a reviewer removed an unused meta import): judge the file by itself; the merge runs the probe again
            rc, out = lcompile.run(own); probed.pop(own, None)
    else:
        rc, out, per = lcompile.run_set(mods) if len(mods) > 1 else (*lcompile.run(mods[0] if mods else own), [])
    if rc != 0: print("COMPILE FAILED (local), nothing pushed:\n" + out[-6000:]); sys.exit(1)
    if [l for l in out.split("\n") if "warning" in l.lower() and "declaration uses" not in l]: print("COMPILES WITH WARNINGS (local), nothing pushed:\n" + out[-6000:]); sys.exit(1)
    # Counterfactuals reuse the compiled sandbox, one original module at a time.
    sys.path.insert(0, str(clone / "tools"))
    forced = forced_adaptations(clone, sb, item, mods, group=g)
    if forced:
        rt += "\n## Forced adaptations\n\n" + forced
    # local: the maintainer's probe (the axioms of every declaration of the file), as the merge runs it
    for m in mods if pm else []:
        rc, out = probed[m] if m in probed else lcompile.run(m, probe=pm.group(1))
        ax = sorted(set(re.findall(r"SHEAF-AXIOM (\S+) (\S+)", out)))
        if ax: print(f"AXIOMS, nothing pushed: in {m.relative_to(sb)} " + "; ".join(f"{d} uses {a}" for d, a in ax[:10]) + " (only propext, Classical.choice, Quot.sound)"); sys.exit(1)
        if rc != 0 or "SHEAF-PROBED" not in out: print(f"note: the axiom probe did not run on {m.relative_to(sb)} (the merge runs it again): " + out.strip()[-300:].replace("\n", " "))
    # the server: every module that imports no other module of the delivery (the others are compiled by the landing, as one set)
    names = {lcompile.modname(m) for m in mods}
    # the human, 2026-10-12: no compile on the server for a delivery (the local compile above and the global build of
    # the batch decide; 160 workers opening connections for it overran the connection limit). WEIL_SERVER_COMPILE=1 restores it.
    for m in (mods if os.environ.get("WEIL_SERVER_COMPILE") == "1" else []):
        if len(mods) > 1 and [d for d in lcompile.IMPORT.findall(m.read_text()) if d in names and d != lcompile.modname(m)]: continue
        rc, out = scompile.run(g, lcompile.modname(m).replace(".", "_"), str(m))
        if rc != 0: print(f"COMPILE FAILED on the server for {m.relative_to(sb)}, nothing pushed (if a module you import landed in the last minutes, wait for the next green build and run again):\n" + out[-5000:]); sys.exit(1)
        if [l for l in out.split("\n") if "warning" in l.lower() and "declaration uses" not in l]: print("COMPILES WITH WARNINGS on the server, nothing pushed:\n" + out[-5000:]); sys.exit(1)
    data = {}
    for n in nodes:
        try: data[n] = json.loads(n.read_text())
        except Exception as e: raise SystemExit(f"FAILED: {n.relative_to(sb)} is not valid JSON: {e}")
    lock = open(sharedrepo.WT / "locks" / f"deliver-{g}.lock", "w"); fcntl.flock(lock, fcntl.LOCK_EX)
    if sh("git", "status", "--porcelain", "--untracked-files=no", cwd=clone).stdout.strip():
        sh("git", "checkout", "-q", "-f", "HEAD", cwd=clone); sh("git", "reset", "-q", "--hard", "HEAD", cwd=clone)
    sh("git", "clean", "-q", "-fd", "--", "dag", "coord", "lean", cwd=clone, check=False)
    sharedrepo.fetch("weil-conjectures-sheaf")
    br = f"deliver/{g}/{item}"
    check_import_sources(clone, sb, mods)  # recheck the freshly fetched delivery base before writing/pushing
    sh("git", "checkout", "-q", "--ignore-other-worktrees", "-B", br, "origin/sheaf-dag", cwd=clone)
    try:
        added = []; notes = []
        for n, d in data.items():
            rel = n.relative_to(sb); dst = clone / rel
            if dst.exists():
                cur = json.loads(dst.read_text()); before = json.dumps(cur, sort_keys=True)
                changed_stmt = d.get("statement") != cur.get("statement")
                if changed_stmt and not isinstance(d.get("statement_change"), dict): raise SystemExit(f"FAILED: {n.stem}: the statement differs from sheaf-dag without a `statement_change` record (coord/brief-stage3.md §4)")
                prune = set(s3.STAGE3_PRUNES)
                allow = OWN | prune | (OWN_CHANGE if changed_stmt else set())
                other = [k for k in set(d) | set(cur) if k not in allow and d.get(k) != cur.get(k)]
                if other: notes.append(f"{n.stem}: fields not yours to change were NOT delivered: {sorted(other)[:6]}")
                try:
                    s3.apply_tool_uses_pruning(cur, cur, d)
                except ValueError as exc:
                    raise SystemExit(f"FAILED: {n.stem}: {exc}") from exc
                for k in allow - prune:
                    if k in d and d[k] is None: cur.pop(k, None)   # 2026-10-14: `null` removes a field of yours (a reviewer-ordered detachment)
                    elif k in d: cur[k] = d[k]
                if json.dumps(cur, sort_keys=True) == before: continue
                dst.write_text(json.dumps(cur, indent=1, ensure_ascii=False) + "\n")
            else:
                dst.parent.mkdir(parents=True, exist_ok=True); dst.write_text(json.dumps(d, indent=1, ensure_ascii=False) + "\n")
            added.append(str(rel))
        for m in mods:
            r = m.relative_to(sb); (clone / r).parent.mkdir(parents=True, exist_ok=True)
            if (clone / r).exists() and (clone / r).read_text() == m.read_text(): continue
            (clone / r).write_text(m.read_text()); added.append(str(r))
        for c in changes:
            r = c.relative_to(sb); (clone / r).parent.mkdir(parents=True, exist_ok=True); (clone / r).write_text(scrub(c.read_text())); added.append(str(r))
        rp = pathlib.Path("coord") / "reports" / g / f"{item}.md"; (clone / rp).parent.mkdir(parents=True, exist_ok=True)
        (clone / rp).write_text(scrub(rt)); added.append(str(rp))
        sh("git", "add", "--", *added, cwd=clone)
        # 2026-10-14: the landing tools never delete a file, so a withdrawn module is emptied instead (kept as a module
        # with no declarations); the queue's pruning removes it once nothing imports it
        for x in deleted:
            (clone / x).write_text("module\n\n/-! Withdrawn: no declarations remain. -/\n")
        if deleted: sh("git", "add", "--", *deleted, cwd=clone)
        if not sh("git", "diff", "--cached", "--name-only", cwd=clone).stdout.strip(): raise SystemExit("FAILED: nothing differs from sheaf-dag")
        sh("git", "-c", "user.name=Ubuntu", "-c", "user.email=ubuntu@localhost.localdomain", "commit", "-q", "-m", f"Prove {item} ({g})", cwd=clone)
        head = sh("git", "rev-parse", "--short", "HEAD", cwd=clone).stdout.strip()
        p = subprocess.run(["/usr/bin/python3", "tools/preflight_delivery.py", g, item, "--stage", "3"], cwd=clone, capture_output=True, text=True, env=dict(ENV, PATH="/usr/local/bin:/usr/bin:/bin", SHEAF_COMPILE_ROOT="/nonexistent"), timeout=900)   # the compile is lcompile's and the server's, never the clone's
        pout = p.stdout + p.stderr
        only_second = p.returncode and "1 reason(s)" in pout and "Second reading by" in pout
        for x in notes: print("note:", x)
        if only_second and not push and not (sb / ".check").exists():
            print(f"OK (dry run): commit {head} compiles and passes the preflight except for the second reading, which the second reader writes; nothing pushed."); return
        if p.returncode: print("PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:\n" + pout[-4500:]); sys.exit(1)
        cls = [l for l in pout.split("\n") if l.startswith("review class")]
        if not push: print(f"OK (dry run): commit {head} compiles and passes the preflight; nothing pushed. {cls[-1] if cls else ''}"); return
        sh("git", "push", "-q", "-f", "origin", f"{br}:refs/heads/{br}", cwd=clone, timeout=300)
        print(f"DELIVERED {item} at {head}")
    finally:
        sh("git", "checkout", "-q", "-f", "--detach", cwd=clone, check=False)   # 2026-10-16: worktree; the main branch is checked out in the shared clone
        sh("git", "reset", "-q", "--hard", "origin/sheaf-dag", cwd=clone, check=False)
        sh("git", "branch", "-q", "-D", br, cwd=clone, check=False)
        sh("git", "clean", "-q", "-fd", "--", "dag", "coord", "lean", cwd=clone, check=False)
if __name__ == "__main__": main()
