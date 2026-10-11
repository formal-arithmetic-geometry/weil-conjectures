#!/usr/bin/env python3
"""Everything a reviewer of a stage-1 delivery has to read, in one file.

Usage:
  tools/review_packet.py <group> <item> [--out <file>]     prints the path of the packet

Read from the branch deliver/<group>/<item> and from sheaf-dag with `git show`; nothing is checked out or changed.
The packet holds: the item (statement, source, proof steps) with, under each step, the full statement of every
node it cites; the new nodes (statement, source, Mathlib searches and match); the fields changed in existing nodes;
for each new node the existing nodes with the same Stacks tag; the Stacks text (statement and proof) of every tag
named by the item and the new nodes; the group's report; earlier returns of the item. A reviewer who has the packet
opens other files only to follow a doubt.

  tools/review_packet.py <group> <item> --stage 2 [--out <file>]
Stage 2 (a statement delivery, tools/README.md "Stage 2"): the node (statement, kind, chapter, unit, stmt_deps); each
stmt_dep with its statement and its recorded `lean`; the delivered `lean` record and the result of the mechanical
checks of tools/stage2_delivery.py; the Lean file in full; for every identifier of the file that is some node's
recorded declaration, that node's statement; the compile (on the server only); for each NEW definition node of the
delivery (coord/STATE.md, STAGE 2 EXTRA NODES) its statement, source, searches, the node in full, the nodes with the
same title or Stacks tag, the Stacks text of its tags and its module in full; for each DEPENDENCY module the dependency
node's statement, its old record (lean, mathlib_match), the delivered record and the module in full; the report;
earlier returns. When the item is CORRECTED (coord/STATE.md, STAGE 2 STATEMENT CORRECTION) a section `## Statement
corrected` before the Lean: old and new statement verbatim, what, source, the base->head diff of stmt_deps, proof and
proof_deps, the citers table (base nodes citing the item, with the delivered holds/note) and the statements of two
citers (those marked holds:false first).
"""
from __future__ import annotations
import json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
if not (ROOT / "dag").exists(): ROOT = pathlib.Path.home() / "weil-conjectures-sheaf"
TAG = re.compile(r"\b0[0-9A-Z]{3}\b")


def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout


def show(ref, path):
    r = subprocess.run(["git", "-C", str(ROOT), "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def tags_of(*xs):
    out = []
    for x in xs:
        for t in TAG.findall(json.dumps(x, ensure_ascii=False) if not isinstance(x, str) else x):
            if t not in out: out.append(t)
    return out


def stacks(tag, tagmap, cap=9000):
    lab = tagmap.get(tag)
    if not lab: return None
    parts = lab.split("-"); f = None
    for k in range(len(parts) - 1, 0, -1):
        c = ROOT / "literature" / "stacks-project" / ("-".join(parts[:k]) + ".tex")
        if c.exists(): f = c; label = "-".join(parts[k:]); break
    if f is None: return None
    L = f.read_text(errors="ignore").split("\n")
    try: i = next(n for n, l in enumerate(L) if l.strip() == f"\\label{{{label}}}")
    except StopIteration: return None
    a = i
    while a > 0 and not L[a].startswith("\\begin{") and not L[a].startswith("\\section") and not L[a].startswith("\\subsection"): a -= 1
    m = re.match(r"\\begin\{(\w+)\}", L[a]); b = i
    if m:
        while b < len(L) - 1 and not L[b].startswith(f"\\end{{{m.group(1)}}}"): b += 1
        c = b + 1
        while c < len(L) and not L[c].strip(): c += 1
        if c < len(L) and L[c].startswith("\\begin{proof}"):
            b = c
            while b < len(L) - 1 and not L[b].startswith("\\end{proof}"): b += 1
    else:
        b = min(len(L) - 1, i + 40)
    txt = "\n".join(L[a:b + 1])
    if len(txt) > cap: txt = txt[:cap] + f"\n[... cut at {cap} characters; {f.name} lines {a+1}-{b+1}]"
    return f"{f.name} lines {a+1}-{b+1} ({lab})\n{txt}"


def stacks_tagmap():
    tagmap = {}
    tf = ROOT / "literature" / "stacks-project" / "tags" / "tags"
    if tf.exists():
        for l in tf.read_text().split("\n"):
            if l and not l.startswith("#") and "," in l: a, b = l.split(",", 1); tagmap[a] = b
    return tagmap


def main_stage2(g, item) -> int:
    import stage2_delivery as s2
    br = f"deliver/{g}/{item}"
    G = s2.Git(ROOT)
    head = git("rev-parse", "--short", br).strip()
    if not head: print(f"no branch {br}"); return 1
    base = git("merge-base", "sheaf-dag", br).strip()
    D = s2.read_delivery(G, br, base, g, item)
    nodes = s2.nodes_at(G, "sheaf-dag")
    new, deps = D.get("new") or {}, D.get("deps") or {}
    # the declarations of the delivery's own nodes resolve too (new nodes, dependency nodes as delivered)
    dnodes = dict(nodes); dnodes.update({k: v["node"] for k, v in new.items()}); dnodes.update({k: v["node"] for k, v in deps.items()})
    comp = {c["file"]: c for c in s2.compile_modules(D, g)}
    o = []; w = o.append
    w(f"# Review packet (stage 2): {item} (group {g})\n")
    files = git("diff", "--name-status", f"{base}..{br}").strip()
    w(f"Branch {br} at {head}, on base {base[:9]} (sheaf-dag is at {git('rev-parse', '--short', 'sheaf-dag').strip()}). "
      f"Files:\n\n```\n{files}\n```\n")
    if D.get("roles"):
        w("Classification: the item; " + "; ".join(D["roles"]) + "\n")
    if new or deps:
        w(f"**This delivery has {len(new)} new definition node(s) and {len(deps)} dependency module(s)** (coord/STATE.md, STAGE 2 "
          "EXTRA NODES): read sections 7 and 8; a new node that exists in Mathlib, the source or the DAG, or whose fields break "
          "the rule, is H12; a dependency module that does not state the dependency node's notion is H13.\n")
    if D.get("corrected"):
        w(f"**The item's statement is CORRECTED by this delivery** (statement_change; {len(D.get('citers') or [])} citer(s)): read "
          "the section `Statement corrected` before the Lean.\n")
    d = D["node"] or nodes.get(item) or {}
    w(f"## 1. The node\n\n- kind {d.get('kind')}, status {d.get('status')}, chapter {d.get('chapter')}, unit {d.get('unit')}\n"
      f"- source: {json.dumps(d.get('source'), ensure_ascii=False)}\n- stmt_deps: {d.get('stmt_deps')}"
      + (f" (added by the delivery: {D.get('added_deps')})" if D.get("added_deps") else "") + "\n")
    w(f"**Statement.** {d.get('statement')}\n")
    w("## 2. The statement dependencies and their recorded declarations\n")
    for u in d.get("stmt_deps") or []:
        if u in new:
            w(f"- **[{u}]** NEW definition node of this delivery: see section 7\n"); continue
        n = nodes.get(u)
        if n is None: w(f"- **[{u}]** DOES NOT EXIST on sheaf-dag\n"); continue
        l = n.get("lean") if isinstance(n.get("lean"), dict) else None
        lean = (f"convention node, no Lean notion (L): {l.get('note')}" if l and l.get("convention") else (f"`{l.get('module')}` / `{l.get('declaration')}`" + (f"\n  - statement: `{l.get('statement')}`" if l.get("statement") else "")
                + (f"\n  - branch {l.get('branch')}" if l.get("branch") else "")) if l else "**no Lean declaration recorded**")
        if u in deps:
            lean += "\n  - **the delivery replaces this record by a dependency module: see section 8**"
        w(f"- **[{u}]** ({n.get('kind')}): {n.get('statement')}\n  - lean: {lean}\n")
    w("## 3. The delivered `lean` record\n\n```json\n" + json.dumps(D["rec"], indent=1, ensure_ascii=False) + "\n```\n")
    if D["fails"] or D["notes"]:
        w("**Mechanical checks (tools/stage2_delivery.py) found** (on the whole delivery):\n")
        for L, x in D["fails"]: w(f"- ({L}) {x}")
        for x in D["notes"]: w(f"- note: {x}")
        w("")
    else:
        w("Mechanical checks (a)-(e) of tools/stage2_delivery.py on the whole delivery: nothing found.\n")

    def used_section(text, nid, sdeps):
        used = [u for u in s2.used_recorded(text, s2.declaration_map(dnodes)) if u[2] != nid]
        if not used: w("none found (the file uses no declaration that a node records)\n")
        for tok, full, uid in used:
            n = dnodes.get(uid) or {}
            tagn = " (NEW in this delivery)" if uid in new else (" (dependency module of this delivery)" if uid in deps else "")
            w(f"- `{tok}` = `{full}` is the declaration of **[{uid}]**{tagn}{' (a stmt_dep)' if uid in sdeps else ' (NOT a stmt_dep of the node)'}: {n.get('statement')}\n")
        undeclared = [u for u in sdeps if u not in {x[2] for x in used}]
        if undeclared: w(f"stmt_deps whose recorded declaration the file does not visibly use: {undeclared}\n")

    def compile_section(path):
        c = comp.get(path)
        if c is None: w("not compiled (the module is not among the checked modules)\n"); return
        if c["status"] in ("ok", "fail"): w("```\n" + c["out"][-6000:] + f"\n```\nexit code {c['rc']}\n")
        else: w(c["out"] + "\n")

    if D.get("corrected"):
        b, sc = D.get("base_node") or {}, d.get("statement_change") if isinstance(d.get("statement_change"), dict) else {}
        w("## Statement corrected\n\nThe delivery CORRECTS the item's statement (coord/STATE.md, STAGE 2 STATEMENT CORRECTION). "
          "Read the corrected statement against the source first (a correction that makes the node easier than the source is "
          "H7), then the Lean against the corrected statement, and check the two citers below.\n")
        w("**Old statement (base, verbatim).**\n\n" + str(b.get("statement")) + "\n")
        w("**New statement (delivered, verbatim).**\n\n" + str(d.get("statement")) + "\n")
        w(f"**What was wrong.** {sc.get('what')}\n\n**Source the correction follows.** {json.dumps(sc.get('source'), ensure_ascii=False)}\n"
          f"\n- by {sc.get('by')}, {sc.get('date')}" + ("; it replaces an earlier statement_change (kept under `previous`)" if "previous" in sc else "") + "\n")
        for k in ("stmt_deps", "proof_deps"):
            bo, he = list(b.get(k) or []), list(d.get(k) or [])
            if bo != he:
                w(f"- {k}: base {bo} -> head {he} (lost {[x for x in bo if x not in he]}, gained {[x for x in he if x not in bo]})")
            else:
                w(f"- {k}: unchanged")
        if b.get("proof") != d.get("proof"):
            w("\nproof, base:\n\n```json\n" + json.dumps(b.get("proof"), indent=1, ensure_ascii=False) + "\n```\n"
              "proof, head:\n\n```json\n" + json.dumps(d.get("proof"), indent=1, ensure_ascii=False) + "\n```\n")
        else:
            w("- proof: unchanged\n")
        marks = D.get("citer_marks") or []
        byid = {c.get("id"): c for c in marks}
        w(f"\n**Citers** (base nodes whose stmt_deps or proof_deps name the item: {len(D.get('citers') or [])}):\n")
        w("| citer | holds | note |\n|---|---|---|")
        for cid in D.get("citers") or []:
            c = byid.get(cid)
            w(f"| {cid} | {c.get('holds') if c else '**not listed**'} | {str(c.get('note')).replace('|', '/') if c else ''} |")
        for c in marks:
            if c.get("id") not in (D.get("citers") or []):
                w(f"| {c.get('id')} (does not cite the item on the base) | {c.get('holds')} | {str(c.get('note')).replace('|', '/')} |")
        pick = [c for c in D.get("citers") or [] if (byid.get(c) or {}).get("holds") is False]
        pick += [c for c in D.get("citers") or [] if c not in pick]
        w("\nTwo citers to check (holds:false first):\n")
        for cid in pick[:2]:
            n = nodes.get(cid) or {}
            how = ("stmt_deps" if item in (n.get("stmt_deps") or []) else "") + (" proof_deps" if item in (n.get("proof_deps") or []) else "")
            w(f"- **[{cid}]** ({n.get('kind')}; cites the item in {how.strip()}): {n.get('statement')}\n"
              f"  - its line: {json.dumps(byid.get(cid), ensure_ascii=False)}\n")
        if not pick:
            w("none (no node cites the item)\n")
    w("## 4. The Lean file\n")
    text = D["lean_text"]
    if text is None:
        w("no Lean file in the delivery" + (" (an existing declaration)" if (D["rec"] or {}).get("existing") else "") + "\n")
    else:
        w(f"`{D['lean_path']}`\n\n```lean\n{text.rstrip()}\n```\n")
        w("## 5. Recorded declarations the file uses, with the statements of their nodes\n")
        used_section(text, item, d.get("stmt_deps") or [])
        w("## 6. The compile\n")
        compile_section(D["lean_path"])
    if [m for m in D.get("modules") or [] if m["siblings"]]:
        w("Compile order of the delivery's modules (sibling imports first): " + ", ".join(f"`{m['module']}`" for m in D["modules"]) + "\n")
    tagmap = None
    mods = {m["node"]: m for m in D.get("modules") or []}
    w("## 7. New definition nodes\n")
    if not new: w("none\n")
    for nid, x in new.items():
        n = x["node"]
        w(f"### {nid} (`{x['path']}`)\n\n**Statement.** {n.get('statement')}\n\n- source: {json.dumps(n.get('source'), ensure_ascii=False)}\n"
          f"- stmt_deps: {n.get('stmt_deps')}\n")
        for u in n.get("stmt_deps") or []:
            m = dnodes.get(u) or {}
            w(f"  - [{u}]{' (NEW)' if u in new else ''}: {str(m.get('statement'))[:800]}")
        w("\nMathlib searches recorded:\n")
        for s in n.get("mathlib_searches") or []:
            w("- " + (json.dumps(s, ensure_ascii=False)[:900] if isinstance(s, dict) else str(s)[:900]))
        w("\nThe node in full:\n\n```json\n" + json.dumps(n, indent=1, ensure_ascii=False) + "\n```\n")
        hits = [(h, e) for h, e in nodes.items() if h != nid and str(e.get("title") or "").strip().lower() == str(n.get("title") or "").strip().lower()]
        if hits:
            w("Nodes on sheaf-dag with the same title (is the new node one of them?): " + ", ".join(f"[{h}]" for h, _ in hits[:10]) + "\n")
        tg = tags_of(n.get("source"))
        if tg:
            if tagmap is None: tagmap = stacks_tagmap()
            same = [(h, t) for t in tg for h, e in nodes.items() if t in json.dumps(e.get("source"), ensure_ascii=False)]
            if same:
                w("Nodes on sheaf-dag with the same Stacks tag in their source (is the new node one of them?): "
                  + ", ".join(f"[{h}] ({t})" for h, t in same[:12]) + "\n")
            for t in tg[:6]:
                sx = stacks(t, tagmap)
                w(f"Stacks tag {t}:\n\n" + (f"```\n{sx}\n```\n" if sx else "not found in literature/stacks-project (open the source named in the node)\n"))
        m = mods.get(nid)
        if m:
            w(f"Its module `{m['file']}`:\n\n```lean\n{m['text'].rstrip()}\n```\n")
            w("Recorded declarations it uses:\n"); used_section(m["text"], nid, n.get("stmt_deps") or [])
            w("Compile:\n"); compile_section(m["file"])
        else:
            w("No module (lean record: " + json.dumps(n.get("lean"), ensure_ascii=False) + ")\n")
    w("## 8. Dependency modules\n")
    if not deps: w("none\n")
    for nid, x in deps.items():
        n, b = x["node"], x["base_node"]
        w(f"### {nid} (`{x['path']}`)\n\n**Statement of the dependency node.** {n.get('statement')}\n\n- source: {json.dumps(n.get('source'), ensure_ascii=False)}\n"
          f"- its old record on the base: lean = {json.dumps(b.get('lean'), ensure_ascii=False)}; mathlib_match = {json.dumps(b.get('mathlib_match'), ensure_ascii=False)}\n"
          f"- the delivered record: {json.dumps(n.get('lean'), ensure_ascii=False)}\n")
        m = mods.get(nid)
        if m:
            w(f"The module `{m['file']}`:\n\n```lean\n{m['text'].rstrip()}\n```\n")
            w("Recorded declarations it uses:\n"); used_section(m["text"], nid, n.get("stmt_deps") or [])
            w("Compile:\n"); compile_section(m["file"])
        else:
            w("**No module in the delivery for this dependency node.**\n")
    w("## 9. The group's report\n\n" + (D["report"] or "**no report in the delivery**") + "\n")
    ret = ROOT / "coord" / "returns" / f"{g}.md"
    if ret.exists():
        ent = [e for e in re.split(r"\n(?=## )", ret.read_text()) if item in e.split("\n")[0]]
        if ent: w("## 10. Earlier returns of this item (check that every point was repaired)\n\n" + "\n\n".join(ent)[-8000:] + "\n")
    out = pathlib.Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else pathlib.Path("/tmp/review-packets") / f"{g}__{item}.md"
    out.parent.mkdir(parents=True, exist_ok=True); out.write_text("\n".join(o))
    print(out, f"({len(out.read_text())} characters)")
    return 0


def main() -> int:
    if "--stage" in sys.argv:
        k = sys.argv.index("--stage"); st = sys.argv[k + 1] if k + 1 < len(sys.argv) else ""
        rest = [a for j, a in enumerate(sys.argv[1:], 1) if j not in (k, k + 1) and not a.startswith("--")
                and not (j > 1 and sys.argv[j - 1] == "--out")]
        if st == "2":
            if len(rest) < 2: print(__doc__); return 2
            return main_stage2(rest[0], rest[1])
        if st != "1": print(f"--stage {st!r}: 1 or 2"); return 2
        sys.argv = [x for j, x in enumerate(sys.argv) if j not in (k, k + 1)]
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) < 2: print(__doc__); return 2
    g, item = args[0], args[1]; br = f"deliver/{g}/{item}"
    head = git("rev-parse", "--short", br).strip()
    if not head: print(f"no branch {br}"); return 1
    base = git("merge-base", "sheaf-dag", br).strip()
    changed = [l.split("\t") for l in git("diff", "--name-status", f"{base}..{br}").strip().split("\n") if l]
    index = {p.stem: p for p in (ROOT / "dag" / "nodes").glob("*/*.json")}
    new, mod, other = {}, {}, []
    for st, path in [(c[0], c[-1]) for c in changed]:
        if path.startswith("dag/nodes/") and path.endswith(".json"):
            try: d = json.loads(show(br, path) or "")
            except Exception: other.append(f"{st} {path}  (NOT VALID JSON)"); continue
            (new if st == "A" else mod)[pathlib.Path(path).stem] = (path, d)
        else: other.append(f"{st} {path}")

    def node(nid):
        if nid in new: return new[nid][1], "NEW in this delivery"
        if nid in mod: return mod[nid][1], "existing, changed by this delivery"
        p = index.get(nid)
        if p is None: return None, "DOES NOT EXIST"
        try: return json.loads(p.read_text()), "existing"
        except Exception: return None, "unreadable"

    o = []; w = o.append
    w(f"# Review packet: {item} (group {g})\n")
    w(f"Branch {br} at {head}, on base {base[:9]} (sheaf-dag is at {git('rev-parse', '--short', 'sheaf-dag').strip()}). "
      f"New nodes: {len(new)}; existing nodes changed: {len(mod)}; other files: {', '.join(other) or 'none'}.\n")
    if item not in mod and item not in new: w(f"**The item {item} is not among the files of the delivery.**\n")
    d, _ = node(item)
    if d:
        w(f"## 1. The item\n\n- kind {d.get('kind')}, status {d.get('status')}, chapter {d.get('chapter')}, unit {d.get('unit')}\n- source: {json.dumps(d.get('source'), ensure_ascii=False)}\n- proof_origin: {json.dumps(d.get('proof_origin'), ensure_ascii=False)}\n- stmt_deps: {d.get('stmt_deps')}\n")
        old = show(base, mod[item][0]) if item in mod else None
        if old:
            try:
                if json.loads(old).get("statement") != d.get("statement"): w("**The delivery changes the statement of the item.** Before:\n\n" + str(json.loads(old).get("statement")) + "\n\nAfter:\n")
            except Exception: pass
        w(f"**Statement.** {d.get('statement')}\n")
        if d.get("status") == "mathlib": w(f"**Mathlib match.** {json.dumps(d.get('mathlib_match'), ensure_ascii=False)}\n")
        w("## 2. The proof, step by step, with the statements it cites\n")
        seen = set()
        for k, s in enumerate(d.get("proof") or [], 1):
            if not isinstance(s, dict): w(f"### Step {k}: malformed\n"); continue
            w(f"### Step {k} (elementary: {s.get('elementary')})\n\n{s.get('text')}\n")
            for u in s.get("uses") or []:
                n, what = node(u)
                if n is None: w(f"- **[{u}]** {what}\n"); continue
                if u in seen: w(f"- **[{u}]** ({what}) statement given above\n"); continue
                seen.add(u)
                w(f"- **[{u}]** ({what}; {n.get('kind')}, status {n.get('status')}): {n.get('statement')}\n")
        sr = d.get("split_report")
        if sr: w("**split_report.** " + json.dumps(sr, ensure_ascii=False)[:3000] + "\n")
    w("## 3. New nodes\n")
    if not new: w("none\n")
    tagidx = None
    for nid, (path, n) in new.items():
        w(f"### {nid} ({n.get('kind')}, status {n.get('status')})\n\n- source: {json.dumps(n.get('source'), ensure_ascii=False)}\n- stmt_deps: {n.get('stmt_deps')}; created: {json.dumps(n.get('created'))}; blueprint: {json.dumps(n.get('blueprint'), ensure_ascii=False)[:400]}\n\n**Statement.** {n.get('statement')}\n")
        if n.get("proof"): w("**It carries proof steps** (a new node that is not split carries a statement only): " + json.dumps(n.get("proof"), ensure_ascii=False)[:1500] + "\n")
        if n.get("mathlib_match"): w(f"**Mathlib match.** {json.dumps(n.get('mathlib_match'), ensure_ascii=False)}\n")
        w("Mathlib searches recorded:\n")
        for s in n.get("mathlib_searches") or []:
            w("- " + (json.dumps(s, ensure_ascii=False)[:700] if isinstance(s, dict) else str(s)[:700]))
        w("")
        tg = tags_of(n.get("source"))
        if tg:
            if tagidx is None:
                tagidx = {}
                for p in index.values():
                    t = p.read_text(errors="ignore")
                    m = re.search(r'"source":\s*(\{.*?\}|".*?"|null)', t, re.S)
                    for x in set(TAG.findall(m.group(1))) if m else (): tagidx.setdefault(x, []).append(p)
            hits = []
            for x in tg:
                for p in tagidx.get(x, []):
                    if p.stem != nid and p.stem not in [h[0] for h in hits]: hits.append((p.stem, x, p))
            if hits:
                w(f"Existing nodes with the same Stacks tag ({len(hits)}; is the new node one of them, or a special case?):\n")
                for h, x, p in hits[:10]:
                    try: e = json.loads(p.read_text())
                    except Exception: continue
                    w(f"- [{h}] ({x}, status {e.get('status')}){' — THE ITEM' if h == item else ''}: {str(e.get('statement'))[:600]}")
                w("")
    w("## 4. Existing nodes changed (other than the item)\n")
    k = 0
    for nid, (path, n) in mod.items():
        if nid == item: continue
        k += 1
        try: b = json.loads(show(base, path) or "{}")
        except Exception: b = {}
        ch = [f for f in sorted(set(n) | set(b)) if n.get(f) != b.get(f)]
        w(f"### {nid}: fields changed {ch}\n")
        for f in ch: w(f"- {f}: before {json.dumps(b.get(f), ensure_ascii=False)[:800]}\n  after {json.dumps(n.get(f), ensure_ascii=False)[:1500]}")
        w("")
    if not k: w("none\n")
    w("## 5. The Stacks project text of the tags named by the item and the new nodes\n")
    tagmap = {}
    tf = ROOT / "literature" / "stacks-project" / "tags" / "tags"
    if tf.exists():
        for l in tf.read_text().split("\n"):
            if l and not l.startswith("#") and "," in l: a, b = l.split(",", 1); tagmap[a] = b
    want = tags_of((d or {}).get("source"), (d or {}).get("proof_origin"), *[n.get("source") for _, n in new.values()], *[s.get("text", "") for s in ((d or {}).get("proof") or []) if isinstance(s, dict)])
    for t in want[:10]:
        x = stacks(t, tagmap)
        w(f"### Tag {t}\n\n" + (f"```\n{x}\n```\n" if x else "not found in literature/stacks-project (open the source named in the node)\n"))
    if len(want) > 10: w(f"(further tags named, not printed: {', '.join(want[10:])})\n")
    rep = show(br, f"coord/reports/{g}/{item}.md")
    w("## 6. The group's report\n\n" + (rep if rep else "**no report in the delivery**") + "\n")
    ret = ROOT / "coord" / "returns" / f"{g}.md"
    if ret.exists():
        ent = [e for e in re.split(r"\n(?=## )", ret.read_text()) if item in e.split("\n")[0]]
        if ent: w("## 7. Earlier returns of this item (check that every point was repaired)\n\n" + "\n\n".join(ent)[-8000:] + "\n")
    out = pathlib.Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else pathlib.Path("/tmp/review-packets") / f"{g}__{item}.md"
    out.parent.mkdir(parents=True, exist_ok=True); out.write_text("\n".join(o))
    print(out, f"({len(out.read_text())} characters)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
