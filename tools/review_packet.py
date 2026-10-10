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


def main() -> int:
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
