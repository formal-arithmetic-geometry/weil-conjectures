#!/usr/bin/env python3
"""Merge a newer commit of the source library into lean/, file by file (three-way).

Usage:
  tools/upstream_merge.py plan    <base> <tip> [--source-git DIR] [--resolved DIR] [--json OUT]   read only: what `apply` would do
  tools/upstream_merge.py apply   <base> <tip> [--source-git DIR] [--resolved DIR] [--json OUT]   write lean/ (nothing is committed)
  tools/upstream_merge.py cycles [--json OUT]                         source import cycles and missing project imports
  tools/upstream_merge.py migrate [--apply] [--map FILE] [--target-lean DIR] [--json OUT]   canonical redirects, plan by default
  tools/upstream_merge.py release-gone <items-before> <items-after>     release obsolete queue claims under locks
  tools/upstream_merge.py targets <base> <tip> [--source-git DIR]     whether the source changed the text of a target statement
                                                                      (the theorems of lean/Challenge.lean); exit 4 when it did

<base> is the commit of the source repository that lean/ was last brought to (coord/upstream-base.txt), <tip> the
commit to go to; both are read from the git repository DIR (a checkout of the source repository; default: this one).
The environment variable UPSTREAM_MERGE_ROOT names another copy of this project to work on (a rehearsal, a dry run).
A file of the source repository at path P is lean/P here. For each file the source changed between base and tip:

  take          we did not change it: the file becomes the tip's (a new file is added, a deleted one removed)
  theirs-rule   it is one of the modules left to the other team (ALWAYS_THEIRS): the tip's file, whatever we did
  imports       we changed it only by adding import lines: the tip's file plus those of our lines that name a module
                that still exists
  merged        both changed it and `git merge-file` joins the two changes without conflict
  source-proof  both changed the same lines, and every such place is one of: a `sorry` of the base that both sides
                replaced (`sorry-both`: the source's proof is taken, ours is dropped; the lemmas we added for it stay),
                import lines (`imports`: the source's lines, then ours), or lines added in front of a declaration
                whose proof is taken from the source (`prefix`: the source's lines). Then our own `import Sheaf.X`
                lines whose module declares nothing the file still names are removed (listed)
  resolved      both changed the same lines otherwise, and DIR holds the file a person or an agent decided on for
                exactly this pair (our blob, the tip's blob): DIR/<P> and one line in DIR/index.tsv
                (P <TAB> our blob <TAB> tip blob <TAB> what was chosen and why)
  conflict      both changed the same lines and nothing is recorded: needs judgment. Each place is described:
                `sorry-source-proved` (we changed the statement or the text around a `sorry` the source proved),
                `sorry-we-proved-source-edited`, `deleted-by-source`, `added-by-both`, `other`
A file only we changed is kept as it is. `apply` writes every file except the conflicts and exits 3 when a conflict
is left (0 otherwise); `plan` exits the same way and writes nothing.
The layout files (ADAPTED: lakefile.toml) are merged the same way; `blueprint` and `.gitmodules` are not adopted.

It also prints what the source removed that we use: declarations (by name, read from the source text of the changed
files) that the base declared and the tip does not, and are named in lean/Sheaf or in a node's `lean` record.
"""
from __future__ import annotations
import collections, json, os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(os.environ.get("UPSTREAM_MERGE_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
SRC = ROOT                                                   # the git repository holding <base> and <tip>
LEAN = ROOT / "lean"
NOT_ADOPTED = ("blueprint", ".gitmodules", ".github", ".gitignore")
# the modules another team proves (roles: the two target modules of proper base change): always the source's file
ALWAYS_THEIRS = (
    "WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/ProjectiveLine.lean",
    "WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/BaseChangeProperty.lean",
)
IMPORT = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(\S+)")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|unsafe|partial|nonrec|scoped|local)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([^\s({\[:]+)")


def git(*a, text=True, check=True):
    r = subprocess.run(["git", "-C", str(SRC), *a], capture_output=True, text=text)
    if check and r.returncode:
        sys.exit(f"git {' '.join(a)}: {r.stderr.strip() if text else r.stderr.decode().strip()}")
    return r.stdout


def tree(rev):
    out = {}
    for l in git("ls-tree", "-r", rev).splitlines():
        meta, p = l.split("\t", 1)
        mode, typ, sha = meta.split()
        if typ == "blob" and not p.startswith(NOT_ADOPTED):
            out[p] = sha
    return out


def blob(sha):
    return git("cat-file", "blob", sha, text=False) if sha else None


def hash_bytes(b):
    return subprocess.run(["git", "hash-object", "--stdin"], input=b, capture_output=True).stdout.decode().strip()


def imports_of(text):
    return [m.group(1) for l in text.split("\n") if (m := IMPORT.match(l))]


def module_exists(m, tip_tree):
    p = m.replace(".", "/") + ".lean"
    return (LEAN / p).exists() or p in tip_tree or not m.split(".")[0] in ("Sheaf", "WeilConjectures")


def only_imports(base, ours):
    """Our added import lines when the file differs from the base by added import lines (and blank lines) only."""
    b, o = base.split("\n"), ours.split("\n")
    added = [l for l in o if IMPORT.match(l) and l not in b]
    rest_o = [l for l in o if l not in added]
    strip = lambda ls: [l for l in ls if l.strip()]
    return added if strip(rest_o) == strip(b) and added else None


def add_imports(theirs, lines, tip_tree):
    have = set(imports_of(theirs))
    keep = [l for l in lines if IMPORT.match(l).group(1) not in have and module_exists(IMPORT.match(l).group(1), tip_tree)]
    t = theirs.split("\n")
    last = max((i for i, l in enumerate(t) if IMPORT.match(l)), default=None)
    if last is None:
        return theirs, []
    t[last + 1:last + 1] = keep
    return "\n".join(t), keep


_NAMES, _IMPS = {}, {}


def _module(m):
    """(declared short names, imported modules of lean/) of a module of lean/, cached; None when it has no file here."""
    if m not in _NAMES:
        f = LEAN / (m.replace(".", "/") + ".lean")
        if not f.is_file():
            _NAMES[m] = None; _IMPS[m] = []
        else:
            t = f.read_text(errors="ignore")
            _NAMES[m] = {n.split(".")[-1] for n in decl_names(t)}
            # only `public import` passes declarations on to an importer (Lean's module system)
            _IMPS[m] = [x.group(1) for l in t.split("\n") if (x := re.match(r"^public\s+(?:meta\s+)?import\s+(\S+)", l))
                        and x.group(1).split(".")[0] in ("Sheaf", "WeilConjectures")]
    return _NAMES[m], _IMPS[m]


def _closure(roots):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or _module(m)[0] is None:
            continue
        seen.add(m); todo += _module(m)[1]
    return seen


def drop_unused_imports(text, theirs):
    """After the source's proof replaced ours: our own `import Sheaf.X` lines (not `public`, not the source's) are
    removed when the file names no declaration that only X brings: none of X, and none of the modules X imports
    (transitively, through `public import`) that the file's other imports do not reach. So what only our dropped proof needed leaves the
    targets' closure. By names, so a use without a name (an instance) is not seen: the build decides, and a module
    that then fails gets its import back by hand in the side copy. Returns (text, [modules dropped])."""
    src = set(theirs.split("\n"))
    lines = text.split("\n")
    body = "\n".join(l for l in lines if not IMPORT.match(l))
    words = set(re.findall(r"[^\s()\[\]{}⟨⟩,:.]+", body))
    dropped = []
    for l in list(lines):
        m = re.match(r"^import\s+(Sheaf\.\S+)\s*$", l)
        if not m or l in src or _module(m.group(1))[0] is None:
            continue
        others = [i for x in lines if x != l for i in imports_of(x)]
        only = _closure([m.group(1)]) - _closure(others)
        if not any(_module(x)[0] & words for x in only):
            lines.remove(l); dropped.append(m.group(1))
    return "\n".join(lines), dropped


def merge3(ours, base, theirs):
    with tempfile.TemporaryDirectory() as d:
        ps = []
        for n, b in (("ours", ours), ("base", base), ("theirs", theirs)):
            p = pathlib.Path(d) / n
            p.write_bytes(b)
            ps.append(str(p))
        r = subprocess.run(["git", "merge-file", "-p", "--diff3", "-L", "ours", "-L", "base", "-L", "source", *ps],
                           capture_output=True)
        return r.returncode, r.stdout


def describe_conflicts(merged: str):
    """(records, text): one record per conflict block of a diff3 merge (kind, the declaration it is in, the line),
    and the text with every block resolved by rule, or None when a block needs judgment."""
    lines, i, decl = merged.split("\n"), 0, None
    seg = []                                                 # plain lines (str) and blocks (dict)
    while i < len(lines):
        l = lines[i]
        if (m := DECL.match(l)):
            decl = m.group(2)
        if l.startswith("<<<<<<< "):
            o, b, t, part, start = [], [], [], "o", i
            i += 1
            while i < len(lines) and not lines[i].startswith(">>>>>>> "):
                x = lines[i]
                if x.startswith("||||||| "): part = "b"
                elif x == "=======": part = "t"
                else: {"o": o, "b": b, "t": t}[part].append(x)
                i += 1
            has = lambda ls: any(re.search(r"\bsorry\b", x) for x in ls)
            body = [x for x in o + b + t if x.strip()]
            if body and all(IMPORT.match(x) for x in body): kind = "imports"
            elif has(b) and not has(o) and not has(t): kind = "sorry-both"
            elif has(b) and has(o) and not has(t): kind = "sorry-source-proved"
            elif has(b) and not has(o) and has(t): kind = "sorry-we-proved-source-edited"
            else: kind = "other"
            seg.append({"kind": kind, "declaration": decl, "line": start + 1, "o": o, "b": b, "t": t})
        else:
            seg.append(l)
        i += 1
    blocks = [x for x in seg if isinstance(x, dict)]
    # lines both sides put in front of one declaration whose `sorry` both replaced: they go with the proof
    for n, x in enumerate(seg):
        if isinstance(x, dict) and x["kind"] == "other" and not [y for y in x["b"] if y.strip()]:
            between, nxt = [], None
            for y in seg[n + 1:]:
                if isinstance(y, dict): nxt = y; break
                between.append(y)
            if nxt and nxt["kind"] == "sorry-both" and sum(1 for y in between if DECL.match(y)) <= 1 \
                    and not any(y.startswith(("end ", "namespace ", "section")) for y in between):
                x["kind"] = "prefix"; x["declaration"] = nxt["declaration"] or next(
                    (DECL.match(y).group(2) for y in between if DECL.match(y)), None)
    for n, x in enumerate(seg):                              # a block inside a declaration header names it itself
        if isinstance(x, dict) and x["declaration"] is None:
            x["declaration"] = next((DECL.match(y).group(2) for y in x["o"] + x["t"] if DECL.match(y)), None)
    out, ok = [], True
    for x in seg:
        if isinstance(x, str): out.append(x); continue
        if x["kind"] in ("sorry-both", "prefix"): out += x["t"]
        elif x["kind"] == "imports":
            have = {IMPORT.match(y).group(1) for y in x["t"] if IMPORT.match(y)}
            mine = {IMPORT.match(y).group(1) for y in x["o"] if IMPORT.match(y)}
            if have <= mine: out += x["o"]                   # merged before
            else: out += x["t"] + [y for y in x["o"] if IMPORT.match(y) and IMPORT.match(y).group(1) not in have]
        else: ok = False
    recs = [{"kind": x["kind"], "declaration": x["declaration"], "line": x["line"], "ours": len(x["o"]),
             "base": len(x["b"]), "source": len(x["t"])} for x in blocks]
    return recs, ("\n".join(out) if ok else None)


def decl_names(text):
    """Declared names of a source text, with the namespaces in force (approximate: for the report only)."""
    names, ns = set(), []
    for l in text.split("\n"):
        s = l.strip()
        if s.startswith("namespace "):
            ns.append(s.split()[1])
        elif s.startswith("end ") and ns and s.split()[1] == ns[-1]:
            ns.pop()
        elif (m := DECL.match(l)):
            n = m.group(2)
            if n.startswith("_root_."): names.add(n[7:])
            else: names.add(".".join(ns + [n]))
    return names


def resolved_index(d):
    idx = {}
    if d and (d / "index.tsv").exists():
        for l in (d / "index.tsv").read_text().splitlines():
            f = l.split("\t")
            if len(f) >= 4 and not l.startswith("#"):
                idx[(f[0], f[1] or None, f[2] or None)] = f[3:]
    return idx


def statement(text, short):
    """The text of the declaration named `short` (last name component) up to its `:=`, spaces normalised."""
    m = re.search(r"^(?:theorem|lemma)\s+(?:[\w.]*\.)?" + re.escape(short) + r"\b(.*?):=", text, re.S | re.M)
    return " ".join(m.group(1).split()) if m else None


def targets(base, tip):
    ch = LEAN / "Challenge.lean"
    names = re.findall(r"^theorem\s+([^\s({\[:]+)", ch.read_text(), re.M) if ch.exists() else []
    if not names:
        print("TARGETS: no target statements found in lean/Challenge.lean")
        return 4
    B, T = tree(base), tree(tip)
    bad = 0
    for n in names:
        short = n.split(".")[-1]
        found = {}
        for side, tr in (("base", B), ("tip", T)):
            for p, sha in tr.items():
                if p.endswith(".lean") and p.startswith("WeilConjectures/"):
                    data = blob(sha)
                    if short.encode() in data and (st := statement(data.decode(), short)) is not None:
                        found[side] = (p, st); break
        if "base" not in found or "tip" not in found:
            print(f"TARGET {n}: not found in the {'base' if 'base' not in found else 'tip'}"); bad += 1
        elif found["base"][1] != found["tip"][1]:
            print(f"TARGET {n}: the source CHANGED its statement ({found['tip'][0]})"); bad += 1
        else:
            print(f"target {n}: statement text unchanged ({found['tip'][0]}"
                  + ("" if found["base"][0] == found["tip"][0] else f", moved from {found['base'][0]}") + ")")
    return 4 if bad else 0


def release_gone(before, after):
    """Release vanished queue items using the claim tool's paths and log, without worker abandonment."""
    import fcntl
    sys.path.insert(0, str(ROOT / "tools"))
    import claim
    def items(path):
        return {line.split("\t")[0] for line in pathlib.Path(path).read_text().splitlines()
                if line and not line.startswith("#")}
    removed = items(before) - items(after)
    with (ROOT / "coord/.merge.lock").open("a") as merge:
        fcntl.flock(merge, fcntl.LOCK_EX)
        # Serialize against expired-claim takeover, and re-read ownership immediately before each unlink.
        with (claim.C / ".takeover").open("a") as takeover:
            fcntl.flock(takeover, fcntl.LOCK_EX)
            queued = {line.split("\t")[0] for line in (ROOT / "coord/queue.tsv").read_text().splitlines() if line and not line.startswith("#")}
            saved, changed_returns = {}, []
            for item in sorted(removed - queued):
                record = claim.read(item)
                if not record: continue
                who = record["who"]
                saved[item] = record
                claim.lock(item).unlink(missing_ok=True)
                claim.log(f"maintenance released {who}'s {item}: upstream sync proved or retired the item; no longer queued")
                if claim.drop_return_entries(who, item): changed_returns.append(f"coord/returns/{who}.md")
                print(f"released {who}: {item}", flush=True)
            folder = pathlib.Path(before).parent
            (folder / "claims-before.json").write_text(json.dumps(saved, indent=2) + "\n")
            if saved:
                paths = ["coord/deliveries.log", *changed_returns, *(str(claim.lock(item).relative_to(ROOT)) for item in saved)]
                tracked = subprocess.check_output(["git", "-C", str(ROOT), "ls-files", "--", *paths], text=True).splitlines()
                if tracked:
                    subprocess.run(["git", "-C", str(ROOT), "add", "--", *tracked], check=True)
                    if subprocess.run(["git", "-C", str(ROOT), "diff", "--cached", "--quiet", "--", *tracked]).returncode:
                        subprocess.run(["git", "-C", str(ROOT), "-c", "commit.template=", "commit", "-q", "-m", "Release queue claims closed or retired by upstream sync", "--trailer", "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *tracked], check=True)
                        (folder / "commit.claims").write_text(subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True))
            print(f"Released {len(saved)} obsolete claims; {len(removed & queued)} items still queued elsewhere retained.")
    return 0


def lean_code_mask(text):
    """Preserve code positions while blanking nested comments and string literals."""
    chars = list(text); i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                chars[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                chars[i] = " "; i += 1
                if i < len(text): chars[i] = " "; i += 1
            else:
                end = text[i] == '"'
                if text[i] != "\n": chars[i] = " "
                i += 1
                if end: string = False
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            chars[i:end] = " " * (end - i); i = end
        elif text.startswith("/-", i):
            chars[i:i+2] = "  "; depth = 1; i += 2
        elif text[i] == '"':
            chars[i] = " "; string = True; i += 1
        else: i += 1
    return "".join(chars)


def redirect_text(text, rel, mapping):
    import fnmatch
    changes = collections.Counter()
    def allowed(rule): return any(fnmatch.fnmatch(rel, p) for p in rule.get("paths", ["**"])) and not any(fnmatch.fnmatch(rel, p) for p in rule.get("exclude", []))
    def replace(pattern, make):
        nonlocal text
        masked = lean_code_mask(text)
        edits = [(m.start(), m.end(), make(m)) for m in pattern.finditer(masked)]
        for start, end, value in reversed(edits): text = text[:start] + value + text[end:]
    imports = mapping.get("imports", {}) if rel not in mapping.get("preserve_imports_in", []) else {}
    masked = lean_code_mask(text)
    edits = []
    for line in re.finditer(r"(?m)^[ \t]*(?:(?:public|meta|private)\s+)*import[ \t]+([^\n]*)", masked):
        start = line.start(1)
        for token in re.finditer(r"[\w.']+", line.group(1)):
            old = token.group()
            if old in imports:
                target = imports[old]; target = " ".join(target) if isinstance(target, list) else target
                edits.append((start + token.start(), start + token.end(), target))
                changes[f"import {old} -> {target}"] += 1
    for start, end, value in reversed(edits): text = text[:start] + value + text[end:]
    rules = {r["from"]: r["to"] for r in mapping.get("identifiers", []) if allowed(r)}
    if rules:
        pat = re.compile(r"(?<![\w.'])(" + "|".join(re.escape(n) for n in sorted(rules, key=len, reverse=True)) + r")(?![\w'])")
        def rename(m):
            old = m.group(); changes[f"name {old} -> {rules[old]}"] += 1; return rules[old]
        replace(pat, rename)
    for rule in mapping.get("term_predicates", []):
        if not allowed(rule): continue
        # Only a simple name/field chain is rewritten; arbitrary expressions require a typed repair.
        pat = re.compile(r"(?<![\w.'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\." + re.escape(rule["from"]) + r"(?![\w'])")
        def predicate(m):
            if m.group(1) in (rule["to"].rsplit(".", 1)[0], "_root_." + rule["to"].rsplit(".", 1)[0]): return m.group()
            changes[f"predicate .{rule['from']} -> {rule['to']}"] += 1
            return f"({rule['to']} {m.group(1)})"
        replace(pat, predicate)
    for rule in mapping.get("implicit_first_arguments", []):
        if not allowed(rule) or rule["name"] not in text: continue
        masked = lean_code_mask(text); edits = []
        pattern = re.compile(r"(?<![\w'.])" + re.escape(rule["name"]) + r"(?![\w'.])")
        for match in pattern.finditer(masked):
            line_start = masked.rfind("\n", 0, match.start()) + 1
            if re.match(r"\s*attribute\b", masked[line_start:match.start()]): continue
            pos = match.end()
            # Only an actual same-line application; a bare reference or attribute
            # must not consume the next command, including intervening comments.
            while pos < len(masked) and masked[pos] in " \t": pos += 1
            start = pos
            if pos < len(masked) and masked[pos] == "(":
                depth = 1; pos += 1
                while pos < len(masked) and depth:
                    if masked[pos] == "(": depth += 1
                    elif masked[pos] == ")": depth -= 1
                    pos += 1
                if depth: continue
                value = text[start:pos]
                if re.match(r"\(\s*[\w']+\s*:=", value): continue
            else:
                arg = re.match(r"[\w']+(?:\.[\w']+)*", masked[pos:])
                if not arg: continue
                pos += len(arg.group()); value = text[start:pos]
            edits.append((match.end(), pos, " (" + rule["argument"] + " := " + value + ")"))
            changes["implicit argument " + rule["name"]] += 1
        for start, end, value in reversed(edits): text = text[:start] + value + text[end:]
    # Bundle Scheme morphisms/squares using the canonical over-category API. This
    # retains the caller's Scheme-level hypotheses and the exact exchange map.
    over_edits = []
    for rule in mapping.get("over_applications", []):
        if not allowed(rule) or rule["name"] not in text: continue
        masked = lean_code_mask(text)
        def argument(pos):
            while pos < len(masked) and masked[pos].isspace(): pos += 1
            start = pos
            if pos >= len(masked): raise ValueError("missing argument")
            if masked[pos] in "([{":
                stack = [masked[pos]]; pos += 1
                while stack:
                    if masked[pos] in "([{": stack.append(masked[pos])
                    elif masked[pos] in ")]}": stack.pop()
                    pos += 1
            else:
                match = re.match(r"[\w'.]+", masked[pos:])
                if not match: raise ValueError("not an atomic argument")
                pos += len(match.group())
            return pos, text[start:pos]
        for match in re.finditer(r"(?<![\w'.])" + re.escape(rule["name"]) + r"(?![\w'])", masked):
            try:
                pos, coefficient = argument(match.end())
                pos, ell = argument(pos); pos, field = argument(pos)
                if ell != "ℓ" or field != "k": continue
                values = []
                for _ in range(rule["arity"]):
                    pos, value = argument(pos); values.append(value)
                replacement = match.group() + " " + coefficient + " ℓ " + " ".join(
                    "(" + value + ".asOver (Spec (.of k)))" for value in values)
                over_edits.append((match.start(), pos, replacement))
                changes["over application " + rule["name"]] += 1
            except (ValueError, IndexError): continue
    for start, end, replacement in sorted(over_edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    if over_edits and "import Sheaf.AlgebraicGeometry.OverSquare" not in text:
        text = text.replace("module\n", "module\n\npublic import Sheaf.AlgebraicGeometry.OverSquare\n", 1)
    for rule in mapping.get("structural_witnesses", []):
        if not allowed(rule): continue
        for chooser, theorem in (("choose_spec", "strictHenselizationStructuralMap_eq"), ("choose", "strictHenselizationStructuralMap")):
            pat = re.compile(r"(?<![\w.'])Classical\." + chooser + r"\s*\(\s*(?P<ns>(?:AlgebraicGeometry\.)?Scheme\.)?exists_strictHenselizationStructuralMap\s+(?P<arg>[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\s*\)")
            def witness(m):
                changes[f"witness Classical.{chooser} -> {theorem}"] += 1
                return f"{m.group('ns') or ''}{theorem} {m.group('arg')}"
            replace(pat, witness)
    return text, dict(changes)


KNOWN_MAP_KEYS = {"version", "source_tip", "reason", "notes", "node_declarations", "preserve_imports_in", "imports",
                  "identifiers", "term_predicates", "implicit_first_arguments", "over_applications", "structural_witnesses"}


def quick_filter(mapping):
    """A test `text -> bool` that is False only when redirect_text(text, ...) certainly changes nothing (2026-10-20, hot
    path of the scheduled sync: 452 s for 23k files, almost all in lean_code_mask). Every rule matches a fixed name
    delimited by non-name characters: an old import, an identifier, a rule name or a structural witness is a dot-prefix
    of a name token of the text (a maximal run of [\\w.']), a predicate field is a dot-component of one. One token scan
    and two set intersections per file. A map with a rule kind not known here disables the filter."""
    if set(mapping) - KNOWN_MAP_KEYS:
        return lambda text: True
    prefixes = set(mapping.get("imports", {}))
    prefixes |= {r["from"] for r in mapping.get("identifiers", [])}
    prefixes |= {r["name"] for r in mapping.get("implicit_first_arguments", [])}
    prefixes |= {r["name"] for r in mapping.get("over_applications", [])}
    if mapping.get("structural_witnesses"):
        prefixes.add("exists_strictHenselizationStructuralMap")
    fields = {r["from"] for r in mapping.get("term_predicates", [])}
    return _token_filter(prefixes, fields)


def _token_filter(prefixes: set[str], fields: set[str]):
    prefixes = {w for w in prefixes if w}; fields = {w for w in fields if w}
    tok = re.compile(r"[\w.']+")

    def hit(text: str) -> bool:
        for t in set(tok.findall(text)):
            parts = t.split(".")
            if fields and not fields.isdisjoint(parts):
                return True
            acc = ""
            for p in parts:
                acc = p if not acc else acc + "." + p
                if acc in prefixes:
                    return True
        return False
    return hit


def migrate(args):
    import argparse
    parser = argparse.ArgumentParser(description="Apply reviewed canonical imports and Lean identifier redirects")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--map", default=str(ROOT / "coord/upstream-migrations.json"))
    parser.add_argument("--target-lean", default=str(LEAN))
    parser.add_argument("--json")
    opt = parser.parse_args(args)
    map_path = pathlib.Path(opt.map)
    if not map_path.is_file():
        print("canonical migrations: no map; no changes")
        if opt.json: pathlib.Path(opt.json).write_text(json.dumps({"files": []}) + "\n")
        return 0
    mapping = json.loads(map_path.read_text())
    if mapping.get("version") != 1: raise ValueError("unsupported canonical migration map version")
    target = pathlib.Path(opt.target_lean)
    for old, values in mapping.get("imports", {}).items():
        values = values if isinstance(values, list) else [values]
        for value in values:
            # 2026-10-21: a destination sitting in quarantine (tools/rework.py) is still the canonical module; the
            # scheduled sync stopped on LowerShriek.CompactlySupported, quarantined as a collateral of a red build
            if not (target / (value.replace(".", "/") + ".lean")).is_file() and \
                    not (ROOT / "quarantine" / (value.replace(".", "/") + ".lean")).is_file():
                sys.exit(f"canonical migration destination missing for {old}: {value}")
    files = set(LEAN.glob("*.lean"))
    for root in ("Sheaf", "WeilConjectures", "Comparator"): files.update((LEAN / root).rglob("*.lean"))
    report, writes = {"map": str(map_path), "files": []}, []
    # 2026-10-20 (scheduled sync, hot path: 452 s for 23k files, almost all in lean_code_mask): every rule of
    # redirect_text rewrites only a match of a fixed string (an old import name, an identifier, a predicate field, a
    # rule name), so a file containing none of them is returned unchanged; skip it before masking.
    hit = quick_filter(mapping)
    for f in sorted(files):
        before = f.read_text()
        if not hit(before):
            continue
        after, changes = redirect_text(before, str(f.relative_to(LEAN)), mapping)
        if after != before:
            report["files"].append({"path": str(f.relative_to(ROOT)), "before": hash_bytes(before.encode()), "after": hash_bytes(after.encode()), "changes": changes})
            writes.append((f, after))
    # DAG pointers use exact reviewed qualified names. Statements and removed, non-equivalent
    # theorems are never rewritten; any module move must be explicitly recorded with its name.
    node_rules = mapping.get("node_declarations", {})
    node_hit = _token_filter(set(node_rules), set())   # a rule rewrites only a node naming one of its declarations
    for f in sorted((ROOT / "dag/nodes").rglob("*.json")):
        before = f.read_text()
        if not node_hit(before):
            continue
        node = json.loads(before); record = node.get("lean")
        if not isinstance(record, dict): continue
        changes = {}
        old = record.get("declaration")
        if isinstance(old, str) and old in node_rules:
            rule = node_rules[old]; rule = {"declaration": rule} if isinstance(rule, str) else rule
            record["declaration"] = rule["declaration"]
            if "module" in rule:
                record["module"] = rule["module"]
                if "file" in record:
                    record["file"] = "lean/" + rule["module"].replace(".", "/") + ".lean"
            if "statement" in rule: record["statement"] = rule["statement"]
            changes[old] = rule["declaration"]
        values = record.get("declarations")
        if isinstance(values, list):
            renamed = []
            for old in values:
                if isinstance(old, str) and old in node_rules:
                    rule = node_rules[old]; target = rule if isinstance(rule, str) else rule["declaration"]
                    renamed.append(target); changes[old] = target
                else: renamed.append(old)
            record["declarations"] = renamed
        if changes:
            after = json.dumps(node, ensure_ascii=False, indent=1) + "\n"
            report["files"].append({"path": str(f.relative_to(ROOT)), "kind": "dag-pointer", "before": hash_bytes(before.encode()), "after": hash_bytes(after.encode()), "changes": changes})
            writes.append((f, after))
    if opt.apply:
        for f, text in writes: f.write_text(text)
    if opt.json: pathlib.Path(opt.json).write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"canonical migrations: {len(writes)} source/node files {'adapted' if opt.apply else 'need adaptation'}")
    for f, _ in writes: print("  " + str(f.relative_to(ROOT)))
    return 0


def source_cycles(args):
    import argparse
    parser = argparse.ArgumentParser(description="Check combined upstream/own source imports without compiling")
    parser.add_argument("--json")
    opt = parser.parse_args(args)
    files = set(LEAN.glob("*.lean"))
    for root in ("Sheaf", "WeilConjectures", "Comparator"): files.update((LEAN / root).rglob("*.lean"))
    modules, edges, positions, legacy = {}, {}, {}, []
    for f in sorted(files):
        rel = f.relative_to(LEAN).with_suffix("")
        if rel.parts[0] == "Comparator": rel = pathlib.Path(*rel.parts[1:])
        name = ".".join(rel.parts)
        modules[name] = str(f.relative_to(ROOT)); edges[name] = set()
        source = lean_code_mask(f.read_text())
        if rel.parts[0] == "Sheaf":
            for field in re.finditer(r"(?m)^[ \t]+antitone_step[ \t]*:=", source):
                legacy.append({"file": str(f.relative_to(ROOT)), "line": source.count("\n", 0, field.start()) + 1})
        for line in re.finditer(r"(?m)^[ \t]*(?:(?:public|meta|private)[ \t]+)*import[ \t]+([^\n]*)", source):
            for token in re.finditer(r"[\w.']+", line.group(1)):
                target = token.group()
                if target == "all": continue
                edges[name].add(target)
                positions[(name, target)] = source.count("\n", 0, line.start()) + 1
    missing = [{"from": n, "to": t, "file": modules[n], "line": positions[(n, t)]}
               for n in sorted(edges) for t in sorted(edges[n])
               if t.split(".")[0] in ("Sheaf", "WeilConjectures", "Weil") and t not in modules]
    sys.setrecursionlimit(max(10000, 2 * len(modules) + 1000))
    index, low, stack, on_stack, components = {}, {}, [], set(), []
    def visit(n):
        index[n] = low[n] = len(index); stack.append(n); on_stack.add(n)
        for target in sorted(edges[n] & modules.keys()):
            if target not in index: visit(target); low[n] = min(low[n], low[target])
            elif target in on_stack: low[n] = min(low[n], index[target])
        if low[n] == index[n]:
            component = set()
            while True:
                target = stack.pop(); on_stack.remove(target); component.add(target)
                if target == n: break
            if len(component) > 1 or n in edges[n]: components.append(component)
    for name in sorted(modules):
        if name not in index: visit(name)
    cycles = []
    for component in components:
        active, path, visited = {}, [], set()
        def find(n):
            visited.add(n); active[n] = len(path); path.append(n)
            for target in sorted(edges[n] & component):
                if target in active: return path[active[target]:] + [target]
                if target not in visited:
                    found = find(target)
                    if found: return found
            path.pop(); active.pop(n)
            return None
        cycle = find(min(component))
        cycles.append({"modules": cycle, "edges": [{"from": a, "to": b, "file": modules[a], "line": positions[(a, b)]} for a, b in zip(cycle, cycle[1:])]})
    report = {"modules": len(modules), "cycles": cycles, "missing": missing, "legacy_constructors": legacy}
    if opt.json: pathlib.Path(opt.json).write_text(json.dumps(report, indent=2) + "\n")
    print(f"source import graph: {len(modules)} modules; {len(cycles)} cycles; {len(missing)} missing project imports; {len(legacy)} legacy filtration constructors")
    for cycle in cycles[:20]:
        print("  cycle: " + " -> ".join(cycle["modules"]))
        for edge in cycle["edges"]: print(f"    {edge['file']}:{edge['line']} imports {edge['to']}")
    for edge in missing[:20]: print(f"  missing: {edge['file']}:{edge['line']} imports {edge['to']}")
    for field in legacy: print(f"  legacy constructor: {field['file']}:{field['line']}; replace typed DecreasingFiltration step/antitone_step fields with canonical F/F_succ_le and a successor-order proof")
    return 1 if cycles or missing or legacy else 0


def main():
    global SRC
    a = sys.argv[1:]
    if a and a[0] == "cycles":
        return source_cycles(a[1:])
    if a and a[0] == "migrate":
        return migrate(a[1:])
    if len(a) >= 3 and a[0] == "release-gone":
        return release_gone(a[1], a[2])
    if len(a) < 3 or a[0] not in ("plan", "apply", "targets"):
        sys.exit(__doc__)
    mode, base, tip = a[0], a[1], a[2]
    opt = dict(zip(a[3::2], a[4::2]))
    if "--source-git" in opt:
        SRC = pathlib.Path(opt["--source-git"])
    if mode == "targets":
        return targets(base, tip)
    rdir = pathlib.Path(opt["--resolved"]) if "--resolved" in opt else None
    ridx = resolved_index(rdir)
    B, T = tree(base), tree(tip)
    rep = {"base": git("rev-parse", base).strip(), "tip": git("rev-parse", tip).strip(), "files": [], "removed_used": []}
    count = collections.Counter()
    writes = []                                              # (path, bytes or None)
    for p in sorted(set(B) | set(T)):
        b, t = B.get(p), T.get(p)
        if b == t:
            continue
        f = LEAN / p
        ours = f.read_bytes() if f.exists() else None
        o = hash_bytes(ours) if ours is not None else None
        rec = {"path": p, "ours": o, "tip": t, "base": b}
        if o == t:
            rec["class"] = "same"
        elif o == b:
            rec["class"] = "take"; writes.append((p, blob(t)))
        elif p in ALWAYS_THEIRS:
            rec["class"] = "theirs-rule"; writes.append((p, blob(t)))
        elif ours is None and b is not None:
            # we deleted a file the source changed (a module of ours replaced it): keep it deleted, say so
            rec["class"] = "deleted-here"
        elif t is None:
            if (p, o, t) in ridx:
                rec["class"] = "resolved"; rec["choice"] = ridx[(p, o, t)]
                writes.append((p, (rdir / p).read_bytes()))
            else:
                rec["class"] = "conflict"; rec["conflicts"] = [{"kind": "deleted-by-source", "declaration": None, "line": 0}]
        elif b is None:
            if (p, o, t) in ridx:
                rec["class"] = "resolved"; rec["choice"] = ridx[(p, o, t)]
                writes.append((p, (rdir / p).read_bytes()))
            else:
                rec["class"] = "conflict"; rec["conflicts"] = [{"kind": "added-by-both", "declaration": None, "line": 0}]
        else:
            bt, ot, tt = blob(b).decode(), ours.decode(), blob(t).decode()
            lines = only_imports(bt, ot)
            if lines is not None:
                new, kept = add_imports(tt, lines, T)
                rec["class"] = "imports"; rec["imports_kept"] = [IMPORT.match(l).group(1) for l in kept]
                rec["imports_dropped"] = [IMPORT.match(l).group(1) for l in lines if l not in kept]
                writes.append((p, new.encode()))
            else:
                rc, merged = merge3(ours, blob(b), blob(t))
                if rc == 0:
                    rec["class"] = "merged"; writes.append((p, merged))
                elif (p, o, t) in ridx:
                    rec["class"] = "resolved"; rec["choice"] = ridx[(p, o, t)]
                    writes.append((p, (rdir / p).read_bytes()))
                else:
                    recs, text = describe_conflicts(merged.decode(errors="replace"))
                    rec["conflicts"] = recs
                    if text is not None:
                        if any(c["kind"] == "sorry-both" for c in recs):     # only when a proof of ours was replaced now
                            text, rec["imports_unused"] = drop_unused_imports(text, tt)
                        rec["class"] = "source-proof"; writes.append((p, text.encode()))
                    else:
                        rec["class"] = "conflict"
        if writes and writes[-1][0] == p and writes[-1][1] == ours and rec["class"] not in ("take", "theirs-rule"):
            writes.pop(); rec["class"] = "same"              # merged before: running again changes nothing
        count[rec["class"]] += 1
        rep["files"].append(rec)

    # declarations the source removed (or renamed, or moved out of the changed files) that we name
    gone = set()
    newnames = set()
    for p in sorted(set(B) | set(T)):
        if not p.endswith(".lean") or B.get(p) == T.get(p):
            continue
        nb = decl_names(blob(B[p]).decode()) if p in B else set()
        nt = decl_names(blob(T[p]).decode()) if p in T else set()
        gone |= nb - nt; newnames |= nt - nb
    gone -= newnames                                         # moved between changed files
    if gone:
        pat = re.compile(r"(?<![\w.'])(" + "|".join(re.escape(g) for g in sorted(gone, key=len, reverse=True)) + r")(?![\w'])")
        used = collections.defaultdict(set)
        for q in sorted((LEAN / "Sheaf").rglob("*.lean")):
            for m in pat.finditer(q.read_text()):
                used[m.group(1)].add(str(q.relative_to(ROOT)))
        for q in sorted((ROOT / "dag" / "nodes").glob("*/*.json")):
            try: n = json.loads(q.read_text())
            except Exception: continue
            l = n.get("lean") or {}
            ds = [l.get("declaration")] + list(l.get("declarations") or []) if isinstance(l, dict) else []
            for d in ds:
                d = d.get("name") if isinstance(d, dict) else d
                if d in gone: used[d].add("node " + n.get("id", q.stem))
        rep["removed_used"] = [{"declaration": g, "used_by": sorted(u)} for g, u in sorted(used.items())]
    rep["removed"] = len(gone)

    if mode == "apply":
        for p, data in writes:
            f = LEAN / p
            if data is None:
                if f.exists(): f.unlink()
            else:
                f.parent.mkdir(parents=True, exist_ok=True)
                tmp = f.with_name(f.name + ".upstream-new"); tmp.write_bytes(data); tmp.replace(f)
    kept = sum(1 for p in B if B.get(p) == T.get(p) and (LEAN / p).exists() and hash_bytes((LEAN / p).read_bytes()) != B[p]) \
        if "--count-kept" in a else None
    rep["counts"] = dict(count)
    if "--json" in opt:
        pathlib.Path(opt["--json"]).write_text(json.dumps(rep, indent=1))
    print(f"source {rep['base'][:9]} -> {rep['tip'][:9]}: {sum(count.values())} files changed by the source; "
          + ", ".join(f"{k} {v}" for k, v in sorted(count.items())) + (f"; ours kept {kept}" if kept is not None else ""))
    for r in rep["files"]:
        if r["class"] in ("imports", "merged", "resolved", "theirs-rule", "deleted-here"):
            extra = ""
            if r["class"] == "imports":
                extra = f": kept {len(r['imports_kept'])} import(s)" + (f", dropped {r['imports_dropped']}" if r["imports_dropped"] else "")
            if r["class"] == "resolved": extra = ": " + " | ".join(r["choice"])
            print(f"  {r['class']:12} {r['path']}{extra}")
    for r in rep["files"]:
        if r["class"] in ("conflict", "source-proof"):
            print(f"  {'CONFLICT' if r['class'] == 'conflict' else 'source-proof':12} {r['path']}")
            for c in r["conflicts"]:
                print(f"      {c['kind']:30} {c.get('declaration') or '-'}  (line {c['line']} of the diff3 merge; ours {c.get('ours', 0)} lines, source {c.get('source', 0)})")
            for m in r.get("imports_unused") or []:
                print(f"      import dropped (only our replaced proof used it): {m}")
    if rep["removed_used"]:
        print(f"declarations the source no longer declares in the files it changed, named by us ({len(rep['removed_used'])} of {rep['removed']}):")
        for r in rep["removed_used"]:
            print(f"  {r['declaration']}: {', '.join(r['used_by'][:6])}{' ...' if len(r['used_by']) > 6 else ''}")
    else:
        print(f"declarations the source no longer declares in the files it changed: {rep['removed']}; none named in lean/Sheaf or in a node's lean record")
    return 3 if count["conflict"] else 0


if __name__ == "__main__":
    sys.exit(main())
