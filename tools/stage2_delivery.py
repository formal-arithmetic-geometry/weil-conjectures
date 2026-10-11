#!/usr/bin/env python3
"""The checks of a stage-2 delivery (stages/2-statements.md; format decided by the lead, 2026-10-11), shared by
tools/preflight_delivery.py --stage 2, tools/review_packet.py --stage 2 and tools/merge_delivery.py --stage 2.

A delivery branch deliver/<G>/<item> is ONE commit on top of sheaf-dag with only:
  (1) the module lean/Sheaf/<Topic>/<Name>.lean (module Sheaf.<Topic>.<Name>; the declarations inside carry no
      `Sheaf.` prefix), or no Lean file when the node is an existing declaration of Mathlib or of the source;
  (2) the node file dag/nodes/<chapter>/<item>.json, changed only in `lean`:
      {module, declaration, declarations?, file?, statement, branch, by, date, existing} (`fixed_by`, the reviewer's
      id, is added by merge_delivery.py when a reviewer's fix changed the record);
  (3) coord/reports/<G>/<item>.md with `## Worker report` and `## Second reading by <G>`.

Failures are (letter, text) pairs; the letters are the ones of the stage-2 preflight:
  a commit and files, b node and record, c the Lean file, d an existing declaration, e the report, f the compile.

    python3 tools/stage2_delivery.py signature <file.lean> <declaration>     print the statement the tools read
    python3 tools/stage2_delivery.py decls <file.lean>                       list the declarations the tools see
"""
from __future__ import annotations
import gzip, json, os, pathlib, re, shutil, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from node_fields import changed_fields_except, STAGE2_OWNS  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = pathlib.Path(os.environ.get("SHEAF_SOURCE_REPO", str(pathlib.Path.home() / "weil-conjectures-slopmaster2")))
KEYS = ("module", "declaration", "statement", "branch", "by", "date", "existing")
OPTIONAL = ("declarations", "file", "fixed_by")
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
MODULE = re.compile(r"^Sheaf(\.[A-Za-z_][A-Za-z0-9_']*){2,}$")
IMPORT_OK = ("Mathlib.", "WeilConjectures.", "Sheaf.")


# ---------------------------------------------------------------- reading Lean text

def mask(text: str) -> str:
    """`text` with the contents of comments, docstrings and strings replaced by spaces (newlines and the comment
    delimiters `--`, `/-`, `/--`, `/-!`, `-/` kept), so that positions stay those of the original."""
    out = list(text)
    n = len(text)
    i = 0

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i + 2, j)
            i = j
        elif text.startswith("/-", i):
            k = i + 2
            if k < n and text[k] in "-!":
                k += 1
            start, depth = k, 1
            while k < n and depth:
                if text.startswith("/-", k):
                    depth += 1; k += 2
                elif text.startswith("-/", k):
                    depth -= 1; k += 2
                else:
                    k += 1
            blank(start, k - 2 if depth == 0 else k)
            i = k
        elif text[i] == '"':
            k = i + 1
            while k < n and text[k] != '"':
                k += 2 if text[k] == "\\" else 1
            blank(i + 1, k)
            i = k + 1
        else:
            i += 1
    return "".join(out)


HEAD = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]\n]*\][ \t\n]*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)[ \t]+)*)"
    r"(?P<kw>theorem|lemma|def|abbrev|structure|class(?:[ \t]+inductive)?|instance|inductive|opaque|axiom)\b[ \t]*"
    r"(?:\(priority[^)]*\)[ \t]*)?(?P<name>«[^»]*»|[^\s:(\[{⦃]+)?", re.M)
SCOPE = re.compile(r"^(?:noncomputable[ \t]+)?(?P<k>namespace|section|end)\b[ \t]*(?P<n>[^\s]*)", re.M)
STARTER = re.compile(r"^(?:[A-Za-z_@#«]|/-)", re.M)
NOT_STARTER = re.compile(r"^(?:where|deriving|with|termination_by|decreasing_by)\b")
OPEN = re.compile(r"^[ \t]*open[ \t]+([^\n]*)", re.M)
THEOREM_KW = ("theorem", "lemma")


def normalize(s: str) -> str:
    return " ".join((s or "").split())


def declarations(text: str) -> list[dict]:
    """The declarations of a Lean file: [{name (full), short, kw, start, kw_pos, sig_end, end, statement, body,
    docstring}]; anonymous instances have name None."""
    m = mask(text)
    events = [(x.start(), "scope", x) for x in SCOPE.finditer(m)] + [(x.start(), "decl", x) for x in HEAD.finditer(m)]
    events.sort(key=lambda e: e[0])
    starts = [x.start() for x in STARTER.finditer(m) if not NOT_STARTER.match(m, x.start())]
    stack: list[tuple[str, str]] = []
    out = []
    for pos, kind, x in events:
        if kind == "scope":
            k, nm = x.group("k"), x.group("n")
            if k == "namespace":
                stack.append(("namespace", nm))
            elif k == "section":
                stack.append(("section", nm))
            elif stack:
                stack.pop()
            continue
        kw_pos = x.start("kw")
        line_start = m.rfind("\n", 0, kw_pos) + 1
        end = next((s for s in starts if s > kw_pos and s > line_start), len(m))
        # the signature: up to `:=`, `where` or `|` at bracket depth 0
        depth, k, sig_end = 0, x.end(), None
        while k < end:
            c = m[k]
            if c in "([{⦃⟨":
                depth += 1
            elif c in ")]}⦄⟩":
                depth -= 1
            elif depth == 0:
                if m.startswith(":=", k) or (c == "|" and m[k - 1] in " \n\t"):
                    sig_end = k; break
                if m.startswith("where", k) and not (m[k - 1].isalnum() or m[k - 1] in "_.'") and \
                        (k + 5 >= len(m) or not (m[k + 5].isalnum() or m[k + 5] in "_'")):
                    sig_end = k; break
            k += 1
        if sig_end is None:
            sig_end = end
        name = x.group("name")
        if name:
            name = name.strip("«»") if name.startswith("«") else name
            ns = ".".join(nm for kd, nm in stack if kd == "namespace" and nm)
            full = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
        else:
            full = None
        doc = None
        before = m[:x.start()].rstrip()
        if before.endswith("-/"):
            o = before.rfind("/--")
            if o >= 0 and before.rfind("/-!", o) < 0:
                doc = text[o:len(before)]
        out.append({"name": full, "short": name, "kw": " ".join(x.group("kw").split()), "start": x.start(),
                    "kw_pos": kw_pos, "sig_end": sig_end, "end": end,
                    "statement": normalize(text[kw_pos:sig_end]), "body": m[sig_end:end], "docstring": doc})
    return out


def imports(text: str) -> list[str]:
    return re.findall(r"^import[ \t]+(\S+)", mask(text), re.M)


def opens(text: str) -> list[str]:
    out = []
    for line in OPEN.findall(mask(text)):
        for w in line.split():
            if w in ("in", "scoped", "hiding", "renaming") or w.startswith("("):
                break
            out.append(w)
    return out


def check_lean_text(text: str, rec: dict, item: str, check_statement: bool = True) -> tuple[list[tuple[str, str]], dict | None]:
    """Check (c) on the text of the module. Returns (failures, the declaration found or None)."""
    fails = []
    f = lambda s: fails.append(("c", s))  # noqa: E731
    for imp in imports(text):
        if not imp.startswith(IMPORT_OK):
            f(f"import {imp}: a module imports only Mathlib.*, WeilConjectures.* or Sheaf.*")
    for k, line in enumerate(text.split("\n"), 1):
        if len(line) > 100:
            f(f"line {k} has {len(line)} characters (at most 100)")
    decls = declarations(text)
    masked = mask(text)
    byname = {d["name"]: d for d in decls if d["name"]}
    for d in decls:
        where = f"{d['kw']} {d['name'] or '(anonymous)'}"
        if d["kw"] == "axiom":
            f(f"{where}: an axiom; a statement is a theorem with proof `sorry`")
        if re.search(r"\bsorry\b", masked[d["kw_pos"]:d["sig_end"]]):
            f(f"{where}: `sorry` inside the signature")
        if d["kw"] in THEOREM_KW:
            if not re.fullmatch(r":=\s*(?:by\s+)?sorry", d["body"].strip()):
                f(f"{where}: the proof is not `sorry` (stage 2 states; every theorem and lemma ends with `:= by sorry` or `:= sorry`)")
        elif re.search(r"\bsorry\b", d["body"]):
            f(f"{where}: `sorry` in the body of a {d['kw']}: a hollow definition (AGENTS.md §5); state the proof it needs as a theorem of its own")
    decl = rec.get("declaration")
    found = byname.get(decl) if isinstance(decl, str) else None
    if found is None:
        f(f"lean.declaration {decl!r} is not declared in the file (declared: {', '.join(list(byname)[:12]) or 'nothing'})")
    else:
        if not found["docstring"] or f"(blueprint: {item})" not in found["docstring"]:
            f(f"the docstring of {decl} does not contain `(blueprint: {item})`")
        if check_statement and normalize(rec.get("statement")) != found["statement"]:
            f(f"lean.statement differs from the signature in the file:\n      recorded: {normalize(rec.get('statement'))}\n      in file:  {found['statement']}")
    for extra in rec.get("declarations") or []:
        if isinstance(extra, str) and extra not in byname:
            f(f"lean.declarations names {extra}, which the file does not declare")
    for n in [decl] + [x for x in (rec.get("declarations") or []) if isinstance(x, str)]:
        if isinstance(n, str) and n in byname:
            hit = upstream_has(n)
            if hit:
                f(f"declaration name exists in Mathlib/source: {n} ({hit})")
    return fails, found


# ---------------------------------------------------------------- names of Mathlib and of the source

_NAMES: dict[str, set] | None = None
_MODULE_OF: dict[str, str] = {}


def _names() -> dict[str, set]:
    global _NAMES
    if _NAMES is not None:
        return _NAMES
    _NAMES = {"Mathlib": set(), "source": set()}
    p = ROOT / "local" / "library_names_mathlib.tsv.gz"
    if p.exists():
        with gzip.open(p, "rt", errors="ignore") as fh:
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                _NAMES["Mathlib"].add(parts[0])
                if len(parts) > 1:
                    _MODULE_OF[parts[0]] = parts[1]
    p = ROOT / "dag" / "lean_names_upstream.json"
    if p.exists():
        def walk(x):
            if isinstance(x, str):
                _NAMES["source"].add(x)
            elif isinstance(x, list):
                for y in x:
                    walk(y)
            elif isinstance(x, dict):
                for y in x.values():
                    walk(y)
        for part in json.loads(p.read_text()).values():
            if isinstance(part, dict):
                walk(part.get("names"))
                walk(part.get("matched_declarations"))
    for p in sorted((ROOT / "local").glob("sorry_map_slopmaster2_*.jsonl.gz")):
        with gzip.open(p, "rt", errors="ignore") as fh:
            for line in fh:
                try:
                    n = json.loads(line).get("n")
                except ValueError:
                    continue
                if n:
                    _NAMES["source"].add(n)
    return _NAMES


def upstream_has(name: str) -> str | None:
    for where, s in _names().items():
        if name in s:
            return {"Mathlib": "local/library_names_mathlib.tsv.gz",
                    "source": "the source repository (dag/lean_names_upstream.json / sorry map)"}[where]
    return None


def existing_file(module: str) -> pathlib.Path | None:
    rel = module.replace(".", "/") + ".lean"
    if module.startswith("Mathlib."):
        return SOURCE / ".lake" / "packages" / "mathlib" / rel
    if module.startswith("WeilConjectures."):
        return SOURCE / rel
    return None


def check_existing(rec: dict) -> tuple[list[tuple[str, str]], list[str]]:
    """Check (d). Returns (failures, notes)."""
    fails, notes = [], []
    mod, decl = str(rec.get("module") or ""), str(rec.get("declaration") or "")
    if not mod.startswith(("Mathlib.", "WeilConjectures.")):
        fails.append(("d", f"lean.existing is true but lean.module {mod!r} is neither Mathlib.* nor WeilConjectures.*"))
        return fails, notes
    want = "mathlib" if mod.startswith("Mathlib.") else "slopmaster2"
    if rec.get("branch") != want:
        fails.append(("d", f"lean.branch is {rec.get('branch')!r}; a declaration of {mod.split('.')[0]} has branch {want!r}"))
    p = existing_file(mod)
    if not SOURCE.is_dir():
        notes.append(f"existing declaration: not checked here (no source checkout {SOURCE}; set SHEAF_SOURCE_REPO)")
        return fails, notes
    if p is None or not p.exists():
        fails.append(("d", f"lean.module {mod}: no file {p}"))
        return fails, notes
    text = p.read_text(errors="ignore")
    short = decl.split(".")[-1]
    grep = re.search(r"\b(theorem|lemma|def|structure|class|abbrev|instance|inductive)\s+(?:[\w.'«»]*\.)?" + re.escape(short) + r"(?![\w.'])", text)
    if not grep and (_names() and _MODULE_OF.get(decl) == mod):
        notes.append(f"existing declaration: {decl} is not found by the grep in {p.name} (a structure field or a generated "
                     f"name) but local/library_names_mathlib.tsv.gz lists it in {mod}")
    elif not grep:
        fails.append(("d", f"{short} is not declared in {p} (grep for theorem|lemma|def|structure|class|abbrev|instance|inductive {short})"))
    else:
        hit = next((d for d in declarations(text) if d["name"] == decl), None)
        if hit is None:
            notes.append(f"existing declaration: {short} is declared in {p.name}, but the full name {decl} was not resolved by the reader (check the namespace)")
        elif normalize(rec.get("statement")) != hit["statement"]:
            notes.append(f"existing declaration: lean.statement differs from the signature in {p.name}: {hit['statement'][:300]}")
    return fails, notes


# ---------------------------------------------------------------- the delivery on a branch

class Git:
    def __init__(self, root: pathlib.Path = ROOT):
        self.root = root

    def run(self, *a, check=True) -> str:
        r = subprocess.run(["git", *a], cwd=self.root, capture_output=True, text=True)
        if check and r.returncode != 0:
            raise RuntimeError(f"git {' '.join(a[:3])}: {(r.stderr or r.stdout).strip()}")
        return r.stdout.rstrip("\n")

    def ok(self, *a) -> bool:
        return subprocess.run(["git", *a], cwd=self.root, capture_output=True).returncode == 0

    def show(self, ref, path):
        r = subprocess.run(["git", "show", f"{ref}:{path}"], cwd=self.root, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None

    def node_path(self, ref, item):
        out = self.run("ls-tree", "-r", "--name-only", ref, "--", "dag/nodes", check=False)
        return next((p for p in out.splitlines() if p.endswith(f"/{item}.json")), None)


def report_sections(text: str, group: str) -> tuple[str, str]:
    worker, second = "", ""
    for s in re.split(r"(?m)^## ", text or "")[1:]:
        head, _, body = s.partition("\n")
        if head.strip() == "Worker report":
            worker = body.strip()
        elif head.strip() == f"Second reading by {group}":
            second = body.strip()
    return worker, second


def check_record(rec, group) -> list[tuple[str, str]]:
    fails = []
    f = lambda s: fails.append(("b", s))  # noqa: E731
    if not isinstance(rec, dict):
        return [("b", f"the node's `lean` is {type(rec).__name__}, not a record {{{', '.join(KEYS)}, ...}}")]
    for k in KEYS:
        if k not in rec or rec[k] in (None, ""):
            f(f"lean has no {k}")
    extra = [k for k in rec if k not in KEYS + OPTIONAL]
    if extra:
        f(f"lean has key(s) outside the format: {', '.join(extra)}")
    if rec.get("by") != group:
        f(f"lean.by is {rec.get('by')!r}, not {group!r}")
    if rec.get("date") and not DATE.match(str(rec.get("date"))):
        f(f"lean.date {rec.get('date')!r} is not YYYY-MM-DD")
    if rec.get("existing") not in (True, False):
        f(f"lean.existing is {rec.get('existing')!r}; true or false")
    ds = rec.get("declarations")
    if ds is not None and not (isinstance(ds, list) and all(isinstance(x, str) for x in ds)):
        f("lean.declarations is not a list of names")
    if rec.get("existing") is False:
        mod = str(rec.get("module") or "")
        for n in [rec.get("declaration")] + list(ds or []):
            if isinstance(n, str) and n.startswith("Sheaf."):
                f(f"declaration {n}: names carry no `Sheaf.` prefix (only the module path is Sheaf.<Topic>.<Name>)")
        if not MODULE.match(mod):
            f(f"lean.module {mod!r} is not Sheaf.<Topic>.<Name>")
        want = "lean/" + mod.replace(".", "/") + ".lean"
        if rec.get("file") != want:
            f(f"lean.file is {rec.get('file')!r}; the module {mod} is the file {want}")
        if rec.get("branch") != "sheaf-dag":
            f(f"lean.branch is {rec.get('branch')!r}; a new module has branch 'sheaf-dag'")
    elif rec.get("existing") is True and "file" in rec:
        f("lean.existing is true but lean.file is set (an existing declaration delivers no file)")
    return fails


def read_delivery(git: Git, ref: str, base: str, group: str, item: str, max_commits: int = 1) -> dict:
    """Checks (a), (b), (c) without the compile, (d), (e) of the delivery `ref` against `base`.
    Returns {fails: [(letter, text)], notes, node_path, node, base_node, rec, lean_path, lean_text, report, decl}."""
    D = {"fails": [], "notes": [], "node_path": None, "node": None, "base_node": None, "rec": None,
         "lean_path": None, "lean_text": None, "report": None, "decl": None, "commits": []}
    fails = D["fails"]
    f = lambda L, s: fails.append((L, s))  # noqa: E731
    if not git.ok("rev-parse", "--verify", "-q", ref):
        f("a", f"no ref {ref}"); return D
    if not git.ok("rev-parse", "--verify", "-q", base):
        f("a", f"no ref {base}: run `git fetch origin` (or pass --base <ref>)"); return D
    commits = git.run("rev-list", "--reverse", f"{base}..{ref}").split()
    D["commits"] = commits
    if not commits:
        f("a", f"{ref} has no commit beyond {base} (the branch would deliver nothing)")
    elif len(commits) > max_commits:
        f("a", f"{len(commits)} commits beyond {base}: deliver one item as exactly one commit (squash with `git reset --soft {base}` and commit again)")
    if not git.ok("merge-base", "--is-ancestor", base, ref):
        f("a", f"{ref} is not on top of {base}: fetch, rebase onto {base}, and run again")
    node_path = git.node_path(ref, item)
    D["node_path"] = node_path
    report = f"coord/reports/{group}/{item}.md"
    if node_path is None:
        f("b", f"no node file for {item} on {ref}"); return D
    status = [l.split("\t") for l in git.run("diff", "--name-status", base, ref).splitlines() if l] if commits else []
    lean_files = []
    for st in status:
        code, p = st[0], st[-1]
        if code.startswith("D"):
            f("a", f"{p}: the delivery deletes a file"); continue
        if p in (node_path, report):
            continue
        if p.startswith("lean/") and p.endswith(".lean"):
            lean_files.append(p); continue
        if p.startswith("coord/claims/"):
            f("a", f"{p}: a claim lock file is in the delivery; claims are made with tools/claim.py on the server, never pushed")
        else:
            f("a", f"{p}: file outside the delivery (allowed: lean/Sheaf/<Topic>/<Name>.lean, {node_path}, {report})")
    changed = {st[-1] for st in status}
    if commits and node_path not in changed:
        f("b", "the node file is unchanged (the delivery sets its field `lean`)")
    if len(lean_files) > 1:
        f("a", f"{len(lean_files)} Lean files: one module per node ({', '.join(lean_files)})")
    # (b) the node
    try:
        node = json.loads(git.show(ref, node_path) or "")
    except ValueError as e:
        f("b", f"{node_path}: not valid JSON ({e})"); return D
    D["node"] = node
    base_text = git.show(base, node_path)
    if base_text is None:
        f("b", f"{node_path} does not exist on {base} (a stage-2 delivery states an existing node)")
        bnode = {}
    else:
        bnode = json.loads(base_text)
    D["base_node"] = bnode
    ch = changed_fields_except(bnode, node, STAGE2_OWNS) if base_text is not None else []
    if ch:
        f("b", f"the node changed in field(s) {', '.join(ch)}; a stage-2 delivery takes the node as it is on {base} and sets only `lean`")
    rec = node.get("lean")
    D["rec"] = rec
    rf = check_record(rec, group)
    fails.extend(rf)
    if not isinstance(rec, dict):
        rec = {}
    # (c) / (d)
    lf = rec.get("file")
    if rec.get("existing") is True:
        if lean_files:
            f("d", f"lean.existing is true but the commit has Lean file(s) {', '.join(lean_files)}")
        df, notes = check_existing(rec)
        fails.extend(df); D["notes"] += notes
    elif lf:
        if lean_files and lf not in lean_files:
            f("c", f"lean.file is {lf} but the commit's Lean file is {lean_files[0]}")
        if not lf.startswith("lean/Sheaf/"):
            f("c", f"lean.file {lf}: a module of the library is under lean/Sheaf/")
        text = git.show(ref, lf)
        if text is None:
            f("c", f"no file {lf} in {ref}")
        else:
            if lf not in lean_files:
                f("c", f"{lf} is not changed by the commit (the module is part of the delivery)")
            D["lean_path"], D["lean_text"] = lf, text
            cf, decl = check_lean_text(text, rec, item)
            fails.extend(cf); D["decl"] = decl
    elif lean_files:
        f("c", f"the commit has {lean_files[0]} but lean.file is not set")
    # (e) the report
    rt = git.show(ref, report)
    D["report"] = rt
    fails.extend(check_report(rt, group, report))
    return D


def check_report(rt: str | None, group: str, where: str) -> list[tuple[str, str]]:
    """Check (e) on the text of the report."""
    if rt is None:
        return [("e", f"no report {where}")]
    out = []
    w, s = report_sections(rt, group)
    if not w:
        out.append(("e", "the report has no non-empty section '## Worker report'"))
    if not s:
        out.append(("e", f"the report has no non-empty section '## Second reading by {group}'"))
    return out


def refit_record(text: str | None, rec: dict, override: dict | None = None, reviewer: str | None = None,
                 text_fixed: bool = False) -> tuple[dict, list[str], list[str]]:
    """The delivered `lean` record after a reviewer's fix (merge_delivery.py --stage 2 --apply-fixes).
    `override` (DIR/<item>.lean-record.json) is merged over `rec`, its keys winning except `by`, `date`, `fixed_by`.
    With a fixed Lean file (`text_fixed`, a new module): `statement` is re-read from the file (unless the override
    gives it) and `declarations` filtered to the names the file declares (unless the override gives it).
    `fixed_by` = reviewer when the record changed. Returns (record, notes, refusals)."""
    new, notes, refuse = dict(rec), [], []
    for k, v in (override or {}).items():
        if k in ("by", "date", "fixed_by"):
            if v != rec.get(k):
                notes.append(f"lean-record.json: key {k!r} ignored (stays {rec.get(k)!r})")
            continue
        new[k] = v
    if text_fixed and text is not None and new.get("existing") is not True:
        byname = {d["name"]: d for d in declarations(text) if d["name"]}
        decl = new.get("declaration")
        if decl not in byname:
            refuse.append(f"lean.declaration {decl!r} is not declared in the fixed file (declared: "
                          f"{', '.join(list(byname)[:12]) or 'nothing'}); give the new name in DIR/<item>.lean-record.json")
        elif "statement" not in (override or {}):
            new["statement"] = byname[decl]["statement"]
        ds = new.get("declarations")
        if isinstance(ds, list) and "declarations" not in (override or {}):
            keep = [x for x in ds if x in byname]
            dropped = [x for x in ds if x not in byname]
            if dropped:
                notes.append(f"lean.declarations: dropped {', '.join(map(str, dropped))} (not declared in the fixed file)")
            if keep:
                new["declarations"] = keep
            else:
                del new["declarations"]
    if new != rec:
        new["fixed_by"] = reviewer
    return new, notes, refuse


# ---------------------------------------------------------------- compiling

def compile_root() -> pathlib.Path:
    return pathlib.Path(os.environ.get("SHEAF_COMPILE_ROOT") or ROOT).resolve()


def can_compile(root: pathlib.Path) -> str | None:
    """None when tools/lean_file.sh can run in `root` on this machine, else the reason."""
    lean = root / "lean"
    if not (lean / "lakefile.toml").exists() or not (root / "tools" / "lean_file.sh").exists():
        return "no lean/ project"
    if not shutil.which("lake"):
        return "no lake on PATH"
    m = re.search(r'^packagesDir\s*=\s*"([^"]+)"', (lean / "lakefile.toml").read_text(), re.M)
    if m and not pathlib.Path(m.group(1)).is_dir():
        return f"no package directory {m.group(1)}"
    if not (lean / ".lake").is_dir():
        return "lean/.lake not built here"
    return None


def compile_text(text: str, group: str, item: str, root: pathlib.Path | None = None, timeout: int = 120) -> tuple[bool, int, str]:
    """Write `text` to lean/.sandbox/<group>/<item>.lean of `root` and compile it with tools/lean_file.sh.
    Returns (ran, exit code, output); ran is False when Lean does not run on this machine."""
    root = root or compile_root()
    why = can_compile(root)
    if why:
        return False, 0, f"compile: not run here (no Lean on this machine: {why}; use tools/compile_remote.sh on the server)"
    d = root / "lean" / ".sandbox" / group
    d.mkdir(parents=True, exist_ok=True)
    p = d / f"{item}.lean"
    p.write_text(text)
    env = dict(os.environ, SHEAF_GROUP=group, SHEAF_FILE_TIMEOUT=str(timeout))
    env.pop("SHEAF_TREE", None)
    r = subprocess.run(["bash", str(root / "tools" / "lean_file.sh"), str(p)], cwd=root, env=env, capture_output=True, text=True)
    return True, r.returncode, f"$ SHEAF_GROUP={group} SHEAF_FILE_TIMEOUT={timeout} tools/lean_file.sh {p}\n" + (r.stdout + r.stderr).strip()


# ---------------------------------------------------------------- declaration -> node

def nodes_at(git: Git, ref: str) -> dict[str, dict]:
    """Every node of dag/nodes on `ref`, read with one `git cat-file --batch`."""
    paths = [p for p in git.run("ls-tree", "-r", "--name-only", ref, "--", "dag/nodes").splitlines() if p.endswith(".json")]
    inp = "".join(f"{ref}:{p}\n" for p in paths)
    r = subprocess.run(["git", "cat-file", "--batch"], cwd=git.root, input=inp.encode(), capture_output=True)
    data, out, i = r.stdout, {}, 0
    for p in paths:
        j = data.index(b"\n", i)
        hdr = data[i:j].split()
        if len(hdr) < 3 or hdr[1] != b"blob":
            i = j + 1; continue
        size = int(hdr[2])
        body = data[j + 1:j + 1 + size]
        i = j + 1 + size + 1
        try:
            out[pathlib.PurePosixPath(p).stem] = json.loads(body)
        except ValueError:
            pass
    return out


def declaration_map(nodes: dict[str, dict]) -> dict[str, str]:
    """declaration -> node, from every node's `lean` (declaration, declarations) and `mathlib_match.declaration`."""
    m = {}
    for nid, d in nodes.items():
        l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
        mm = d.get("mathlib_match") if isinstance(d.get("mathlib_match"), dict) else {}
        for n in [l.get("declaration")] + list(l.get("declarations") or []) + [mm.get("declaration")]:
            if isinstance(n, dict):
                n = n.get("name")
            if isinstance(n, str) and n:
                m.setdefault(n, nid)
    return m


IDENT = re.compile(r"(?<![\w.'])[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")


def used_recorded(text: str, dmap: dict[str, str]) -> list[tuple[str, str, str]]:
    """(identifier as written, full name, node) for every identifier of the file that is a recorded declaration,
    resolving the namespaces opened in the file and the namespaces it is in."""
    m = mask(text)
    prefixes = set(opens(text))
    for x in SCOPE.finditer(m):
        if x.group("k") == "namespace" and x.group("n"):
            parts = x.group("n").split(".")
            for k in range(1, len(parts) + 1):
                prefixes.add(".".join(parts[:k]))
    out, seen = [], set()
    for tok in IDENT.findall(m):
        if tok in seen:
            continue
        seen.add(tok)
        for cand in [tok] + [f"{p}.{tok}" for p in sorted(prefixes)]:
            if cand in dmap:
                out.append((tok, cand, dmap[cand])); break
    return out


def main(argv: list[str]) -> int:
    if len(argv) >= 2 and argv[0] == "decls":
        for d in declarations(pathlib.Path(argv[1]).read_text()):
            print(f"{d['kw']}\t{d['name']}\t{d['statement'][:120]}")
        return 0
    if len(argv) >= 3 and argv[0] == "signature":
        d = next((d for d in declarations(pathlib.Path(argv[1]).read_text()) if d["name"] == argv[2]), None)
        print(d["statement"] if d else f"no declaration {argv[2]}")
        return 0 if d else 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
