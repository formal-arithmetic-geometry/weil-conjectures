#!/usr/bin/env python3
"""The checks of a stage-2 delivery (stages/2-statements.md; format decided by the lead, 2026-10-11), shared by
tools/preflight_delivery.py --stage 2, tools/review_packet.py --stage 2 and tools/merge_delivery.py --stage 2.

A delivery branch deliver/<G>/<item> is ONE commit on top of sheaf-dag with only:
  (1) the module lean/Sheaf/<Topic>/<Name>.lean (module Sheaf.<Topic>.<Name>; the declarations inside carry no
      `Sheaf.` prefix), or no Lean file when the node is an existing declaration of Mathlib, of the source, or of
      lean/Sheaf on the base (module Sheaf.*, branch sheaf-dag: another node of this project already states it);
  (2) the node file dag/nodes/<chapter>/<item>.json, changed only in `lean`:
      {module, declaration, declarations?, file?, statement, branch, by, date, existing, note?} (`fixed_by`, the
      reviewer's id, is added by merge_delivery.py when a reviewer's fix changed the record), and in `stmt_deps` only by
      adding new definition nodes of the delivery; or, under STAGE 2 STATEMENT CORRECTION (decision of the human,
      2026-10-11 06:22 UTC), CORRECTED: `statement` changed and, as far as forced, `stmt_deps`, `proof`, `proof_deps`,
      with a `statement_change` record (node_fields.check_statement_change; citers = the base nodes citing the item);
  (3) coord/reports/<G>/<item>.md with `## Worker report` and `## Second reading by <G>`, plus `## New nodes`,
      `## Dependency modules` and `## Statement corrected` when the delivery has them;
and, by the rule STAGE 2 EXTRA NODES (decision of the human, 2026-10-11 05:55 UTC; coord/STATE.md):
  (A) NEW DEFINITION NODES dag/nodes/<chapter of the item>/<id>.json, absent on the base, with the fields of
      check_new_node (kind definition, status split, created.item = the item, created.group = G, ...), each with its
      own module and `lean` record (or `existing: true` and no module), cited by the item;
  (B) DEPENDENCY MODULES: for a node in the item's stmt_deps on the base, its node file changed only in `lean` (the
      module's record, with `lean.note` saying why the recorded declaration or mathlib_match was unusable) and its
      module.
Every module is the lean.file of exactly one of these nodes; a module may import a sibling module of the delivery
(compile_modules defers it until the sibling is in the library; the merge lands the modules in dependency order).

Failures are (letter, text) pairs; the letters are the ones of the stage-2 preflight:
  a commit and files, b node and record, c the Lean file, d an existing declaration, e the report, f the compile.

    python3 tools/stage2_delivery.py signature <file.lean> <declaration>     print the statement the tools read
    python3 tools/stage2_delivery.py decls <file.lean>                       list the declarations the tools see
"""
from __future__ import annotations
import gzip, json, os, pathlib, re, shutil, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from node_fields import (changed_fields_except, STAGE2_OWNS, STAGE2_ITEM_ALSO, STAGE2_ITEM_CORRECTION,  # noqa: E402
                         check_statement_change, correction_fields)

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = pathlib.Path(os.environ.get("SHEAF_SOURCE_REPO", str(pathlib.Path.home() / "weil-conjectures-slopmaster2")))
KEYS = ("module", "declaration", "statement", "branch", "by", "date", "existing")
OPTIONAL = ("declarations", "file", "fixed_by", "note")
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
LET_KW = re.compile(r"(?:letI|let|haveI|have|suffices|obtain)(?![\w'])")


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
        # the signature: up to `:=`, `where` or `|` at bracket depth 0. A `let`-style binder (letI, let, haveI, have,
        # suffices, obtain) at depth 0 after the main colon owns the next `:=` at depth 0, unless a `;` or a line
        # indented no deeper than its keyword comes first: `theorem foo : letI := 3; x = x := by sorry`.
        depth, k, sig_end = 0, x.end(), None
        colon, let_col = False, None
        while k < end:
            c = m[k]
            if c in "([{⦃⟨":
                depth += 1
            elif c in ")]}⦄⟩":
                depth -= 1
            elif depth == 0:
                if let_col is not None and (c == ";" or (c == "\n" and len(m[k + 1:].split("\n", 1)[0]) -
                                                        len(m[k + 1:].split("\n", 1)[0].lstrip(" \t")) <= let_col)):
                    let_col = None
                if c == ":" and not m.startswith(":=", k):
                    colon = True
                if colon and c in "lho" and not (m[k - 1].isalnum() or m[k - 1] in "_.'"):
                    w = LET_KW.match(m, k)
                    if w:
                        let_col = k - (m.rfind("\n", 0, k) + 1)
                        k = w.end(); continue
                if m.startswith(":=", k) and let_col is not None:
                    let_col = None
                    k += 2; continue
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
            if upstream_has(extra):
                pass  # an existing Mathlib/source declaration recorded next to the module's own (mixed record, 2026-10-11)
            else:
                f(f"lean.declarations names {extra}, which the file does not declare and which neither Mathlib nor the source has")
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


def check_existing(rec: dict, git: "Git | None" = None, base: str | None = None) -> tuple[list[tuple[str, str]], list[str]]:
    """Check (d). Returns (failures, notes). A declaration of this project (module Sheaf.*, branch sheaf-dag: another
    node already states the statement or defines the notion) is read from lean/Sheaf/<path>.lean on `base` (default
    the working tree's HEAD); no module is compiled for it."""
    fails, notes = [], []
    mod, decl = str(rec.get("module") or ""), str(rec.get("declaration") or "")
    if not mod.startswith(("Mathlib.", "WeilConjectures.", "Sheaf.")):
        fails.append(("d", f"lean.existing is true but lean.module {mod!r} is neither Mathlib.*, WeilConjectures.* nor Sheaf.*"))
        return fails, notes
    want = {"Mathlib": "mathlib", "WeilConjectures": "slopmaster2", "Sheaf": "sheaf-dag"}[mod.split(".")[0]]
    if rec.get("branch") != want:
        fails.append(("d", f"lean.branch is {rec.get('branch')!r}; a declaration of {mod.split('.')[0]} has branch {want!r}"))
    if mod.startswith("Sheaf."):
        if decl.startswith("Sheaf."):
            fails.append(("d", f"declaration {decl}: names carry no `Sheaf.` prefix (only the module path is Sheaf.<...>)"))
        rel = "lean/" + mod.replace(".", "/") + ".lean"
        text = (git or Git(ROOT)).show(base or "HEAD", rel)
        if text is None:
            fails.append(("d", f"lean.module {mod}: no file {rel} on {(base or 'HEAD')[:10]} (an existing project declaration is landed on sheaf-dag)"))
            return fails, notes
        p = pathlib.Path(rel)
    else:
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
    field = (not grep) and re.search(r"^\s+(?:\(\s*)?" + re.escape(short) + r"\s*[:({\[]", text, re.M)
    if not grep and field:
        notes.append(f"existing declaration: {decl} is a structure/class field of {p.name} (not found by the declaration grep)")
    elif not grep and not mod.startswith("Sheaf.") and (_names() and _MODULE_OF.get(decl) == mod):
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


def check_record(rec, group, where: str = "lean") -> list[tuple[str, str]]:
    fails = []
    f = lambda s: fails.append(("b", f"{where}: {s}" if where != "lean" else s))  # noqa: E731
    if not isinstance(rec, dict):
        return [("b", f"{where}: the node's `lean` is {type(rec).__name__}, not a record {{{', '.join(KEYS)}, ...}}")]
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


# The fields of a new definition node (STAGE 2 EXTRA NODES, decision of the human, 2026-10-11 05:55 UTC).
NEW_NODE_KEYS = ("id", "kind", "title", "statement", "source", "stmt_deps", "proof", "proof_deps", "proof_origin",
                 "mathlib_searches", "mathlib_match", "status", "created", "blueprint", "lean_audit", "chapter", "unit",
                 "lean")
SEARCH_KEYS = ("tool", "query", "results", "date", "verdict")
CITE = re.compile(r"\[([a-z][a-z0-9]*(?:-[a-z][a-z0-9]*)+)\]")


def search_kind(tool) -> str | None:
    t = str(tool or "").lower().replace(" ", "")
    if "leansearch" in t:
        return "leansearch"
    if "loogle" in t or "leanfinder" in t:
        return "loogle/leanfinder"
    if "grep" in t or t in ("rg", "ripgrep"):
        return "grep"
    return None


def check_new_node(nid: str, d: dict, path: str, item: str, item_node: dict, item_dir: str, group: str,
                   known_ids: set, new_ids: set, base_nodes: dict | None) -> list[tuple[str, str]]:
    """The field rule of a new definition node (coord/STATE.md, STAGE 2 EXTRA NODES). Failures are (b)."""
    fails = []
    f = lambda s: fails.append(("b", f"new node {nid}: {s}"))  # noqa: E731
    if not isinstance(d, dict):
        return [("b", f"new node {nid}: not a JSON object")]
    if pathlib.PurePosixPath(path).parent.as_posix() != item_dir:
        f(f"file {path}: a new node goes into the item's chapter directory {item_dir}/")
    if d.get("id") != nid:
        f(f"id is {d.get('id')!r}, the file name says {nid!r}")
    if not nid.startswith("def-"):
        f("the id of a new definition node has the form def-<chapter prefix>-<short-name>")
    extra = [k for k in d if k not in NEW_NODE_KEYS]
    if extra:
        f(f"key(s) outside the rule: {', '.join(extra)} (the maintainer's fields come with the merge)")
    missing = [k for k in NEW_NODE_KEYS if k not in d]
    if missing:
        f(f"missing key(s): {', '.join(missing)}")
    if d.get("kind") != "definition":
        f(f"kind is {d.get('kind')!r}; a new node of a stage-2 delivery is a \"definition\"")
    if d.get("status") != "split":
        f(f"status is {d.get('status')!r}; \"split\" (a definition needs no proof)")
    if not str(d.get("title") or "").strip():
        f("no title")
    stmt = str(d.get("statement") or "")
    if not stmt.strip():
        f("empty statement")
    if "\\\\" in stmt and re.search(r"\\\\[A-Za-z]", stmt):
        f("the statement has doubled backslashes (\\\\cmd): TeX is written once")
    src = d.get("source")
    if not (isinstance(src, dict) and str(src.get("document") or "").strip() and str(src.get("place") or "").strip()):
        f("source is not {document, place} with both non-empty")
    sd = d.get("stmt_deps")
    if not isinstance(sd, list):
        f("stmt_deps is not a list"); sd = []
    for c in sd:
        if c not in known_ids and c not in new_ids:
            f(f"stmt_deps names {c}, which is no node (neither on the base nor new in the delivery)")
        if c == nid:
            f("stmt_deps names the node itself")
    cited = CITE.findall(stmt)
    for c in cited:
        if c not in sd:
            f(f"the statement cites [{c}], which is not in stmt_deps")
    for c in sd:
        if c not in cited:
            f(f"stmt_deps has {c}, which the statement does not cite as [{c}]")
    if d.get("proof") != [] or d.get("proof_deps") != [] or d.get("proof_origin") is not None:
        f("proof and proof_deps must be [] and proof_origin null (a definition has no proof)")
    if d.get("mathlib_match") is not None:
        f("mathlib_match is not null: a notion of Mathlib or the source is no new node (record it as an "
          "`existing: true` lean record, and only when no DAG node carries it)")
    ms = d.get("mathlib_searches")
    kinds = set()
    if not isinstance(ms, list):
        f("mathlib_searches is not a list"); ms = []
    for k, s in enumerate(ms, 1):
        if not isinstance(s, dict):
            f(f"mathlib_searches[{k}] is not an object"); continue
        miss = [x for x in SEARCH_KEYS if not str(s.get(x) or "").strip()]
        if miss:
            f(f"mathlib_searches[{k}] has no {', '.join(miss)}")
        kd = search_kind(s.get("tool"))
        if kd:
            kinds.add(kd)
    want = {"leansearch", "loogle/leanfinder", "grep"}
    if kinds != want:
        f(f"mathlib_searches lack the kind(s) {', '.join(sorted(want - kinds))} (LeanSearch; Loogle or LeanFinder; grep of "
          "Mathlib, of the source repository and of lean/Sheaf)")
    cr = d.get("created")
    if not isinstance(cr, dict):
        f("no created record"); cr = {}
    if cr.get("by") != "worker":
        f(f"created.by is {cr.get('by')!r}, not \"worker\"")
    if cr.get("item") != item:
        f(f"created.item is {cr.get('item')!r}, not the item {item!r}")
    if cr.get("group") != group:
        f(f"created.group is {cr.get('group')!r}, not {group!r}")
    if not DATE.match(str(cr.get("date") or "")):
        f(f"created.date {cr.get('date')!r} is not YYYY-MM-DD")
    bp = d.get("blueprint")
    if not isinstance(bp, dict):
        f("no blueprint field {is, from, same_as}")
    else:
        if bp.get("is") is not None:
            f(f"blueprint.is is {bp.get('is')!r}; null for a new node")
        fr = bp.get("from") if isinstance(bp.get("from"), dict) else None
        if fr is None:
            f("blueprint.from is not {node, place, via}")
        else:
            if not str(fr.get("place") or "").strip() or fr.get("place") == "unspecified":
                f("blueprint.from.place is empty or \"unspecified\": name the place of the blueprint proof the notion serves")
            if base_nodes is not None:
                try:
                    import blueprint_refs as brf
                    tmp = dict(base_nodes)
                    tmp[item] = item_node
                    tmp[nid] = d
                    anc, chain_ = brf.chain(nid, tmp)
                    via = chain_[1:]
                    if fr.get("node") != anc:
                        f(f"blueprint.from.node is {fr.get('node')!r}; `tools/blueprint_refs.py ancestor {item}` gives {anc!r}")
                    if fr.get("via") != via:
                        f(f"blueprint.from.via is {fr.get('via')!r}; the item's via with the item in front is {via!r}")
                except Exception as e:  # noqa: BLE001
                    f(f"blueprint.from not checked ({e})")
        if not isinstance(bp.get("same_as"), list):
            f("blueprint.same_as is not a list (the search for the same notion in the blueprint)")
    la = d.get("lean_audit")
    if la != {"master": {"state": "none"}, "slopmaster2": {"state": "none"}}:
        f(f"lean_audit is {json.dumps(la)}; {{\"master\": {{\"state\": \"none\"}}, \"slopmaster2\": {{\"state\": \"none\"}}}}")
    for k in ("chapter", "unit"):
        if d.get(k) != item_node.get(k):
            f(f"{k} is {d.get(k)!r}; the item's is {item_node.get(k)!r}")
    fails.extend(check_record(d.get("lean"), group, f"new node {nid}"))
    return fails


def section_text(text: str | None, title: str) -> str:
    for s in re.split(r"(?m)^## ", text or "")[1:]:
        head, _, body = s.partition("\n")
        if head.strip() == title:
            return body.strip()
    return ""


def module_path(rec: dict) -> str | None:
    m = rec.get("module") if isinstance(rec, dict) else None
    return "lean/" + m.replace(".", "/") + ".lean" if isinstance(m, str) and m else None


def read_delivery(git: Git, ref: str, base: str, group: str, item: str, max_commits: int = 1,
                  overrides: dict | None = None, drop=(), revert=(), drop_files=(), revert_statement: bool = False) -> dict:
    """Checks (a), (b), (c) without the compile, (d), (e) of the delivery `ref` against `base`.
    `overrides` {path: text} replaces the text of a delivered file (a reviewer's fix, merge_delivery.py).
    `drop` (merge_delivery.py --stage 2 --drop-nodes, lead 2026-10-11): ids of NEW nodes of the delivery that are left
    out (a duplicate of a landed node): the node file and every module whose only owner is that node are not part of
    the delivery read; the item's stmt_deps / proof_deps lose the id; a kept module importing a dropped module fails
    (c); an id that is not a new node of the delivery fails (b). D["dropped"] = {id: {path, file}}.
    `revert` (--revert-nodes, 2026-10-11): ids of EXISTING nodes (on the base) whose change by the delivery is left out:
    the node stays as it is on sheaf-dag, its delivered module is left out as for a dropped node; an id the delivery
    does not change, or the item, fails (b). D["reverted"] = {id: {path, file, module}}.
    `drop_files` (--drop-files): NEW modules lean/Sheaf/... of the delivery left out (the fix no longer uses them); a
    kept module importing one, or a kept record with it as lean.file, fails (c). D["dropped_files"] = [path].
    `revert_statement` (--revert-statement, 2026-10-11): the delivery's statement correction of the ITEM is left out:
    statement, stmt_deps, proof, proof_deps and statement_change as on the base (stmt_deps keeps the delivery's kept
    new nodes it added), the delivered `lean` record kept; the item is then checked as uncorrected, and (b) fails when
    the branch does not change those fields, when the item's module uses the declaration of a node the restored
    stmt_deps lose, or when a kept new node cites the item (a cycle). D["statement_reverted"] = [fields],
    D["stmt_deps_reverted"] = [ids the restored stmt_deps lose].
    Returns {fails: [(letter, text)], notes, node_path, node, base_node, rec, lean_path, lean_text, report, decl,
    commits, base, new: {id: {path, node}}, deps: {id: {path, node, base_node}}, modules: [{file, node, role, rec,
    text, decl, module, siblings}] in dependency order (a module after the sibling modules it imports), roles,
    corrected (the item's statement is corrected: STAGE 2 STATEMENT CORRECTION), citers (the base nodes whose
    stmt_deps or proof_deps name the item, computed when corrected), citer_marks (statement_change.citers)}."""
    D = {"fails": [], "notes": [], "node_path": None, "node": None, "base_node": None, "rec": None,
         "lean_path": None, "lean_text": None, "report": None, "decl": None, "commits": [],
         "new": {}, "deps": {}, "modules": [], "roles": [], "report_path": f"coord/reports/{group}/{item}.md",
         "corrected": False, "citers": [], "citer_marks": [], "dropped": {}, "reverted": {}, "dropped_files": [],
         "statement_reverted": [], "stmt_deps_reverted": []}
    fails = D["fails"]
    over = overrides or {}
    f = lambda L, s: fails.append((L, s))  # noqa: E731
    show = lambda p: over[p] if p in over else git.show(ref, p)  # noqa: E731
    if not git.ok("rev-parse", "--verify", "-q", ref):
        f("a", f"no ref {ref}"); return D
    if not git.ok("rev-parse", "--verify", "-q", base):
        f("a", f"no ref {base}: run `git fetch origin` (or pass --base <ref>)"); return D
    # A delivery built on an older tip of sheaf-dag is checked against the commit it was built on (the merge-base),
    # as the stage-1 tools do: sheaf-dag moves on every minute and the merge is by files on the current tip (lead,
    # 2026-10-11 05:47 UTC, after C1's def-pc-compactly-generated failed (a) only because of the moved tip).
    mb = git.run("merge-base", base, ref).strip()
    if not mb:
        f("a", f"{ref} has no common history with {base}: rebuild the branch on {base}"); return D
    if mb != git.run("rev-parse", base).strip():
        D["notes"].append(f"{ref} is based on {mb[:9]} (sheaf-dag has moved on); checked against that base")
        base = mb
    D["base"] = base
    commits = git.run("rev-list", "--reverse", f"{base}..{ref}").split()
    D["commits"] = commits
    if not commits:
        f("a", f"{ref} has no commit beyond {base} (the branch would deliver nothing)")
    elif len(commits) > max_commits:
        f("a", f"{len(commits)} commits beyond {base}: deliver one item as exactly one commit (squash with `git reset --soft {base}` and commit again)")
    node_path = git.node_path(ref, item)
    D["node_path"] = node_path
    report = D["report_path"]
    if node_path is None:
        f("b", f"no node file for {item} on {ref}"); return D
    item_dir = pathlib.PurePosixPath(node_path).parent.as_posix()
    base_paths = {pathlib.PurePosixPath(p).stem: p for p in
                  git.run("ls-tree", "-r", "--name-only", base, "--", "dag/nodes", check=False).splitlines() if p.endswith(".json")}
    # --drop-nodes / --revert-nodes decide "new vs existing" on the tip of sheaf-dag (2026-10-11): a node the delivery
    # adds that has since landed via another group is left out like a dropped new node (the delivery's copy omitted)
    tip_paths = {pathlib.PurePosixPath(p).stem: p for p in
                 git.run("ls-tree", "-r", "--name-only", "sheaf-dag", "--", "dag/nodes", check=False).splitlines()
                 if p.endswith(".json")}
    status = [l.split("\t") for l in git.run("diff", "--name-status", base, ref).splitlines() if l] if commits else []
    lean_files, node_files, added_files = [], [], set()
    for st in status:
        code, p = st[0], st[-1]
        if code.startswith("D"):
            f("a", f"{p}: the delivery deletes a file"); continue
        if code.startswith("R"):
            f("a", f"{st[1]} -> {p}: the delivery renames a file"); continue
        if p == report:
            continue
        if p.startswith("dag/nodes/") and p.endswith(".json"):
            node_files.append((code, p)); continue
        if p.startswith("lean/Sheaf/") and p.endswith(".lean"):
            lean_files.append(p)
            if code.startswith("A"):
                added_files.add(p)
            if not code.startswith("A"):
                D["notes"].append(f"{p} exists on the base: the delivery changes a module of the library")
            continue
        if p.startswith("coord/claims/"):
            f("a", f"{p}: a claim lock file is in the delivery; claims are made with tools/claim.py on the server, never pushed")
        else:
            f("a", f"{p}: file outside the delivery (allowed: modules lean/Sheaf/<Topic>/<Name>.lean, {node_path}, new "
                   f"definition nodes {item_dir}/<id>.json, dependency node files changed in `lean`, {report})")
    changed = {st[-1] for st in status}
    if commits and node_path not in changed:
        f("b", "the node file is unchanged (the delivery sets its field `lean`)")
    # (b) the item
    try:
        node = json.loads(show(node_path) or "")
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
    base_deps = list(bnode.get("stmt_deps") or [])
    # classify the other node files: new definition nodes and dependency nodes
    drop = set(drop or ())
    revert = set(revert or ())
    if item in revert:
        f("b", f"--revert-nodes {item}: the item itself is not reverted (RETURN the delivery instead)")
    for code, p in node_files:
        if p == node_path:
            continue
        nid = pathlib.PurePosixPath(p).stem
        if nid in revert and nid in base_paths and base_paths[nid] == p:
            # --revert-nodes: the delivery's change of an existing node is left out (the node stays as on the base);
            # its delivered module (lean.file) is left out below when no kept node owns it
            try:
                dn = json.loads(git.show(ref, p) or "")
            except ValueError:
                dn = {}
            r = dn.get("lean") if isinstance(dn, dict) else None
            D["reverted"][nid] = {"path": p, "file": r.get("file") if isinstance(r, dict) else None,
                                  "module": r.get("module") if isinstance(r, dict) else None}
            continue
        if (nid in drop or nid in revert) and nid not in base_paths:
            if nid in revert and tip_paths.get(nid) != p:
                f("b", f"--revert-nodes {nid}: a new node of this delivery not on sheaf-dag (leave it out with --drop-nodes)")
                continue
            # --drop-nodes: left out; its module (lean.file) is left out below when no kept node owns it
            try:
                dn = json.loads(git.show(ref, p) or "")
            except ValueError:
                dn = {}
            r = dn.get("lean") if isinstance(dn, dict) else None
            D["dropped"][nid] = {"path": p, "file": r.get("file") if isinstance(r, dict) else None,
                                 "module": r.get("module") if isinstance(r, dict) else None}
            if nid in tip_paths:
                D["notes"].append(f"{nid}: landed on sheaf-dag since the delivery's base; the delivery's copy is left out")
            continue
        try:
            nd = json.loads(show(p) or "")
        except ValueError as e:
            f("b", f"{p}: not valid JSON ({e})"); continue
        if nid in base_paths:
            if base_paths[nid] != p:
                f("b", f"{p}: the node {nid} is {base_paths[nid]} on the base"); continue
            if nid not in base_deps:
                f("b", f"{p}: the node {nid} exists on the base and is not in the item's stmt_deps there: a delivery changes "
                       "only the item, new definition nodes and dependency nodes of the item")
                continue
            bd = json.loads(git.show(base, p) or "{}")
            D["deps"][nid] = {"path": p, "node": nd, "base_node": bd}
        else:
            D["new"][nid] = {"path": p, "node": nd}
    for nid in sorted(drop - set(D["dropped"])):
        f("b", f"--drop-nodes {nid}: not a new node of this delivery (only a node file the delivery creates is dropped)")
    for nid in sorted(revert - set(D["reverted"]) - set(D["dropped"]) - {item}):
        f("b", f"--revert-nodes {nid}: not an existing node changed by this delivery (a new node is left out with --drop-nodes)")
    for nid, x in D["reverted"].items():
        D["roles"].append(f"REVERTED dependency node {nid} ({x['path']} stays as on sheaf-dag"
                          + (f"; delivered module {x['file']}" if x["file"] else "") + ")")
    for nid, x in D["dropped"].items():
        D["roles"].append(f"DROPPED new node {nid} ({x['path']}" + (f", module {x['file']}" if x["file"] else "") + ")")
    # a dropped node landed on sheaf-dag under the same id keeps its citations (they name the landed node)
    gone_nodes = {x for x in D["dropped"] if x not in tip_paths}
    if gone_nodes:
        # the item loses its citations of the dropped nodes (the reviewer's fixes repoint the module and the record)
        node = dict(node)
        for k in ("stmt_deps", "proof_deps"):
            if isinstance(node.get(k), list) and any(x in gone_nodes for x in node[k]):
                node[k] = [x for x in node[k] if x not in gone_nodes]
        D["node"] = node
    if revert_statement and base_text is not None:
        # --revert-statement: the item's statement fields as on the base, whatever the branch (or a fixed node file)
        # says; the fields compared are those of the branch, so that a re-read on the reviewer's fixes still knows them
        try:
            raw = json.loads(git.show(ref, node_path) or "")
        except ValueError:
            raw = {}
        miss = object()
        dsd = [x for x in (node.get("stmt_deps") or []) if isinstance(x, str)]
        sd = list(bnode.get("stmt_deps") or [])
        keep = [x for x in dsd if x in D["new"] and x not in sd]
        rnode = dict(node)
        for k in STAGE2_ITEM_CORRECTION:
            if k in bnode:
                rnode[k] = json.loads(json.dumps(bnode[k]))
            else:
                rnode.pop(k, None)
        if keep:
            rnode["stmt_deps"] = sd + keep
        # what the branch changes, beyond adding new nodes to stmt_deps and the citations of dropped nodes
        for k in ("stmt_deps", "proof_deps"):
            if isinstance(raw.get(k), list):
                raw[k] = [x for x in raw[k] if x not in gone_nodes]
        ch = [k for k in STAGE2_ITEM_CORRECTION if raw.get(k, miss) != rnode.get(k, miss)]
        if not ch:
            f("b", "--revert-statement: the delivery does not change the item's " + ", ".join(STAGE2_ITEM_CORRECTION)
                   + " (beyond adding its new nodes to stmt_deps)")
        else:
            node = rnode
            D["node"] = node
            D["statement_reverted"] = ch
            D["stmt_deps_reverted"] = [x for x in dsd if x not in (node.get("stmt_deps") or [])]
            D["roles"].insert(0, f"the item's statement correction is REVERTED (--revert-statement: {', '.join(ch)} as on "
                                 "sheaf-dag" + (f"; stmt_deps keep the new node(s) {', '.join(keep)}" if keep else "")
                                 + (f"; stmt_deps lose {', '.join(D['stmt_deps_reverted'])}" if D["stmt_deps_reverted"] else "")
                                 + "; the delivered lean record kept)")
    new_ids = set(D["new"])
    for nid in D["new"]:
        D["roles"].append(f"new definition node {nid} ({D['new'][nid]['path']})")
    for nid in D["deps"]:
        D["roles"].append(f"dependency node {nid} ({D['deps'][nid]['path']}), changed in `lean`")
    # STAGE 2 STATEMENT CORRECTION (decision of the human, 2026-10-11 06:22 UTC): the item is "corrected" when its
    # statement, proof, proof_deps or statement_change differ from the base; it may then change in
    # STAGE2_ITEM_CORRECTION too, and node_fields.check_statement_change validates the record.
    corrected = base_text is not None and bool(correction_fields(bnode, node))
    D["corrected"] = corrected
    D["citers"] = []
    owns = STAGE2_OWNS + STAGE2_ITEM_ALSO + (STAGE2_ITEM_CORRECTION if corrected else ())
    ch = changed_fields_except(bnode, node, owns) if base_text is not None else []
    if ch:
        f("b", f"the node changed in field(s) {', '.join(ch)}; a stage-2 delivery takes the node as it is on {base} and sets "
               "only `lean` (and adds the new definition nodes to stmt_deps)"
               + ("; a statement correction changes statement, stmt_deps, proof, proof_deps and statement_change" if corrected else
                  "; a statement correction (statement_change) may change statement, stmt_deps, proof, proof_deps"))
    hd = node.get("stmt_deps") if isinstance(node.get("stmt_deps"), list) else []
    gone = [x for x in base_deps if x not in hd]
    added = [x for x in hd if x not in base_deps]
    base_nodes = None
    if corrected:
        base_nodes = nodes_at(git, base)
        cit = sorted(n for n, d in base_nodes.items() if n != item and
                     (item in (d.get("stmt_deps") or []) or item in (d.get("proof_deps") or [])))
        D["citers"] = cit
        for x in check_statement_change(bnode, node, cit):
            f("b", f"statement correction: {x}")
        sc = node.get("statement_change") if isinstance(node.get("statement_change"), dict) else {}
        D["citer_marks"] = [c for c in sc.get("citers") or [] if isinstance(c, dict)]
        bad = [x for x in added if x not in new_ids and x not in base_paths]
        if bad:
            f("b", f"the corrected item's stmt_deps gained {', '.join(bad)}, which are neither nodes on the base nor new nodes "
                   "of the delivery")
        cited = set(CITE.findall(str(node.get("statement") or "")))
        miss = sorted(c for c in cited if c not in hd)
        if miss:
            f("b", f"the corrected statement cites {', '.join('[' + c + ']' for c in miss)}, not in the item's stmt_deps")
        for k in ("proof_deps",):
            for x in node.get(k) or []:
                if x not in base_paths and x not in new_ids:
                    f("b", f"the corrected item's {k} names {x}, which is no node on the base nor of the delivery")
        D["added_deps"] = [x for x in added if x in new_ids]
    else:
        if gone:
            f("b", f"the item's stmt_deps lost {', '.join(gone)}: a delivery only adds the new definition nodes to it "
                   "(or corrects the statement, with statement_change)")
        # STMT_DEPS MAY GAIN LANDED NODES (launcher 2026-10-11 07:55 +08): a node that exists on the base with a
        # `lean` record (landed by another group meanwhile) may be added to the item's stmt_deps without a correction.
        landed = []
        for x in added:
            # a dropped new node landed on sheaf-dag since the base is read there (--drop-nodes, 2026-10-11)
            at = (base, base_paths[x]) if x in base_paths else ("sheaf-dag", tip_paths[x]) if x in D["dropped"] and x in tip_paths else None
            if x in new_ids or at is None:
                continue
            try:
                bn = json.loads(git.show(*at) or "{}")
            except ValueError:
                bn = {}
            r = bn.get("lean")
            if isinstance(r, dict) and (r.get("module") or r.get("existing") is True or r.get("convention")) \
                    or bn.get("status") in ("mathlib", "merged"):
                landed.append(x)
        if landed:
            D["notes"].append(f"the item's stmt_deps gained the landed node(s) {', '.join(landed)} (STMT_DEPS MAY GAIN LANDED NODES)")
        bad = [x for x in added if x not in new_ids and x not in landed]
        if bad:
            f("b", f"the item's stmt_deps gained {', '.join(bad)}, which are neither new nodes of the delivery nor nodes landed "
                   "on the base with a lean record (only those may be added, or a statement correction with statement_change)")
        D["added_deps"] = added
    if corrected:
        D["roles"].insert(0, f"the item is CORRECTED (statement_change): {len(D['citers'])} citer(s) on the base, "
                             f"{sum(1 for c in D.get('citer_marks') or [] if c.get('holds') is False)} marked holds:false")
    rec = node.get("lean")
    D["rec"] = rec
    fails.extend(check_record(rec, group))
    if not isinstance(rec, dict):
        rec = {}
    # (b) the new nodes and the dependency nodes
    if base_nodes is None and D["new"]:
        base_nodes = nodes_at(git, base)
    known = set(base_paths)
    for nid, x in D["new"].items():
        fails.extend(check_new_node(nid, x["node"], x["path"], item, node, item_dir, group, known, new_ids, base_nodes))
    # every new node is cited by the item, directly or through another new node
    reach, todo = set(), [x for x in hd if x in new_ids]
    while todo:
        u = todo.pop()
        if u in reach:
            continue
        reach.add(u)
        todo += [v for v in (D["new"][u]["node"].get("stmt_deps") or []) if v in new_ids]
    for nid in D["new"]:
        if nid not in reach:
            f("b", f"new node {nid}: not cited by the item (add it to the item's stmt_deps, or cite it from a new node the "
                   "item cites)")
    if D["new"] and base_nodes is not None:
        pre = {n.split("-")[1] for n, d in base_nodes.items() if d.get("chapter") == node.get("chapter") and n.count("-") >= 2}
        for nid in D["new"]:
            if nid.count("-") < 2 or nid.split("-")[1] not in pre:
                D["notes"].append(f"new node {nid}: the prefix {nid.split('-')[1] if nid.count('-') >= 1 else nid!r} is not "
                                  f"used by any node of the chapter {node.get('chapter')} on the base")
    for nid, x in D["deps"].items():
        nd, bd = x["node"], x["base_node"]
        ch = changed_fields_except(bd, nd, STAGE2_OWNS)
        if ch:
            f("b", f"dependency node {nid}: changed in field(s) {', '.join(ch)}; a dependency node changes only in `lean` "
                   "(its mathlib_match stays)")
        r = nd.get("lean")
        fails.extend(check_record(r, group, f"dependency node {nid}"))
        if isinstance(r, dict):
            if r.get("existing") is not False and not (r.get("existing") is True and str(r.get("module") or "").startswith("Sheaf.")):
                f("b", f"dependency node {nid}: lean.existing must be false (a dependency module states the notion), or true "
                       "with branch sheaf-dag and module Sheaf.<...> (a declaration another node of this project already landed)")
            if not str(r.get("note") or "").strip():
                f("b", f"dependency node {nid}: lean.note missing: why the recorded declaration or mathlib_match is unusable "
                       "and what the module states")
    # (c) / (d): the modules
    owners: dict[str, list[str]] = {}
    recs = [(item, "item", rec)] + [(n, "new", x["node"].get("lean")) for n, x in D["new"].items()] \
        + [(n, "dependency", x["node"].get("lean")) for n, x in D["deps"].items()]
    mods = []
    # --drop-nodes: a module whose only owner is a dropped node is left out of the delivery
    kept_files = {r.get("file") for _, _, r in recs if isinstance(r, dict) and r.get("existing") is not True}
    dropped_mods = set()
    for why, xs in (("dropped", D["dropped"]), ("reverted", D["reverted"])):
        for x in xs.values():
            if x["file"] and x["file"] in lean_files and x["file"] not in kept_files:
                lean_files.remove(x["file"])
                if x["module"]:
                    dropped_mods.add(x["module"])
                D["notes"].append(f"{x['file']}: the module of a {why} node, left out")
    # --drop-files: new modules of the delivery the fix no longer uses
    gone_files = set()
    for lf in dict.fromkeys(drop_files or ()):
        if lf not in added_files:
            f("c", f"--drop-files {lf}: not a new module lean/Sheaf/<...>.lean of this delivery")
            continue
        if lf in lean_files:
            lean_files.remove(lf)
        gone_files.add(lf)
        D["dropped_files"].append(lf)
        dropped_mods.add(lf[len("lean/"):-len(".lean")].replace("/", "."))
        D["roles"].append(f"DROPPED module {lf} (--drop-files)")
    for nid, role, r in recs:
        if not isinstance(r, dict):
            continue
        who = "the item" if role == "item" else f"{role} node {nid}"
        if r.get("existing") is True:
            if role == "item" and lean_files and not D["new"] and not D["deps"]:
                f("d", f"lean.existing is true but the commit has Lean file(s) {', '.join(lean_files)}")
            df, notes = check_existing(r, git, base)
            fails.extend((L, x if role == "item" else f"{who}: {x}") for L, x in df)
            D["notes"] += [x if role == "item" else f"{who}: {x}" for x in notes]
            continue
        lf = r.get("file")
        if lf and lf in gone_files:
            f("c", f"{who}: lean.file {lf} is left out by --drop-files (point the record at a kept module or a landed "
                   "declaration)")
            continue
        if not lf:
            if role == "item" and lean_files and not D["new"] and not D["deps"]:
                f("c", f"the commit has {lean_files[0]} but lean.file is not set")
            continue
        owners.setdefault(lf, []).append(nid)
        if not lf.startswith("lean/Sheaf/"):
            f("c", f"{who}: lean.file {lf}: a module of the library is under lean/Sheaf/")
        text = show(lf)
        if text is None:
            f("c", f"{who}: no file {lf} in {ref}"); continue
        if lf not in lean_files and lf not in over:
            f("c", f"{who}: {lf} is not changed by the commit (the module is part of the delivery)")
        cf, decl = check_lean_text(text, r, nid)
        fails.extend((L, x if role == "item" else f"{lf} ({nid}): {x}") for L, x in cf)
        mods.append({"file": lf, "node": nid, "role": role, "rec": r, "text": text, "decl": decl,
                     "module": r.get("module")})
        if role == "item":
            D["lean_path"], D["lean_text"], D["decl"] = lf, text, decl
    for m in mods:
        bad = [i for i in imports(m["text"]) if i in dropped_mods]
        # a module of that name already on sheaf-dag (the delivery's copy duplicated a landed module): the import
        # reads the landed module (2026-10-11)
        landed = [i for i in bad if git.show("sheaf-dag", "lean/" + i.replace(".", "/") + ".lean") is not None]
        for i in landed:
            D["notes"].append(f"{m['file']} ({m['node']}): imports {i}, the landed module of that name on sheaf-dag "
                              "(the delivery's copy is left out)")
        bad = [i for i in bad if i not in landed]
        if bad:
            f("c", f"{m['file']} ({m['node']}): imports the dropped/reverted module(s) {', '.join(bad)} (fix it to "
                   "import the landed declaration's module)")
    for lf in lean_files:
        o = owners.get(lf, [])
        if not o:
            f("c", f"{lf}: no node of the delivery has it as lean.file (every module is the module of the item, of a new "
                   "definition node or of a dependency node)")
    for lf, o in owners.items():
        if len(o) > 1:
            f("c", f"{lf} is the lean.file of several nodes ({', '.join(o)}): one module per node")
    seen: dict[str, str] = {}
    for m in mods:
        for d in declarations(m["text"]):
            if d["name"] and d["name"] in seen and seen[d["name"]] != m["file"]:
                f("c", f"{d['name']} is declared in {seen[d['name']]} and in {m['file']}")
            elif d["name"]:
                seen[d["name"]] = m["file"]
    # dependency order: a module after the sibling modules it imports
    names = {m["module"]: m for m in mods if m["module"]}
    for m in mods:
        m["siblings"] = [i for i in imports(m["text"]) if i in names and i != m["module"]]
    order, state = [], {}

    def visit(m, stack):
        k = m["file"]
        if state.get(k) == 2:
            return
        if state.get(k) == 1:
            f("c", f"the modules import each other in a cycle: {' -> '.join(stack + [m['module']])}")
            return
        state[k] = 1
        for s in m["siblings"]:
            visit(names[s], stack + [m["module"]])
        state[k] = 2
        order.append(m)
    for m in mods:
        visit(m, [])
    D["modules"] = order
    for m in order:
        D["roles"].append(f"module {m['file']} of {m['role']} {m['node']}"
                          + (f" (imports the delivery's {', '.join(m['siblings'])})" if m["siblings"] else ""))
    if D["statement_reverted"]:
        # --revert-statement: the item's module uses no declaration of a node the restored stmt_deps lose
        for x in D["stmt_deps_reverted"]:
            # its declarations as recorded on the base, or on sheaf-dag now (a node landed since the base)
            names = []
            for at in (base, "sheaf-dag") if x in base_paths else ():
                try:
                    r = json.loads(git.show(at, base_paths[x]) or "{}").get("lean")
                except (ValueError, AttributeError):
                    r = None
                if isinstance(r, dict):
                    names += [r.get("declaration")] + list(r.get("declarations") or [])
            for nm in {str(n).split(".")[-1] for n in names if n}:
                if D["lean_text"] and re.search(rf"(?<![\w']){re.escape(nm)}(?![\w'])", D["lean_text"]):
                    f("b", f"--revert-statement: the item's module {D['lean_path']} uses {nm}, the declaration of {x}, which "
                           "the restored stmt_deps do not have (fix the module with --apply-fixes, or RETURN)")
        # no cycle: a kept new node reachable from the item does not cite the item
        for nid in sorted(reach):
            if item in (D["new"][nid]["node"].get("stmt_deps") or []) + (D["new"][nid]["node"].get("proof_deps") or []):
                f("b", f"--revert-statement: the new node {nid} cites the item, which cites it: a cycle in the DAG")
    # (e) the report
    rt = show(report)
    D["report"] = rt
    fails.extend(check_report(rt, group, report, list(D["new"]), list(D["deps"]), D["corrected"], D["citers"]))
    return D


def check_report(rt: str | None, group: str, where: str, new_ids=(), dep_ids=(), corrected: bool = False,
                 citers=()) -> list[tuple[str, str]]:
    """Check (e) on the text of the report: the two sections, `## New nodes` / `## Dependency modules` naming every
    new node / dependency node of the delivery, and `## Statement corrected` (naming every citer) when the item is
    corrected."""
    if rt is None:
        return [("e", f"no report {where}")]
    out = []
    w, s = report_sections(rt, group)
    if not w:
        out.append(("e", "the report has no non-empty section '## Worker report'"))
    if not s:
        out.append(("e", f"the report has no non-empty section '## Second reading by {group}'"))
    for title, ids in (("New nodes", new_ids), ("Dependency modules", dep_ids)):
        if not ids:
            continue
        body = section_text(rt, title)
        if not body:
            out.append(("e", f"the report has no non-empty section '## {title}' (the delivery has {', '.join(ids)})"))
            continue
        for i in ids:
            if i not in body:
                out.append(("e", f"the section '## {title}' does not name {i}"))
    if corrected:
        body = section_text(rt, "Statement corrected")
        if not body:
            out.append(("e", "the item's statement is corrected but the report has no non-empty section '## Statement "
                             "corrected' (old statement, what was wrong, the source place, one line per citer)"))
        else:
            for i in citers:
                if i not in body:
                    out.append(("e", f"the section '## Statement corrected' does not name the citer {i}"))
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
    if new.get("existing") is True and rec.get("existing") is False:
        # (2026-10-11) a new module turned into existing declarations: no `file` (absent or null in the override), the
        # module's `declarations` go unless the override gives them, the statement must be given verbatim
        if new.get("file") is None or "file" not in (override or {}):
            new.pop("file", None)
        if "declarations" not in (override or {}):
            new.pop("declarations", None)
        if "statement" not in (override or {}):
            refuse.append("existing: true: give the existing declaration's statement verbatim in the record override")
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


def landed_same(root: pathlib.Path, module: str, text: str) -> bool:
    """Whether the library of `root` already has `module` with exactly `text` (a sibling that has landed)."""
    p = root / "lean" / (module.replace(".", "/") + ".lean")
    try:
        return p.read_text() == text
    except OSError:
        return False


def compile_modules(D: dict, group: str, root: pathlib.Path | None = None, timeout: int = 120) -> list[dict]:
    """Compile every module of the delivery in dependency order, each on its own in lean/.sandbox/<group>/<node>.lean.
    A module that imports a sibling module of the delivery which is not yet in the library is not compiled: its status
    is "deferred" (the merge lands the modules in order, and each landing compiles in the library, where the sibling then
    exists). Returns [{file, node, status: ok|fail|deferred|not run, rc, out}]."""
    root = root or compile_root()
    texts = {m["module"]: m["text"] for m in D.get("modules") or []}
    res, bad = [], set()
    for m in D.get("modules") or []:
        pend = [s for s in m.get("siblings") or [] if s in bad or not landed_same(root, s, texts.get(s, ""))]
        if pend:
            res.append({"file": m["file"], "node": m["node"], "status": "deferred", "rc": None,
                        "out": f"compile: deferred: imports sibling {', '.join(pend)} (not yet in the library; the merge "
                               "lands the modules in dependency order and each landing compiles in the library)"})
            continue
        ran, rc, out = compile_text(m["text"], group, m["node"], root, timeout)
        st = "not run" if not ran else ("ok" if rc == 0 else "fail")
        if st == "fail":
            bad.add(m["module"])
        res.append({"file": m["file"], "node": m["node"], "status": st, "rc": rc, "out": out})
    return res


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
