#!/usr/bin/env python3
"""Import the natural-language blueprint of the Weil-conjectures repository into dag/nodes/.

Usage:
  tools/import_blueprint.py [--lean-master DIR] [--lean-slopmaster2 DIR] [--mathlib DIR] [--dry]

Reads   literature/blueprint/master/blueprint/sec-*/sk-*/*.md   (TOML frontmatter, statement, `## Proof`)
Writes  dag/nodes/<section>/<id>.json   one file per definition / theorem / lemma
        dag/notes/<section>/<id>.json   the remarks and the section files, which are not nodes
        dag/notes/dropped_edges.tsv     the dependency edges that pointed at a remark, or at the node itself
        dag/import_report.json          the counts of this run

The Lean trees and the Mathlib checkout are only read: a declaration named in the blueprint's `lean` field is
looked up in the source text (no Lean is run), and a node is a Mathlib leaf only when its statement carries the
blueprint's own `*Mathlib:*` paragraph and every declaration named there is found in the Mathlib sources.
Without the directories the corresponding fields stay empty. Everything here is text processing; what the rules
are and which were checked by reading is in `coord/ledger.md` (2026-10-08).

Rules (fixed on 2026-10-08, one ledger line each):
  kinds      definition -> definition; theorem, lemma -> statement; thm-weil-final additionally target.
  notes      kind = remark and kind = section go to dag/notes/; edges to them are dropped and listed.
             A remark tagged latex:openproblem that a node's text cites is kept as a statement with no proof.
  versions   a file with `## Detailed form` holds several versions; the last one is the node, the earlier
             ones are kept verbatim in `blueprint_sketch`.
  deps       stmt_deps = ids cited in the statement; a step's uses = ids cited in the step. Frontmatter `uses`
             entries the text does not cite are kept (a definition among them as a statement dependency, a
             statement as a proof dependency without a step) unless the list has more than 20 entries.
  steps      labelled paragraphs (`*Step 1.*`, `*Clause (i).*`, …) if the proof has at least two, else the
             items of a top-level numbered list, else paragraphs; displayed formulas stay with their sentence.
  no proof   a proof that declares itself a recorded input, is omitted, or relies on a recorded input for one
             of its steps is not a proof: `proof` stays empty, the text is in `blueprint_proof_text`.
"""
from __future__ import annotations
import argparse, collections, datetime, json, pathlib, re, shutil, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
BP = ROOT / "literature" / "blueprint" / "master" / "blueprint"
TARGET = "thm-weil-final"
SCRATCH = pathlib.Path("/tmp/claude-1008/-home-bwucc/15bc8903-1b9b-4c9f-963b-b77ee3192e8e/scratchpad/weil")
DEFAULT_MATHLIB = pathlib.Path("~/weil-conjectures-slopmaster2/.lake/packages/mathlib").expanduser()  # SETUP.md, "The machine"
PADDED = 20          # a `uses` list longer than this is a subsection poured in
LONG_PROOF = 300     # words
FEW_DEPS = 3
BODY_LINES = 10      # stages/1-dag.md §2

CITE = re.compile(r"\[([a-z][a-z0-9.\-]*)\]")
BACKTICK = re.compile(r"(?<!\[)`([a-z][a-z0-9.\-]*)`")
META = [  # paragraphs that are about the node, not part of its statement or proof
    ("status", re.compile(r"\*\*Status\.\*\*")),
    ("source_note", re.compile(r"\*Source note:\*")),
    ("source", re.compile(r"\*Source:\*")),
    ("recorded_in_advance", re.compile(r"\*Recorded in advance\*")),
    ("mathlib", re.compile(r"\*Mathlib:\*")),
    ("implementation_note", re.compile(r"\*Implementation note\.\*")),
    ("uses_line", re.compile(r"Uses:")),
    ("unresolved_dependencies", re.compile(r"Unresolved dependencies:")),
]
# a proof that says it is not one
WHOLE_INPUT = re.compile(
    r"\A(?:This is the recorded (?:classical )?input|The clauses are the recorded (?:classical )?input"
    r"|\*Recorded classical interface\.\*|Two recorded inputs are used"
    r"|The statement is the input recorded in the reference)|not discharged here", re.S)
OMITTED = re.compile(r"\AOmitted\b")
PART_INPUT = re.compile(
    r"recorded\s+(?:classical\s+)?(?:input|interface)|Quoted rather than proved"
    r"|Reference for the classical inputs|classical input of the source note", re.S)
LIT = re.compile(
    r"Stacks|\bTag\b|\bSGA\b|\bEGA\b|\bFGA\b|\bBBD\b|Milne|Hartshorne|Mumford|Bhatt|Scholze|Conrad|Kiehl|Freitag"
    r"|Weil II|Laumon|Katz|Kleiman|Bosch|Matsumura|Bourbaki|Waterhouse|Jacobson|Milnor|Illusie|Gabber|Weibel|Neeman")
STACKS_TAG = re.compile(r"stacks\.math\.columbia\.edu/tag/([0-9A-Z]{4})|\bTags?\s+\[?`?([0-9][0-9A-Z]{3})\b")
OTHER_REF = re.compile(
    r"(SGA\s*\d(?:\s*1/2|½)?|EGA\s*[IV]+|\bFGA\b|\bBBD\b|Weil II|Milne|Hartshorne|Mumford|Bhatt|Scholze|Conrad|Kiehl"
    r"|Freitag|Laumon|Katz|Kleiman|Bosch|Matsumura|Bourbaki|Waterhouse|Jacobson|Milnor|Illusie|Gabber|Weibel|Neeman)")
ALWAYS_REF = re.compile(r"SGA|EGA|FGA|BBD|Weil II")
LOCATOR = re.compile(r"\*[A-Z][^*]{6,}\*|(?:Ch\.|Chapter|§|Section|Sect\.|Th\.|Theorem|Thm\.|Exp\.|Exposé|Lemma|Prop\.|Proposition|Cor\.)\s*[\dIVX]")
LABEL = re.compile(r"\A## |\A(\*{1,2})(?:[^*\n]{1,90}?[.:)]\1(?!\*)|[^*\n]{1,90}?\1[.:])")
LIST_ITEM = re.compile(r"\A(?:\d+\.|[-*])\s+")


# ---------------------------------------------------------------- the blueprint files

def parse_file(p: pathlib.Path) -> dict:
    m = re.match(r"\+\+\+\n(.*?)\n\+\+\+\n?(.*)", p.read_text(), re.S)
    if not m:
        raise SystemExit(f"no frontmatter: {p}")
    fm, body = m.groups()
    d = {"path": p, "body": body}
    for line in fm.splitlines():
        k, _, v = line.partition("=")
        k, v = k.strip(), v.strip()
        if v.startswith("["):
            d[k] = re.findall(r'"((?:[^"\\]|\\.)*)"', v)
        elif v.startswith('"'):
            d[k] = json.loads(v)
        else:
            d[k] = int(v) if v.lstrip("-").isdigit() else v
    for k in ("uses", "lean", "tags"):
        d.setdefault(k, [])
    return d


def paragraphs(text: str) -> list[str]:
    return [x.strip("\n") for x in re.split(r"\n[ \t]*\n", text) if x.strip()]


def split_meta(text: str) -> tuple[str, list[dict]]:
    """The text without its meta paragraphs, and those paragraphs."""
    keep, meta = [], []
    for para in paragraphs(text):
        for label, rx in META:
            if rx.match(para.strip()):
                meta.append({"label": label, "text": para.strip()}); break
        else:
            keep.append(para)
    return "\n\n".join(keep).strip(), meta


def versions(body: str) -> tuple[list[dict], bool]:
    """Split a body at its `## ` headings into versions {statement, proof}. `## Detailed form` opens a new
    version; `## Proof` opens the proof of the current one; any other heading is an embedded statement or
    remark and stays, with its heading, in the proof part of the current version."""
    parts = re.split(r"^## (.*)$", body, flags=re.M)
    vs = [{"statement": parts[0], "proof": None}]
    embedded = False
    for j in range(1, len(parts), 2):
        head, text = parts[j].strip(), parts[j + 1]
        if head == "Detailed form":
            vs.append({"statement": text, "proof": None})
        elif head == "Proof" and vs[-1]["proof"] is None:
            vs[-1]["proof"] = text
        else:
            embedded = embedded or head != "Proof"
            vs[-1]["proof"] = (vs[-1]["proof"] or "") + f"\n\n## {head}\n\n" + text
    return vs, embedded


def is_display(para: str) -> bool:
    s = para.strip()
    return s.startswith("$$") and s.endswith("$$") and len(s) >= 4


def sentences(paras: list[str]) -> list[str]:
    """Join a displayed formula to the paragraph before it, and the text after it when the formula does not
    end the sentence."""
    out: list[str] = []
    glue = False
    for para in paras:
        if is_display(para) and out:
            out[-1] += "\n\n" + para
            inner = para.strip()[2:-2].strip()
            inner = re.sub(r"(\\(?:qedhere|qquad|quad|,|;|!)|\s)+\Z", "", inner)
            glue = not inner.endswith(".")
        elif glue and out and not LABEL.match(para.strip()) and not LIST_ITEM.match(para.strip()):
            out[-1] += "\n\n" + para; glue = False
        else:
            out.append(para); glue = False
    return out


def steps_of(proof: str) -> tuple[list[str], str]:
    """The proof cut into steps, and how: 'labels', 'list' or 'paragraphs'."""
    units = sentences(paragraphs(proof))
    if not units:
        return [], "none"
    labelled = [bool(LABEL.match(u.strip())) for u in units]
    if sum(labelled) >= 2:
        out: list[str] = []
        for u, lab in zip(units, labelled):
            if lab or not out:
                out.append(u)
            else:
                out[-1] += "\n\n" + u
        return out, "labels"
    items: list[str] = []
    n_items = 0
    for u in units:
        lines = u.split("\n")
        if re.match(r"\d+\.\s+", lines[0]):
            cur: list[str] = []
            for line in lines:               # one paragraph may hold several items
                if re.match(r"\d+\.\s+", line) and cur:
                    items.append("\n".join(cur)); cur = []
                if re.match(r"\d+\.\s+", line):
                    n_items += 1
                cur.append(line)
            items.append("\n".join(cur))
        elif items and u.startswith(("  ", "\t")):
            items[-1] += "\n\n" + u            # an indented continuation of the item
        else:
            items.append(u)
    if n_items >= 2:
        return items, "list"
    return units, "paragraphs"


# ---------------------------------------------------------------- Lean sources (text only)

HEAD = re.compile(
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|local|scoped|public)\s+)*"
    r"(def|theorem|lemma|instance|abbrev|structure|class|inductive|opaque|axiom|alias)\s+([^\s({\[:⦃]+)")
CONT = re.compile(r"(?:\||where\b|termination_by\b|decreasing_by\b|deriving\b|with\b|[)}\]⟩])")
SORRY = re.compile(r"(?<![\w.'])(?:sorry|admit)(?![\w'])")


def code_only(text: str) -> str:
    """The source with comments and string literals blanked, line structure kept."""
    out = []
    for kind, a, b in li.lex(text):
        seg = text[a:b]
        out.append(seg if kind in ("code", "ws") else "".join("\n" if c == "\n" else " " for c in seg))
    return "".join(out)


def index_file(path: pathlib.Path, module: str) -> dict[str, dict]:
    """qualified name -> {module, line, kind, sorry_free, body_lines}; fields and constructors point at their type."""
    try:
        lines = code_only(path.read_text()).split("\n")
    except (OSError, li.LexError, UnicodeDecodeError):
        return {}
    out, stack, cur = {}, [], None

    def close(end: int):
        nonlocal cur
        if cur is None:
            return
        block = lines[cur["start"]:end]
        text = "\n".join(block)
        m = re.search(r":=|\bwhere\b", text)
        if m:
            body = text[m.end():]
            first, _, rest = body.partition("\n")
            n = sum(1 for x in rest.split("\n") if x.strip()) + (1 if first.strip() not in ("", "by") else 0)
        else:
            n = sum(1 for x in block[1:] if x.strip().startswith("|"))
        rec = {"module": module, "line": cur["start"] + 1, "kind": cur["kind"],
               "sorry_free": not SORRY.search(text), "body_lines": n}
        out.setdefault(cur["name"], rec)
        if cur["kind"] in ("structure", "class", "inductive"):
            for x in block[1:]:
                f = re.match(r"\s+(?:\|\s*)?([A-Za-z_][\w']*)\s*(?::|\(|\{|\[|$)", x)
                if f:
                    out.setdefault(cur["name"] + "." + f.group(1), dict(rec, kind="field"))
        cur = None

    for n, line in enumerate(lines):
        if not line.strip() or line[0].isspace():
            continue
        m = re.match(r"namespace\s+(\S+)", line)
        if m:
            close(n); stack += m.group(1).replace("«", "").replace("»", "").split("."); continue
        if re.match(r"(?:noncomputable\s+|public\s+)*section\b", line):
            close(n); stack.append(None); continue
        e = re.match(r"end\b\s*(\S*)", line)
        if e:                                    # `namespace A.B` may be closed by `end B` and `end A`
            close(n)
            for _ in range(max(1, len(e.group(1).split(".")) if e.group(1) else 1)):
                if stack:
                    stack.pop()
            continue
        h = HEAD.match(line)
        if h:
            close(n)
            name = h.group(2).replace("«", "").replace("»", "")
            ns = [x for x in stack if x]
            name = name[7:] if name.startswith("_root_.") else ".".join(ns + [name])
            cur = {"start": n, "kind": h.group(1), "name": name}
            continue
        if re.match(r"@\[[^\]]*\]\s*$", line):
            close(n); continue
        if cur is not None and CONT.match(line):
            continue
        close(n)
    close(len(lines))
    return out


class LeanTree:
    def __init__(self, root: pathlib.Path | None, branch: str, lazy: bool = False, sub: str = ""):
        self.root, self.branch, self.idx, self.done, self.sub = root, branch, {}, set(), sub
        if root and root.is_dir() and not lazy:
            for p in sorted(root.rglob("*.lean")):
                self._add(p)

    def _add(self, p: pathlib.Path):
        if p in self.done:
            return
        self.done.add(p)
        mod = ".".join(p.relative_to(self.root).with_suffix("").parts)
        for k, v in index_file(p, mod).items():
            self.idx.setdefault(k, v)

    def find(self, name: str) -> dict | None:
        if name in self.idx:
            return self.idx[name]
        if not (self.root and self.root.is_dir()):
            return None
        last = name.split(".")[-1]
        pat = rf"(def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|alias|axiom)\s+([\w.']+\.)?«?{re.escape(last)}»?([^\w.'!?]|$)"
        try:
            r = subprocess.run(["rg", "-l", "-j1", "-g", "*.lean", "-e", pat, str(self.root / self.sub)],
                               capture_output=True, text=True, timeout=120)
        except (OSError, subprocess.TimeoutExpired):
            return None
        for f in sorted(r.stdout.split()):
            self._add(pathlib.Path(f))
        return self.idx.get(name)


# ---------------------------------------------------------------- the import

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-master", default=str(SCRATCH / "tree_master"))
    ap.add_argument("--lean-slopmaster2", default=str(SCRATCH / "tree_slopmaster2"))
    ap.add_argument("--mathlib", default=str(DEFAULT_MATHLIB))
    ap.add_argument("--dry", action="store_true")
    a = ap.parse_args()
    today = datetime.date.today().isoformat()

    raw: dict[str, dict] = {}
    for p in sorted(BP.rglob("*.md")):
        d = parse_file(p)
        if d["id"] in raw:
            raise SystemExit(f"duplicate id {d['id']}: {p} and {raw[d['id']]['path']}")
        raw[d["id"]] = d
    ids = set(raw)

    def cites(text: str) -> list[str]:
        seen = []
        for m in sorted(list(CITE.finditer(text)) + list(BACKTICK.finditer(text)), key=lambda m: m.start()):
            if m.group(1) in ids and m.group(1) not in seen:
                seen.append(m.group(1))
        return seen

    # which files are nodes
    node_kind: dict[str, str] = {}
    for i, d in raw.items():
        if d["kind"] == "definition":
            node_kind[i] = "definition"
        elif d["kind"] in ("theorem", "lemma"):
            node_kind[i] = "statement"
    promoted = set()
    for i, d in raw.items():
        if i in node_kind:
            for c in cites(d["body"]):
                if raw[c]["kind"] == "remark" and "latex:openproblem" in raw[c]["tags"]:
                    promoted.add(c)
    changed = True
    while changed:                               # an open problem that a promoted open problem cites
        changed = False
        for i in list(promoted):
            for c in cites(raw[i]["body"]):
                if raw[c]["kind"] == "remark" and "latex:openproblem" in raw[c]["tags"] and c not in promoted:
                    promoted.add(c); changed = True
    for i in promoted:
        node_kind[i] = "statement"

    master = LeanTree(pathlib.Path(a.lean_master) if a.lean_master else None, "master")
    slop = LeanTree(pathlib.Path(a.lean_slopmaster2) if a.lean_slopmaster2 else None, "slopmaster2", lazy=True)
    mathlib = LeanTree(pathlib.Path(a.mathlib) if a.mathlib else None, "mathlib", lazy=True, sub="Mathlib")
    mathlib_commit = ""
    if a.mathlib and (pathlib.Path(a.mathlib) / ".git").exists():
        r = subprocess.run(["git", "-C", a.mathlib, "rev-parse", "--short", "HEAD"], capture_output=True, text=True)
        mathlib_commit = r.stdout.strip()

    nodes: dict[str, dict] = {}
    notes: dict[str, dict] = {}
    dropped: list[tuple[str, str, str]] = []

    def section_of(d) -> str:
        return d["path"].relative_to(BP).parts[0]

    def rel(d) -> str:
        return str(d["path"].relative_to(ROOT))

    for i, d in raw.items():
        if i not in node_kind:
            notes[i] = {
                "id": i, "kind": d["kind"], "title": d.get("title", ""),
                "text": d["body"].strip(),
                "source": {"document": rel(d), "place": f"order {d.get('order')}"},
                "cites": [c for c in cites(d["body"]) if c != i],
                "blueprint_uses": d["uses"], "blueprint_lean": d["lean"], "blueprint_tags": d["tags"],
                "_section": section_of(d),
            }
            continue
        flags: list[str] = []
        vs, embedded = versions(d["body"])
        chosen = vs[-1]
        statement, meta_s = split_meta(chosen["statement"])
        proof_text_full = (chosen["proof"] or "").strip()
        proof_text, meta_p = split_meta(proof_text_full)
        meta = [dict(m, where="statement") for m in meta_s] + [dict(m, where="proof") for m in meta_p]
        if len(vs) > 1:
            flags.append("detailed_form")
        if sum(1 for v in vs if v["proof"] is not None) >= 2:
            flags.append("two_proofs")
        if embedded:
            flags.append("embedded_statements")
        if len(vs) > 2:
            flags.append("multiple_detailed_forms")
        sketch = []
        for v in vs[:-1]:
            s_txt = v["statement"].strip(); p_txt = (v["proof"] or "").strip()
            for m in split_meta(s_txt)[1]:           # a status or source paragraph may sit in the first version only
                if m["label"] in ("status", "source", "source_note", "mathlib", "recorded_in_advance") and \
                        not any(x["label"] == m["label"] and x["text"] == m["text"] for x in meta):
                    meta.append(dict(m, where="sketch statement"))
            sketch.append({"statement": s_txt, "proof": p_txt,
                           "cites": [c for c in cites(s_txt + "\n" + p_txt) if c != i]})

        # dependencies
        self_cite = False

        def resolve(cs: list[str], where: str) -> list[str]:
            nonlocal self_cite
            out = []
            for c in cs:
                if c == i:
                    self_cite = True; dropped.append((i, c, where + " (self)")); continue
                if c not in node_kind:
                    if raw[c]["kind"] == "remark":
                        dropped.append((i, c, where))
                    continue                           # a section id in the text is a pointer, not a dependency
                if c not in out:
                    out.append(c)
            return out

        if BACKTICK.search(statement + proof_text) and any(m.group(1) in ids for m in BACKTICK.finditer(statement + proof_text)):
            flags.append("backtick_citation")
        stmt_deps = resolve(cites(statement), "statement")
        steps_txt, how = steps_of(proof_text)
        steps = []
        for s in steps_txt:
            u = resolve(cites(s), "proof")
            steps.append({"text": s, "uses": u, "elementary": False if u else None})
        proof_deps = []
        for s in steps:
            for u in s["uses"]:
                if u not in proof_deps:
                    proof_deps.append(u)
        cited = set(stmt_deps) | set(proof_deps)
        uses_line = []
        for m in meta:
            if m["label"] == "uses_line":
                uses_line += [c for c in cites(m["text"]) if c not in uses_line]
        declared = list(dict.fromkeys(d["uses"] + uses_line))
        uncited = [u for u in declared if u not in cited and u != i]
        text_cites_all = cites(statement + "\n" + proof_text)
        if any(c not in d["uses"] and c != i for c in text_cites_all):
            flags.append("cites_outside_uses")
        uses_not_cited = []
        if len(d["uses"]) > PADDED:
            if uncited:
                flags.append("padded_uses")
        else:
            for u in uncited:
                if u not in ids:
                    continue
                if u not in node_kind:
                    if raw[u]["kind"] == "remark":
                        dropped.append((i, u, "uses"))
                    continue
                uses_not_cited.append(u)
                if node_kind[i] == "definition" or node_kind[u] == "definition":
                    stmt_deps.append(u)
                else:
                    proof_deps.append(u)
        if self_cite:
            flags.append("self_citation")
        if any(x[0] == i and "(self)" not in x[2] for x in dropped):
            flags.append("cites_remark")

        # is the proof a proof
        proof_words = len(proof_text.split())
        blueprint_proof_steps = None
        if node_kind[i] == "statement" or proof_text:
            if not proof_text:
                steps = []
                if node_kind[i] == "statement":
                    flags.append("no_proof_in_blueprint")
            elif OMITTED.match(proof_text):
                flags += ["citation_only", "proof_omitted"]; blueprint_proof_steps, steps = steps, []
            elif WHOLE_INPUT.search(proof_text):
                flags.append("undischarged_input"); blueprint_proof_steps, steps = steps, []
            elif PART_INPUT.search(proof_text):
                flags += ["undischarged_input", "partial_undischarged_input"]; blueprint_proof_steps, steps = steps, []
        if not steps and node_kind[i] == "statement" and any(v["proof"] for v in sketch):
            flags.append("other_version_has_proof")
        if i in promoted:
            flags.append("open_problem")
        if LIT.search(proof_text):
            flags.append("proof_cites_literature")
        if steps and proof_words > LONG_PROOF and len(set(proof_deps) - set(uses_not_cited)) <= FEW_DEPS:
            flags.append("long_proof_few_deps")
        status_txt = " ".join(m["text"] for m in meta if m["label"] == "status")
        if re.search(r"Bypassed by the formalized route", d["body"]):
            flags.append("bypassed")
        if any(m["label"] == "unresolved_dependencies" for m in meta) or \
                re.search(r"(?:Definitions?|Propositions?|Lemmas?|Theorems?|Corollar(?:y|ies))\s+\*[^*\n]+\*", statement + proof_text):
            flags.append("unresolved_references")

        # the source
        ext = []
        whole = d["body"]
        for m in STACKS_TAG.finditer(whole):
            t = m.group(1) or m.group(2)
            e = {"document": "Stacks Project", "place": f"Tag {t}"}
            if e not in ext:
                ext.append(e)
        for sent in re.split(r"(?<=[.;])\s+(?=[A-Z*(])", " ".join(re.sub(r"^## .*$", "", whole, flags=re.M).split())):
            for m in OTHER_REF.finditer(sent):
                if not (ALWAYS_REF.match(m.group(1)) or LOCATOR.search(sent)):
                    continue
                e = {"document": m.group(1), "place": sent[:400]}
                if not any(x["document"] == e["document"] and x["place"] == e["place"] for x in ext):
                    ext.append(e)
        source = {"document": rel(d), "place": f"node {i}, order {d.get('order')}"}
        if ext:
            source["external"] = ext
        src_notes = [m["text"] for m in meta if m["label"] in ("source", "source_note", "recorded_in_advance")]
        if src_notes:
            source["note"] = src_notes

        # Lean
        lean_found, lean_missing = [], []
        for name in d["lean"]:
            rec, br = master.find(name), "master"
            if rec is None:
                rec, br = slop.find(name), "slopmaster2"
            if rec is None:
                lean_missing.append(name); continue
            lean_found.append({"module": rec["module"], "declaration": name, "branch": br, "line": rec["line"],
                               "sorry_free": rec["sorry_free"], "body_lines": rec["body_lines"]})
        lean = None
        if lean_found:
            lean = dict(lean_found[0])
            if len(lean_found) > 1:
                lean["others"] = lean_found[1:]; flags.append("lean_multiple")
            if any(x["body_lines"] > BODY_LINES for x in lean_found):
                flags.append("lean_over_10_lines")
        if lean_missing:
            flags.append("lean_not_found")

        # Mathlib: only what the blueprint itself names
        searches, match, status = [], None, None
        ml = [m for m in meta if m["label"] == "mathlib"]
        if ml and a.mathlib and pathlib.Path(a.mathlib).is_dir():
            names = re.findall(r"`([^`]+)`", ml[0]["text"])
            found = []
            for name in names:
                rec = mathlib.find(name)
                searches.append({"tool": f"text search of the local Mathlib checkout ({mathlib_commit or a.mathlib})",
                                 "query": name,
                                 "results": [f"{rec['module']}:{rec['line']} ({rec['kind']})"] if rec else [],
                                 "date": today})
                if rec:
                    found.append(name)
            if names and len(found) == len(names):
                match, status = found, "mathlib"
            else:
                flags.append("mathlib_named_not_confirmed")
        elif re.search(r"[Mm]athlib", d["body"]):
            flags.append("mentions_mathlib")
        for name in lean_missing:
            if a.mathlib and pathlib.Path(a.mathlib).is_dir():
                rec = mathlib.find(name)
                searches.append({"tool": f"text search of the local Mathlib checkout ({mathlib_commit or a.mathlib})",
                                 "query": name,
                                 "results": [f"{rec['module']}:{rec['line']} ({rec['kind']})"] if rec else [],
                                 "date": today})
                if rec and "lean_names_mathlib_declaration" not in flags:
                    flags.append("lean_names_mathlib_declaration")

        n = {
            "id": i, "kind": node_kind[i],
        }
        if i == TARGET:
            n["target"] = True
        n.update({
            "title": d.get("title", ""),
            "statement": statement,
            "source": source,
            "stmt_deps": stmt_deps,
            "proof": steps,
            "proof_deps": proof_deps,
            "proof_origin": ({"by": "agent", "document": rel(d), "place": "## Proof"} if steps else None),
            "mathlib_searches": searches,
            "mathlib_match": match,
            "status": status,           # filled below
            "merged_into": None,
            "import_flags": flags,
            "blueprint_kind": d["kind"],
            "blueprint_order": d.get("order"),
            "blueprint_uses": d["uses"],
        })
        if lean:
            n["lean"] = lean
        if d["lean"]:
            n["blueprint_lean"] = d["lean"]
        if lean_missing:
            n["blueprint_lean_not_found"] = lean_missing
        if d["tags"]:
            n["blueprint_tags"] = d["tags"]
        if uses_not_cited:
            n["uses_not_cited"] = uses_not_cited
        if blueprint_proof_steps is not None:
            n["blueprint_proof_text"] = proof_text
            n["blueprint_proof_steps"] = blueprint_proof_steps
        if steps:
            n["proof_split_by"] = how
        if sketch:
            n["blueprint_sketch"] = sketch
        if meta:
            n["blueprint_notes"] = meta
        n["_section"] = section_of(d)
        nodes[i] = n

    # status and reachability
    def unfolded(n) -> bool:
        if n["status"] == "mathlib":
            return True
        if n["kind"] == "definition":
            return bool(n.get("lean")) or bool(n["stmt_deps"])
        return bool(n["proof"])

    for n in nodes.values():
        if n["status"] != "mathlib":
            n["status"] = "imported" if unfolded(n) else "unsplit"
    reach, todo = set(), [TARGET]
    while todo:
        x = todo.pop()
        if x in reach:
            continue
        reach.add(x)
        todo += [y for y in nodes[x]["stmt_deps"] + nodes[x]["proof_deps"] if y in nodes]
    for i, n in nodes.items():
        if i not in reach:
            n["import_flags"].append("unreachable")
    from check_dag import sccs
    graph = {i: list(dict.fromkeys(n["stmt_deps"] + n["proof_deps"])) for i, n in nodes.items()}
    cycles = [c for c in sccs(graph) if len(c) > 1]
    for c in cycles:
        for i in c:
            nodes[i]["import_flags"].append("in_cycle")

    # report
    rep = {
        "date": today,
        "blueprint_files": len(raw),
        "nodes": len(nodes),
        "by_kind": dict(collections.Counter(n["kind"] for n in nodes.values())),
        "by_status": dict(collections.Counter(n["status"] for n in nodes.values())),
        "notes": dict(collections.Counter(n["kind"] for n in notes.values())),
        "promoted_open_problems": sorted(promoted),
        "reachable": len(reach),
        "flags": dict(sorted(collections.Counter(f for n in nodes.values() for f in n["import_flags"]).items())),
        "flags_reachable": dict(sorted(collections.Counter(f for i, n in nodes.items() if i in reach for f in n["import_flags"]).items())),
        "stage1_reachable_unsplit": sum(1 for i in reach if nodes[i]["status"] == "unsplit"),
        "proof_split_by": dict(collections.Counter(n.get("proof_split_by", "-") for n in nodes.values())),
        "steps": sum(len(n["proof"]) for n in nodes.values()),
        "steps_citing_nothing": sum(1 for n in nodes.values() for s in n["proof"] if not s["uses"]),
        "lean_records": sum(1 for n in nodes.values() if n.get("lean")),
        "lean_by_branch": dict(collections.Counter(n["lean"]["branch"] for n in nodes.values() if n.get("lean"))),
        "lean_sorry_free_all": sum(1 for n in nodes.values() if n.get("lean") and all(x["sorry_free"] for x in [n["lean"]] + n["lean"].get("others", []))),
        "blueprint_lean_names": sum(len(n.get("blueprint_lean", [])) for n in nodes.values()),
        "blueprint_lean_names_not_found": sum(len(n.get("blueprint_lean_not_found", [])) for n in nodes.values()),
        "mathlib_leaves": sorted(i for i, n in nodes.items() if n["status"] == "mathlib"),
        "mathlib_queries": sum(len(n["mathlib_searches"]) for n in nodes.values()),
        "cycles": len(cycles),
        "cycle_sizes": sorted((len(c) for c in cycles), reverse=True),
        "stage1_reachable_unsplit_by_flag": dict(sorted(collections.Counter(
            f for i in reach if nodes[i]["status"] == "unsplit" for f in
            (nodes[i]["import_flags"] if nodes[i]["kind"] == "statement" else ["definition naming no notion and without Lean"])
            if f in ("undischarged_input", "partial_undischarged_input", "citation_only", "proof_omitted",
                     "no_proof_in_blueprint", "open_problem", "definition naming no notion and without Lean")).items())),
        "dropped_edges": len(dropped),
        "dropped_edges_to_remarks": sum(1 for x in dropped if "(self)" not in x[2]),
        "dropped_self_citations": sum(1 for x in dropped if "(self)" in x[2]),
    }
    print(json.dumps(rep, indent=1, ensure_ascii=False))
    if a.dry:
        return 0

    for sub in ("nodes", "notes"):
        if (ROOT / "dag" / sub).exists():
            shutil.rmtree(ROOT / "dag" / sub)
    for kind, coll in (("nodes", nodes), ("notes", notes)):
        for i, n in coll.items():
            sec = n.pop("_section")
            out = ROOT / "dag" / kind / sec / f"{i}.json"
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(n, indent=1, ensure_ascii=False) + "\n")
    seen, rows = set(), []
    for x in dropped:
        if x not in seen:
            seen.add(x); rows.append(x)
    (ROOT / "dag" / "notes" / "dropped_edges.tsv").write_text(
        "from\tto\twhere\n" + "".join(f"{a_}\t{b_}\t{c_}\n" for a_, b_, c_ in sorted(rows)))
    (ROOT / "dag" / "import_report.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
