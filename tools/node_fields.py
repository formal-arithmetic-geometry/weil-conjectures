#!/usr/bin/env python3
"""Which fields of a node a split sets, and which are the maintainer's (decision of the human, 2026-10-10, evening).

A delivery takes each existing node file as it is on origin/sheaf-dag and sets only the fields a split owns;
every other field of an existing node is the maintainer's and must come through unchanged. The authoritative
list is here and in tools/README.md ("Fields of a node: who sets them"); tools/preflight_delivery.py check 9 and
tools/merge_delivery.py enforce it.

    python3 tools/node_fields.py        prints both lists
"""
from __future__ import annotations

# Top-level fields a split sets on its item (and on the new nodes it creates, which it writes whole).
SPLIT_OWNS = (
    "status",            # unsplit -> split, or mathlib for a leaf
    "statement",         # only a correction named in the report (delivery-errors E7); never silently
    "stmt_deps",         # the nodes the (corrected) statement cites
    "proof",             # the steps {text, uses, elementary}
    "proof_deps",        # the union of the steps' uses
    "proof_origin",      # {by: document|agent, document, place}
    "split_report",      # the report entry, with its `blueprint` entry
    "mathlib_searches",  # the searches run (three kinds for a new node)
    "mathlib_match",     # a verified declaration, file, line for a Mathlib leaf
    "mathlib_candidate", # a declaration that is close but not the node (e.g. SGA1 Galois categories)
    "lean_candidates",   # a slopmaster2 declaration reported as an attachment, for the maintainer to verify
)
# Inside `blueprint`: a split fills `from.place` when it is "unspecified" and `same_as`; `is` is the maintainer's.
SPLIT_OWNS_BLUEPRINT = ("from", "same_as")

# Everything else is the maintainer's. Named here so that the list is explicit; a key not in SPLIT_OWNS is the
# maintainer's whether or not it is listed.
MAINTAINER = (
    "id", "kind", "title", "chapter", "unit", "source", "merged_into",
    "created",            # who created the node and from which item (set when the new node is merged)
    "reviewed",           # the maintainer's acceptance line
    "lead_note",          # the maintainer's notes on the node
    "tool_uses",          # off-unit non-leaf nodes the item uses as tools (recorded at review)
    "import_flags",       # e.g. ["unreachable"]
    "lean", "lean_audit", "lean_notes", "lean_names_rejected",   # the Lean side: attachments and the audit
    "blueprint_lean", "blueprint_lean_not_found", "blueprint_kind", "blueprint_order", "blueprint_uses",
    "blueprint_tags", "blueprint_notes", "blueprint_sketch", "blueprint_proof_text", "blueprint_proof_steps",
    "proof_split_by", "uses_not_cited", "pointers", "note", "target", "target_former", "mathlib_match_withdrawn",
)
MAINTAINER_BLUEPRINT = ("is",)

# Stage 2 (stages/2-statements.md; format of the lead, 2026-10-11): a stage-2 delivery sets the field `lean` of its node
# and nothing else. `lean` stays in MAINTAINER for stage 1: a split never sets it.
STAGE2_OWNS = ("lean",)
# STAGE 2 EXTRA NODES (decision of the human, 2026-10-11 05:55 UTC): on the ITEM only, `stmt_deps` may also change, and
# only by ADDING new definition nodes of the same delivery (tools/stage2_delivery.py read_delivery enforces it); a
# dependency node changes only in STAGE2_OWNS; a new definition node is written whole (stage2_delivery.check_new_node).
STAGE2_ITEM_ALSO = ("stmt_deps",)
# STAGE 2 STATEMENT CORRECTION (decision of the human, 2026-10-11 06:22 UTC; coord/STATE.md): the ITEM may also change
# `statement`, and only as far as the correction forces it `stmt_deps`, `proof`, `proof_deps`; it then carries
# `statement_change` (check_statement_change). The report gets `## Statement corrected`.
STAGE2_ITEM_CORRECTION = ("statement", "stmt_deps", "proof", "proof_deps", "statement_change")
STATEMENT_CHANGE_KEYS = ("date", "by", "old_statement", "what", "source", "citers")
# old_<field> present iff <field> changed; `previous` iff the base node already had a statement_change
STATEMENT_CHANGE_OPTIONAL = ("old_stmt_deps", "old_proof", "old_proof_deps", "previous")
_MISSING = object()


def correction_fields(base: dict, head: dict) -> list[str]:
    """The fields of STAGE2_ITEM_CORRECTION but `stmt_deps` that differ between base and head: non-empty means the
    delivery corrects the item (statement, proof, proof_deps or a new statement_change)."""
    return [k for k in ("statement", "proof", "proof_deps", "statement_change")
            if base.get(k, _MISSING) != head.get(k, _MISSING)]


def check_statement_change(base_node: dict, head_node: dict, citers=None) -> list[str]:
    """The errors of a stage-2 statement correction of the item (coord/STATE.md, STAGE 2 STATEMENT CORRECTION).
    Nothing to check (no error) when statement, proof, proof_deps and statement_change are all as on the base (an
    older stage-1 statement_change, e.g. `by: "L"`, is left alone). `citers`: the ids of the base nodes whose
    stmt_deps or proof_deps contain the item (None: the set is not compared)."""
    import re
    errs: list[str] = []
    e = errs.append
    b, h = base_node or {}, head_node or {}
    ch = correction_fields(b, h)
    if not ch:
        return errs
    stmt_changed = b.get("statement") != h.get("statement")
    sc = h.get("statement_change", _MISSING)
    sc_new = b.get("statement_change", _MISSING) != sc
    if not stmt_changed:
        if sc_new:
            e("statement_change is new or changed but the statement is as on the base (a statement_change records a "
              "correction of the statement)")
        other = [k for k in ("proof", "proof_deps") if k in ch]
        if other:
            e(f"the item changed in {', '.join(other)} without a statement correction (proof and proof_deps change only "
              "as far as a correction of the statement forces it)")
        return errs
    if not sc_new or sc is _MISSING:
        e("the statement changed but the node has no new `statement_change` (a statement changed silently is H7): add "
          "{date, by, old_statement, what, source, citers} and the report section `## Statement corrected`")
        return errs
    if not isinstance(sc, dict):
        e("statement_change is not a JSON object"); return errs
    keys = set(sc)
    missing = [k for k in STATEMENT_CHANGE_KEYS if k not in keys]
    extra = sorted(keys - set(STATEMENT_CHANGE_KEYS) - set(STATEMENT_CHANGE_OPTIONAL))
    if missing:
        e(f"statement_change lacks {', '.join(missing)}")
    if extra:
        e(f"statement_change has unknown key(s) {', '.join(extra)} (allowed: {', '.join(STATEMENT_CHANGE_KEYS + STATEMENT_CHANGE_OPTIONAL)})")
    if "date" in sc and not (isinstance(sc["date"], str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", sc["date"])):
        e(f"statement_change.date {sc.get('date')!r} is not YYYY-MM-DD")
    if "by" in sc and not (isinstance(sc["by"], str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]* stage 2", sc["by"])):
        e(f"statement_change.by {sc.get('by')!r} is not of the form \"<G> stage 2\"")
    if "old_statement" in sc and sc["old_statement"] != b.get("statement"):
        e("statement_change.old_statement is not the base statement verbatim")
    if "what" in sc and not (isinstance(sc["what"], str) and sc["what"].strip()):
        e("statement_change.what is empty: say what was wrong (the counterexample, or what could not be typed and why)")
    if "source" in sc:
        s = sc["source"]
        if not (isinstance(s, dict) and set(s) == {"document", "place"} and all(isinstance(s[k], str) and s[k].strip() for k in s)):
            e("statement_change.source is not {document, place} with non-empty strings")
    for f, k in (("stmt_deps", "old_stmt_deps"), ("proof", "old_proof"), ("proof_deps", "old_proof_deps")):
        changed = b.get(f, _MISSING) != h.get(f, _MISSING)
        if changed and k not in sc:
            e(f"{f} changed but statement_change has no {k}")
        elif not changed and k in sc:
            e(f"statement_change has {k} but {f} did not change")
        elif changed and sc[k] != b.get(f):
            e(f"statement_change.{k} is not the base {f} verbatim")
    if "statement_change" in b:
        if "previous" not in sc:
            e("the base node already has a statement_change: the new record carries it whole under `previous`")
        elif sc["previous"] != b["statement_change"]:
            e("statement_change.previous is not the base node's statement_change verbatim")
    elif "previous" in sc:
        e("statement_change.previous given but the base node has no statement_change")
    if "citers" in sc:
        cl = sc["citers"]
        if not isinstance(cl, list):
            e("statement_change.citers is not a list")
        else:
            ids = []
            for i, c in enumerate(cl):
                if not (isinstance(c, dict) and set(c) == {"id", "holds", "note"}):
                    e(f"statement_change.citers[{i}] is not {{id, holds, note}}"); continue
                if not isinstance(c["id"], str) or not isinstance(c["holds"], bool) or not (isinstance(c["note"], str) and c["note"].strip()):
                    e(f"statement_change.citers[{i}]: id a string, holds true|false, note a non-empty line")
                ids.append(c["id"])
            dup = sorted({x for x in ids if ids.count(x) > 1})
            if dup:
                e(f"statement_change.citers names {', '.join(map(str, dup))} twice")
            if citers is not None:
                want, got = set(citers), {x for x in ids if isinstance(x, str)}
                if want - got:
                    e(f"statement_change.citers misses {', '.join(sorted(want - got))} (every node whose stmt_deps or "
                      f"proof_deps name the item: grep -rl '\"{h.get('id')}\"' dag/nodes)")
                if got - want:
                    e(f"statement_change.citers names {', '.join(sorted(got - want))}, which do not cite the item on the base")
    return errs


def changed_maintainer_fields(base: dict, head: dict) -> list[str]:
    """The maintainer's fields that differ between the committed node (base) and the delivered one (head)."""
    out = []
    for k in sorted(set(base) | set(head)):
        if k in SPLIT_OWNS or k == "blueprint":
            continue
        if base.get(k) != head.get(k):
            out.append(k)
    b0, h0 = base.get("blueprint") or {}, head.get("blueprint") or {}
    for k in MAINTAINER_BLUEPRINT:
        if b0.get(k) != h0.get(k):
            out.append(f"blueprint.{k}")
    return out


def changed_fields_except(base: dict, head: dict, owns=STAGE2_OWNS) -> list[str]:
    """Every top-level field that differs between base and head, except the fields in `owns` (stage 2: only `lean`)."""
    return [k for k in sorted(set(base) | set(head)) if k not in owns and base.get(k, KeyError) != head.get(k, KeyError)]


if __name__ == "__main__":
    print("a split sets:", ", ".join(SPLIT_OWNS), "; in blueprint:", ", ".join(SPLIT_OWNS_BLUEPRINT))
    print("the maintainer's:", ", ".join(MAINTAINER), "; in blueprint:", ", ".join(MAINTAINER_BLUEPRINT))
    print("a stage-2 delivery sets:", ", ".join(STAGE2_OWNS), "; on the item also", ", ".join(STAGE2_ITEM_ALSO),
          "(only adding new definition nodes of the delivery)")
    print("a stage-2 statement correction of the item may change:", ", ".join(STAGE2_ITEM_CORRECTION),
          "; statement_change keys:", ", ".join(STATEMENT_CHANGE_KEYS), "; optional:", ", ".join(STATEMENT_CHANGE_OPTIONAL))
