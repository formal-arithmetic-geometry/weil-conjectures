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
    print("a stage-2 delivery sets:", ", ".join(STAGE2_OWNS), "(nothing else)")
