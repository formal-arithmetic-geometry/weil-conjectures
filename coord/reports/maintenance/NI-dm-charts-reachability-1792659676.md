# NI finite normalization charts: reachability metadata repair

The return for immutable stage-2 head 5bb4823e5b7d requires unreachable flags
on def-sfb-formal-moduli-quotient and def-sfb-moduli-normalization-tests.
Stage-2 new-node validation excludes import_flags because that field belongs
to the maintainer. The worker therefore cannot satisfy both preflight and the
landing reachability check by editing a new-node packet.

Maintenance registers precisely those returned worker-authored definitions on
the authoritative base, with lean: null and import_flags: ["unreachable"].
Their statements, sources, searches, dependencies and provenance are unchanged.
The parent item is also outside the closure of every current/former target;
its missing unreachable flag is corrected. This commit changes no statement,
proof, dependency edge, Lean source, Lean binding or review acceptance.

The retained packet must now supply the helpers as existing dependency modules,
with lean.note explaining that no declaration is recorded yet and what each
module defines. Keep both helpers in the item's stmt_deps and preserve the
base's maintainer metadata. Historical New nodes/BLOCKED notes refer to the
old base. Normal deliver2.py preflight, file compiles and independent review
remain required; the repair does not itself accept the stage-2 statements.

Backups are adjacent .maint-NI-dm-charts-1792659676.bak files. New paths have
absence-marker backups. No dispatcher, provider, delivery, review or landing
tool was changed. The general protected-tool issue is documented in the
maintenance workspace REPORT.md for its owners.
