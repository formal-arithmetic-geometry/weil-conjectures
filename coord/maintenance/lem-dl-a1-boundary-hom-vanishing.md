# lem-dl-a1-boundary-hom-vanishing: completed A7 cleanup

Closed at 20261018T055408Z, against accepted NM landing `b30da4cc05ec9abc1d8954e8deb5e0ef0055ec03`.
Dispatcher key: `lem-dl-a1-boundary-hom-vanishing@f0d0c13fd`; stage 2, group N7.

## Cause and evidence

NM's reviewed stage-2 batch d5f907a14f1845b599a28368dcc3ca8c landed at
2026-10-18 04:00:56 UTC. N7 reacquired the item at 04:01:05 UTC while the
queue was stale. Its later redundant delivery f0d0c13fdeac was returned under
A7/A6/H11 at 04:20 UTC. The redundant delivery branch was subsequently removed,
but the N7 claim and the open return remained. The dispatcher selects held
returns even when the item has left the queue and the branch is absent, so each
worker was asked both to re-deliver and to obey A7's prohibition on re-delivery.
The unchanged accepted packet correctly fails the ordinary new-delivery gate.

At closure, the item has no queue row, no N7 delivery ref, no repair note, and
a reviewed_lean PASS for NM. Its entire node is semantically identical to the
accepted landing (only JSON key ordering differs); its module is byte-identical.
Module SHA-256: `e0b2527b304e74050422fcef15d8e2ff5f88a54901de7574cef8df9dd37fc7c4`.
No mathematical repair or new stage-2 delivery is required.

## Record correction

Removed only this obsolete section from coord/returns/N7.md; the exact section
is archived below. Closed only N7's stale claim, recording an explicit L
maintenance entry in coord/deliveries.log. This closure is not a delivery by N7.
The accepted node, module, NM attribution, and PASS review are unchanged.

Backups made before changing the existing records:

- `coord/returns/N7.md.maint-20261018T055408Z.bak`
- `coord/deliveries.log.maint-20261018T055408Z.bak`
- `coord/claims/lem-dl-a1-boundary-hom-vanishing.lock.maint-20261018T055408Z.bak`

## Next worker

This stage-2 item is already complete. Do not recreate the N7 delivery branch,
change lean.by from NM, alter accepted files to satisfy a dry run, or submit a
replacement delivery. A wanted mathematical correction goes to coord/HUMAN.md
under A7. The theorem's remaining sorry belongs to separate stage-3 work.

The launcher-owned dispatcher and landing tools were not changed. The local
maintenance REPORT.md describes the stale-queue and cleanup-disposition follow-up.

## Archived return (verbatim)

## lem-dl-a1-boundary-hom-vanishing (2026-10-18 04:20 UTC, branch head f0d0c13fde)

L: independent stage-2 immutable head f0d0c13fdeac: A7/A6/H11: this is a push after the merge. The item was merged at 04:00Z by NM (batch d5f907a1, commit b30da4cc05, reviewer PASS); N7's commit came at 04:06Z. The only changes are one uninformative docstring sentence, lean.by changed from NM to N7 (misattribution), and NM's report copied word for word with an empty 'Second reading by N7'. No repair is needed: do not re-deliver, delete the branch, and put any wanted correction into coord/HUMAN.md (A7). Independent check of the unchanged content: nt_compile --json exit 0, no errors; only sorry; no hollow defs; maths true (i^!(j_*F) in D^{>=2}; reverse direction is a negative Ext; pair Homs inject into the geometric ones); edge cases Z empty, E=0, F=0, j=id and the constant sheaf on G_m checked.
