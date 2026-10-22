# NC Artin--Tate stale claim reconciliation (2026-10-22)

The item `lem-sfb-artin-tate-subalgebra-finite-type` was completed by NB and
reviewed by L in `4f1830c730a` (2026-10-22 01:26:16 UTC). It is a Mathlib leaf,
matched to `fg_of_fg_of_fg`, with a passing review by `NT-cc-NB-f94a528e0`.
NC claimed it at 01:26:43 UTC from a stale stage-1 queue row. The live queue
subsequently removed it, but the held claim survived and triggered repeated
stage-1 workers. They correctly retained the completed node; preflight
correctly refused their unchanged item. There is no mathematical repair.

Under `coord/.merge.lock`, backed up the NC claim and `coord/deliveries.log`,
then closed only this stale claim with `tools/claim.py done NC ...`. There is
no NC delivery branch, open return, or repair note for the item. The live
node and its review are unchanged. No Lean source or launcher tool changed.

Validation: the live queue has no row for the item; stage-1 completion is true;
NC no longer holds it; the node SHA-256 is unchanged. The maintainer will also
check that `take-many --with-stage NC <item> 1` refuses the completed item and
that normal dispatcher passes do not restart it.

Launcher follow-up (report only; dispatcher code is outside this repair's
editable scope): `Group.work` restarts held stage-1 claims using its remembered
stage after `Group.server` reports queue stage `-`. Reconcile completed held
claims that have left the live queue, while preserving explicit repair returns
and released repair notes. Preserve the human's rule that a listed, unclaimed
item is dispatched; do not add failure-count gates, caps, waits, or pauses.
