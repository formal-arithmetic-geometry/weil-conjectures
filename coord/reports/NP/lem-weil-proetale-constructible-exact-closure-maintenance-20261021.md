# Superseded stage-1 request reconciled

Maintenance at 2026-10-21T07:15:13Z. Dispatcher key: lem-weil-proetale-constructible-exact-closure@e0185ab3c.

The 05:54 UTC stage-1 packet was superseded by the already verified E1 proof
landing 20261021T061009-L-1683218 (8a6738c4ddcde9268f7070ca43108b7f8353b8a9) at 06:10 UTC.
The 06:29 UTC return explicitly resolved the re-split and rejected its two new
nodes as duplicates. However, the repair note remained released, the NP claim
and return stayed open, and the queue/route note still requested two new nodes.
dag_queue.stage1_repair_owed therefore reopened the completed item, while
preflight correctly rejected both an unchanged delivery and failure to add the
obsolete two nodes. Retrying could not reconcile these contradictory records.

The repair note is now resolved by the existing landing; only this superseded
return and NP claim are closed, and only this item's queue rows are removed.
The rejected packet is preserved at refs/superseded/NP/lem-weil-proetale-constructible-exact-closure/e0185ab3cae665aab1e731cdb91f252caf186a1d. The route note now records
completion. No node, Lean module, pipeline code or dispatch limit is changed.
Backups of every existing edited/deleted file are under /home/ubuntu/weil-maint-bak/NP-exact-closure-1792566458.

The live proof is a 1473-character, two-step assembly from existing nodes.
Keep it. Do not restore the withdrawn finite-stalk/common-finite-type helper
nodes or push the old stage-1 packet. Any future work needs a new concrete
defect record. The previous return is preserved below and in Git history.

## Previous return (closed by this maintenance)

## lem-weil-proetale-constructible-exact-closure (2026-10-21 06:29 UTC, branch head e0185ab3ca)

Superseded by a live stage-3 Lean landing (A7, B10, C5). This S1 re-split was committed 2026-10-21 05:54 UTC on base ecf196f. The live ledger (l.20342) records 'merged deliver/E1/Sheaf.Paper.ProEtaleConstructibleExactClosure (stage 3; reviewer PASS; landing 20261021T061009, proof)' at 06:10 UTC. The live Lean module has 0 sorry. The live node's proof is now 2 steps citing lem-weil-pbc-proetale-constant-module-constructibility and lem-weil-constructible-coefficient-serre. Both of those nodes were already in this delivery's base: coefficient-serre (split, Q5-reviewed 2026-10-19) states the same kernel/cokernel/extension closure for A:Type(u+1), and the other gives the intrinsic⇔fixed-module constructibility comparison over ULift A. So the item follows in 2 steps from existing nodes. The two new statement-only nodes repeat work that coefficient-serre's proof already carries (C5): lem-weil-proetale-finite-stalk-local-models (same-field lift through covers via 092Q, finite stalks ⇔ finite models) and lem-weil-proetale-common-finite-type-models (fibre-product refinement, AsSmall constant-ring equivalence E_T and its predicate comparison). The report's not-duplicates list never weighs reusing coefficient-serre. Landing this delivery would overwrite the Lean-matching live proof with a 3-step 093U(3) assembly citing two unsplit nodes, reopening a closed node (brief-stage1 l.103, B10). Maths read in full: step 1 is correct; the lifting clause is true (κ(v) separable algebraic over an algebraically closed Ω, so trivial); (i)⇔(ii) is true; the nm>0 refinement and the extension clause of 093U(3) are used correctly. Cases checked: Y=∅, the zero ring, and the non-split Z/4 extension. No false statement was found; the RETURN is for supersession and duplication only. No fixes written. Maintainer: the re-split note is resolved by E1's landing; do not re-dispatch this item.

