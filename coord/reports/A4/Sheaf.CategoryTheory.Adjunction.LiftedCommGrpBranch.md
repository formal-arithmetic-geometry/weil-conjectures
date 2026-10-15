## What changed

Kept `Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch` empty and expanded
its withdrawal notice to name the canonical Mathlib replacements and the caller
that proves their operation and adjunct formulas directly.
The repair requested by upstream review #1424 was already landed by C1 as
`20261015T154155-L-159406` before this worker started. This delivery preserves
that repair; it does not recreate the existential wrapper or claim its proof.
No caller, mathematical statement, definition, target, or DAG record needs changing.
The existing change record is `coord/changes/liftedCommGrpBranch.md`.

Verified the landed caller `CategoryTheory.Adjunction.liftsGroupRingObjects`
in a scratch copy through `lcompile.py`. It directly constructs `L.mapCommGrp`,
`R.mapCommGrp`, and `adj.mapCommGrp`, with the operation, unit, counit and
hom-equivalence formulas proved inline. Compilation succeeded without warnings;
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The empty item module also compiled successfully. Its sole delivered change is
the more precise withdrawal notice; it remains a module without imports or declarations.
Loogle, LeanFinder, and local Mathlib searches confirm the existing constructions.

## Proved and sorry left

Holes closed in this delivery: none (0 of 0).
Holes added or split off: none (0).
Sorries left in the item module: none; it has no declarations.
The checked caller `CategoryTheory.Adjunction.liftsGroupRingObjects` has no `sorry`.
This is confirmation of a completed duplicate repair, not new proof progress.

## No longer needed

The duplicate declaration `CategoryTheory.Adjunction.liftedCommGrpBranch` and
module `Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch` remain withdrawn.
There are no source imports of the withdrawn module and no code references to the
retired declaration in either library root. The only remaining Lean-source
mention is a historical docstring in `SitePullbackAbelianUnderlying`; its proof
already uses `Adjunction.mapCommGrp` directly.

The original wrapper's public import `Mathlib.CategoryTheory.Monoidal.CommGrp_`
and the caller's proof import of the wrapper were removed by the landed C1 repair.
No imports are newly removed here. The retired node
`lem-weil-pbc-lifted-comm-group-branch` already has no Lean attachment and is not
used by any other node. The caller already cites
`lem-weil-pbc-adjunction-lifts-abelian-group-objects` instead. The Mathlib
constructions remain necessary. No further modules or nodes are newly pruned.

## Where the brief, the DAG or earlier work was wrong

The dispatched repair is stale: the repository already contains the reviewed C1
repair, its caller adaptation, its updated DAG records, and its landed change
record. The module contains neither the duplicate declaration nor any `sorry`.
There is consequently no open proof obligation to split off or prove here.
The report records this explicitly rather than attributing C1's work to A4.

The unit `sk-def-exchange` realizes neither this retired auxiliary node nor the
caller as its statement or a proof step. Its fixed route is unchanged.
The withdrawn node itself is retained in the DAG, as required.

## Second reading by A4

1. **Signatures and accidental changes — pass.** I compared the delivered module
with `lean/Sheaf/CategoryTheory/Adjunction/LiftedCommGrpBranch.lean` in the
repository. The repository module has no declarations, and the sandbox module
also has no declarations; the difference is documentation only. No target,
definition, theorem signature, import, or caller is changed. The existing
`coord/changes/liftedCommGrpBranch.md` records the earlier C1 interface change
and its forced caller adaptation.

2. **Compilation and axioms — pass.** `lcompile.py` compiles the delivered
module successfully. Since the module declares nothing, it introduces no
axioms, `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The already-landed caller was independently checked in the prior repair and
has no `sorry`; its proof uses only the permitted axioms.

3. **Statements and split nodes — pass.** The withdrawn module adds no
statement and no split-off theorem. The retained DAG node
`lem-weil-pbc-lifted-comm-group-branch` has no Lean attachment and is not
reintroduced. The canonical Mathlib constructions and the direct caller are
already recorded by the existing change and DAG records; no duplicate
declaration is present in the library.

4. **Pruning and imports — pass.** The module has no imports. The retired
wrapper and its old proof import are absent from the caller; the caller keeps
the direct Mathlib constructions needed by its proof. There are no additional
unused imports or proof dependencies to remove, and the unit route
`sk-def-exchange` remains unchanged.

5. **DAG and report consistency — pass.** The node's `proof`, `proof_deps`,
`proof_origin`, reviewed landing, and empty Lean attachment agree with the
withdrawn module and the direct Mathlib proof in
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`. No new node or change
record is needed. The only change made in this second reading is this report
section and the more precise withdrawal comment already present in the sandbox
module.
