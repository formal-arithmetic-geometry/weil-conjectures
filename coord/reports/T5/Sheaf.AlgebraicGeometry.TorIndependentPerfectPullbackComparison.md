## What changed

Repair of return C-f37bb (delivery head f37bbc6904): reconciled the retained
packet with the current shared branch. At inspection, the normal Sheaf path is
absent and its current implementation is preserved at the quarantine path in
`coord/rework.tsv`. It still has the mixed imports described below; the current
source counterpart still supplies the complete comparison proof. The repair
therefore restores the compatibility module against the current branch rather
than replaying a patch against the obsolete delivery base d92f73d8e. No archive
is deleted. The delivery tool recreates the commit on current `sheaf-dag`.
The restored module was recompiled on the server in this repair (exit 0,
1.4 seconds). A fresh complete-signature example and axiom query also compiled
in 2.4 seconds: the theorem uses exactly `propext`, `Classical.choice`, and
`Quot.sound`. The temporary example was removed. The fresh downstream scan again
reported zero modules, and the import-direction check passed.

Restored `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` from
quarantine as a compatibility re-export of
`WeilConjectures.AlgebraicGeometry.TorIndependentPerfectPullbackComparison`.
The source module already proves the same public theorem by the recorded K-flat
stalk argument. The mixed original imports load independent definitions with the
same name and fail before elaboration; the re-export uses one implementation.
No adopted source-library file is changed.

Updated `lem-pc-tor-independent-perfect-pullback-comparison` only in its `lean`
record to name the actual source declaration. Its mathematical statement, proof,
dependencies, and unit route are unchanged. The interface change is recorded in
`coord/changes/tor-independent-perfect-pullback-source-reexport.md`.

Validation on the compile server:
- The original quarantined file reproduces the recorded duplicate-definition
  import failure in 1.5 seconds.
- The compatibility module compiles in 1.8 seconds.
- A temporary example with the complete original signature proves by applying
  the imported theorem, compiling in 2.5 seconds.
- `#print axioms AlgebraicGeometry.torIndependent_perfect_pullback_comparison`
  reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The example and axiom query were removed from the delivered module.

The required `tools/downstream.py --allow-missing --uses` check reports zero
downstream modules and zero declaration users. A separate source scan across
`lean/` and `quarantine/` also finds no importer of the old Sheaf module. The actual consumer, the source `TorIndependentPerfectTensorBaseChange`,
already imports the source counterpart and needs no adaptation. The source and
Sheaf coordinate predicates use the same scheme stalks, explicit tensor-to-stalk
map, K-flat representatives, and canonical localized comparison. The source
K-flat predicate is named `IsKFlatTensor`; the old Sheaf spelling is
`IsAcyclicTensorKFlat`. The full theorem signature retains all hypotheses,
universes and conclusions.

## Proved and sorry left

This is a zero-hole rework repair. The quarantined module had zero `sorry` and
the restored module has zero. Holes closed: none (0 of 0). Holes added: none (0).
Split off: none (0). No sorry remains in any delivered declaration.

`AlgebraicGeometry.torIndependent_perfect_pullback_comparison`, node
`lem-pc-tor-independent-perfect-pullback-comparison`, remains fully proved by
the adopted source module. Its entire axiom closure has no `sorryAx`.

## No longer needed

The duplicate local theorem body and its private helpers `stalk_additive` and
`kFlat_pullback_stalk_cohomology` are replaced by the existing source proof.
The compatibility module no longer directly imports:
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`;
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison`;
- `Mathlib.Topology.Sheaves.Abelian`;
- `WeilConjectures.Algebra.Homology.ModuleStalkExact`;
- `Sheaf.Algebra.Homology.KFlatStalkCriterion`;
- `WeilConjectures.Algebra.Homology.TorIndependentKFlatTensorComparison`;
- `WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat`;
- `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`.

Their required mathematical roles remain in the source proof's import closure.
The two independent Sheaf coordinate/K-flat implementations are not needed by
this wrapper. No dependency node is withdrawn or claimed globally unnecessary:
the source proof follows the same three steps, so the node proof dependencies
are deliberately retained. No library module is deleted; modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined, not present at its normal `lean/` path, and
contains no proof hole. `coord/rework.tsv` identifies its precise import failure:
the environment already contains
`ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst` from the Sheaf model
when importing the source model. The generic proof-worker brief does not mention
this item-specific rework detail.

The DAG still attached the theorem to the Sheaf implementation although the
adopted source tree has the same theorem and its consumer already uses it.
The Lean attachment is corrected to the source declaration. A previously kept
DIFFERENT classification warned against loading both coordinate trees; this
repair avoids that situation by re-exporting the complete source module alone.
Searches through `msearch.py` (LeanFinder, Loogle, grep) found no shorter Mathlib
comparison theorem; direct source search found the exact existing full proof.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
