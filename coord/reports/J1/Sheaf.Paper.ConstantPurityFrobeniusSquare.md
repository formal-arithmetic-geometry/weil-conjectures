## What changed

Restored Sheaf.Paper.ConstantPurityFrobeniusSquare from its quarantine archive,
preserving every declaration and its DAG attachment. Repaired the reported
betaAtStage elaboration timeout by exposing the existing rationalBeta and
betaAtStage endpoint types and bounding local unfolding of the constructed
pullbacks. The rational arrow is explicitly transported along the definitional
equality of the two published stage-category structures before inclusion. The
coefficient-system projections use explicit geometric instances. The five original
conjugation factors are preserved.

Added proof imports of Sheaf.Paper.ConstantGeometricStalkUnit and
Sheaf.CategoryTheory.MateIsoAlongEquivalences. Reused the normalized strict unit
and its uniqueness; proved rational exchange endpoints by definition; proved
invertibility of the exceptional mate from Frobenius equivalences.

Change record: coord/changes/J1-constant-purity-frobenius-elaboration.md.

Validation: lcompile.py compiled the complete restored module successfully in
54.0 seconds, with the unchanged heartbeat limit and the 60-second file limit.
All temporary profiler and diagnostic options have been removed.

## Proved and sorry left

The archive has 6 holes. Closed 4, added 0, split off 0:

- WeilConjectures.ConstantPurityFrobenius.chainUnit_existsUnique: existing identical unit theorem.
- WeilConjectures.ConstantPurityFrobenius.chainUnit_isIso: uniqueness identifies the existing unit.
- WeilConjectures.ConstantPurityFrobenius.rationalExchange_endpoints: definitional equality.
- WeilConjectures.ConstantPurityFrobenius.exceptionalMate_isIso: mate along Frobenius equivalences.

Two holes remain, both attached to lem-pur-constant-purity-frobenius-square:

- WeilConjectures.ConstantPurityFrobenius.beta_existsUnique.
- WeilConjectures.ConstantPurityFrobenius.constant_purity_frobenius_square.

The closed auxiliary proofs use existing declared dependencies, some of which
still depend on sorry. This report counts textual holes closed, not an axiom-free
proof of the main purity square. Its existing six-step plan remains in the node.

## No longer needed

Removed unused proof imports:

- Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition.
- Sheaf.Paper.CompletedOperationTowerSubstitution.
- Sheaf.Paper.AdicSmoothDualizingComplexes (already publicly re-exported by
  RationalSmoothPurityCanonical).

No declaration or module is withdrawn. The first two nodes remain in the main
theorem's unfinished proof plan; removing their currently unused proof imports does
not withdraw those mathematical steps. The item is restored despite having zero
current Lean importers; its unfinished parents and unit route remain attached.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn. The rework entry points to the
actual elaboration defect in betaAtStage. The existing inferred endpoint types
force expensive reduction of constructed functors. Explicit endpoint annotations
together with explicit stage-category transport retain the same morphisms and
avoid that implicit conversion search.

The first two auxiliary holes duplicate the already stated normalized-unit
results in ConstantGeometricStalkUnit. Reuse and uniqueness suffice; no new
unit construction or new unproved statement is needed. The generic mate theorem
likewise supplies exceptionalMate_isIso directly.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
