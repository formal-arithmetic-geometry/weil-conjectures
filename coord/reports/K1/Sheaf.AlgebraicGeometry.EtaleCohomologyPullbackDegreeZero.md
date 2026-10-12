## What changed
Completed three proofs in `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`.
`degreeZeroCohomology_resolution_naturality` lifts the degree-zero term of the mapped
single complex to cycles and uses Mathlib homotopy invariance of homology maps.
`degreeZeroCohomology_resolution_pullback` packages the unit/global-sections comparison
as a natural transformation, identifies its component with the existing global-section
pullback, and uses naturality after cancelling the inclusion of cycles.
`cohomologyMap_zero_eq_globalSectionsUpperStarMap` reduces degree-zero Ext to Hom and
uses uniqueness of left adjoints for the existing constant-sheaf comparison. Two proved
private helpers express the elementary adjunction comparison and the naturality of
Hom(ULift Z,-) with underlying elements. All existing signatures and imports are unchanged.
Updated the existing node's proof text and proof origin to record these implementations.
Removed the previous attempt's unrelated private `True` marker.

## Proved and sorry left
Proved, without using any declaration containing sorry:
- `AlgebraicGeometry.Etale.degreeZeroCohomology_resolution_naturality`.
- `AlgebraicGeometry.Etale.degreeZeroCohomology_resolution_pullback`.
- `AlgebraicGeometry.Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap`.

The only sorry left in the delivered module is
`AlgebraicGeometry.Etale.exists_degreeZeroCohomology_cycles_iso`, with node
`lem-weil-pbc-cohomology-pullback-degree-zero`. Its statement and complete original
bounded-below resolution/transport proof docstring are unchanged. No new sorries were added.
Local compilation is clean; the delivery dry run checks the server compile and axiom probe.

## No longer needed
No imports removed. No whole nodes or modules can be pruned from this delivery:
the remaining augmentation-isomorphism theorem still needs the bounded-below resolution
and K-injective comparison route. The two resolution equality proofs themselves need
neither the pullback-functoriality module nor a resolution-independence theorem; they use
the supplied homotopy or factorization equations and Mathlib directly. The Ext degree-zero
formula likewise uses only the existing Ext/Hom and adjunction definitions and lemmas.
The unit's realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong
The previous failure was not a tool failure: all four original sorries were unchanged,
so the rejection for no progress was correct. The unrelated `True` marker did not prove
any part of the item and was removed. No mathematical discrepancy was established.
The K-injectivity and quasi-isomorphism hypotheses are unnecessary for the two equality
computations, but were retained exactly as stated. No statement was changed.

## Second reading by K1

1. Compared the delivered module with the repository version. Existing declaration signatures and public imports are byte-for-byte unchanged; only proofs, private helpers, and the existing node's proof metadata changed. Verdict: pass.
2. Compiled the module locally with `lcompile.py`; it is clean. The sole remaining `sorry` is the named `exists_degreeZeroCohomology_cycles_iso`, already documented and represented by its node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the three completed declarations and the remaining split theorem against the existing node and source route. The three implementations are strict reductions of the planned naturality, pullback, and Ext/Hom computations; no duplicate split-off statement was added. Verdict: pass.
4. Reviewed the proof routes and imports. The proofs use Mathlib homotopy/naturality and existing adjunction lemmas, while retaining the unit's realized route and required public imports. No additional pruning was justified. Verdict: pass.
5. Compared the node's proof, proof dependencies, and proof origin with the Lean proofs. The node records the three implementations and leaves the augmentation-isomorphism route open, consistently with the module. Verdict: pass.

Changed in this second reading: appended this review; no Lean statements, definitions, or proof terms required repair.
