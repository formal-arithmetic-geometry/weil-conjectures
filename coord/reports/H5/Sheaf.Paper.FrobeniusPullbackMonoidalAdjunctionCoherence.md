## What changed

Filled `comparison_lifts` and `ordinary_adjunction_coherent` in
`Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence`. The first uses
`IsoAlgebra.mapOfNatIsoHom` and proves both inverse equations on carriers.
The second uses `IsoAlgebra.mateIso` and `mapOfNatIsoAdjunction`, expands the
mate formula, and retains the supplied ordinary unit, counit and triangles.
All eleven original public signatures and all public imports are unchanged.

## Proved and sorry left

Closed two of the three original holes:
`WeilConjectures.PodFrobeniusCoherence.comparison_lifts` and
`WeilConjectures.PodFrobeniusCoherence.ordinary_adjunction_coherent`.
The one remaining original hole is
`WeilConjectures.PodFrobeniusCoherence.frobeniusPullbackMonoidalAdjunctionCoherence`,
attached to `lem-pod-frobenius-pullback-monoidal-adjunction-coherence`.
No holes were added and no theorem was split off. The two-proof candidate
compiled in 6.2 seconds. The final file is also being checked through lcompile.

## No longer needed

Removed proof-only imports `Sheaf.Paper.IntegralPullbackComposition`,
`Sheaf.Paper.PullbackIdentitiesScalarExtension`, and
`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`: neither completed
categorical proof needs them. Their nodes remain dependencies of the unfinished
coefficient argument in the original DAG. No node or module is withdrawn or
claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The categorical clauses are directly supplied by the existing `IsoAlgebra`
mate and adjunction APIs; no new categorical adjunction theory is needed.
The coefficient argument was developed through rational localization and
common-stage representatives, but its heterogeneous-equality conversions and
elaboration did not reach a clean full-file check. It is left at the original
named theorem, with its original statement, docstring and proof plan intact.
Experimental private helpers were excluded from this delivery. No mathematical
statement or definition was changed.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
