## What changed

Proved both original holes in `Sheaf.Paper.PullbackCoefficientIterateCoherence`.
`trf_commuting_endomorphism_powers` is an induction using the commuting square.
`trf_pullback_coefficient_iterate_coherence` applies the existing normalized derived
pullback associativity theorem three times, cancels the binary comparisons, and proves
the coefficient assertion by induction and naturality. Private categorical helpers use
the two fixed derived categories of the square.
Passing the three pullback families directly avoids expensive eta conversion of
the derived construction.

Added the proof-only import `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence`.
All existing public signatures, definitions, and public imports are unchanged. Local
transparency attributes prevent unnecessary unfolding during the categorical calculations.
The DAG proof now records the existing associativity theorem and the two elementary
inductions instead of reconstructing ordinary-to-derived coherence here.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.Scheme.trf_commuting_endomorphism_powers`.
- `AlgebraicGeometry.Scheme.trf_pullback_coefficient_iterate_coherence`.

Zero holes added; zero holes remain in the delivered module. No decomposition or unproved
intermediate theorem is delivered.

Validation: `lcompile.py` compiled the complete item with no errors or warnings
in 10.8 seconds at the project options. The packet changes only this Lean module
and its proof-route node, together with the change record
`coord/changes/G3-pullback-iterate-private-proof-context.md`. The record documents
the local proof commands required by static preflight; no auxiliary definition repair
or consumer adaptation is needed.

## No longer needed

Removed unused proof-only imports:

- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.

The item no longer directly proves from `def-weil-proetale-inverse-image`,
`def-weil-pbc-composite-adjunction`, `lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-localization-universal-property`, or `lem-pc-kflat-resolution`.
Their work is encapsulated by the existing
`lem-trf-derived-pullback-coherence`; these nodes can still be needed by its dependencies
and other consumers. Removed the obsolete direct tool-use entry `lem-pc-kflat-resolution`.
The binary comparison node remains a statement dependency and an approved tool use.
No library module or existing DAG node is withdrawn, and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The six-step mathematical argument is correct. Its first four steps are already supplied
by `proEtaleConstantRingDerivedPullback_composition_coherence`, so reproducing them here
would duplicate existing work. The complete conjunction is proved without splitting
off another result.
The exponent-zero comparison and the exponent-one coefficient case are included, and the
argument never assumes that the coefficient morphism is invertible.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
