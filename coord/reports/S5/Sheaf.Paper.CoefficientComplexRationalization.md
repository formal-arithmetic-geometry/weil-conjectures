## What changed

Filled the six theorem proofs in `Sheaf.Paper.CoefficientComplexRationalization`.
All existing signatures, public imports, definitions and instance bodies are unchanged.
Added proved private helpers for arbitrary-universe flat scalar extension, scalar-associator
formulas, generator extensionality, and descent of unit and tower equations.
The module comparison is constructed from the two existing `extendScalarsComp` isomorphisms.
The ordinary equations descend using the canonical derived-comparison coherence laws.
Updated the existing node's proof notes to describe the Lean implementation.
Change record: `coord/changes/S5-coefficient-complex-proof-environment.md` documents
the local instance command and proof-elaboration option flagged by preflight.

## Proved and sorry left

Closed all six original holes, with no added holes:

- `WeilConjectures.coefficientComplexTensors_exact`
- `WeilConjectures.coefficientComplexBeta_existsUnique`
- `WeilConjectures.coefficientComplexIntegerIdentity`
- `WeilConjectures.coefficientComplexIntegerComp`
- `WeilConjectures.coefficientComplexComparison_spec`
- `WeilConjectures.coefficientComplexRationalization`

These declarations belong to `lem-weil-coefficient-complex-rationalization`.
No `sorry` remains in the item or any new helper. Nothing is split off.
Validation is the single-file compilation and axiom probe performed by the delivery tool.

## No longer needed

Removed redundant proof imports `Mathlib.RingTheory.Valuation.ValuationRing`,
`Mathlib.RingTheory.Flat.Basic`, `Mathlib.Algebra.Category.ModuleCat.AB`,
`Mathlib.CategoryTheory.Localization.Predicate`, and
`Mathlib.LinearAlgebra.TensorProduct.Basic`. Required tensor and localization APIs are
already supplied by the retained imports. The new proof imports name the actual flatness,
short-complex exactness and derived-coherence APIs used.
No DAG dependency, project module or unit-route step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition needed correction. Mathlib's existing theorem
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` fixes the module universe to the
ring universe; the item permits arbitrary larger modules. The private exactness helper
therefore applies `Module.Flat.lTensor_exact` to short complexes and `Functor.exact_tfae`
at the required universe. Additivity follows from the scalar-extension adjunction.
The tensor adjunctions reduce uniqueness, unit and tower identities to normalized pure
generators, implementing the planned pure-tensor arguments without any fraction choices.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
