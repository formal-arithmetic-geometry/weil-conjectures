## What changed

Proved `WeilConjectures.integral_twist_rationalization` in
`Sheaf.SecSmoothPurity.WeilTwistRationalization`, preserving its complete signature,
`localizedIntegralFunctor`, visibility, and existing docstrings. The tensor formulas use
`LinearMap.baseChange_tmul`. Exactness uses `ScalarLocalization.extension_exact` with
all three normalization properties extracted from `sfRationalTriangulationDatum`.
The two inverse isomorphisms use `extensionNatIso`, `extension_comp`, and
`extension_id_and_linear`, including explicit transport of the composite endpoints.
The twist specialization reuses the established inverse isomorphisms.
Scoped `linter.unusedVariables false` to the theorem because its unchanged signature
has named instance binders that Lean reports as used only implicitly.
Updated the existing node's proof and proof dependencies to describe these Lean steps.

Searches: LeanFinder for linear functor descent through scalar localization found generic
Mathlib localization linearity results, rather than the required raw tensor-category API.
Loogle found `LinearMap.baseChange_tmul`; the Mathlib grep confirmed its declaration.
Repository searches found the existing semilinear extension API, which supplies the rest.
The unit record has no realized nodes to bypass; the existing route is retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.integral_twist_rationalization`
(node `lem-weil-twist-rationalization`).
Added 0 holes. No `sorry` remains in the delivered Lean module. No split-offs.
This is a proof from the existing stated dependencies, some of which remain unproved;
it is not a claim that the complete transitive axiom closure is already sorry-free.

## No longer needed

Removed the unused proof import `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`.
Removed `def-coefficient-twists-detailed` from the node's proof dependencies: the
specialization follows from the inverse-isomorphism clauses without using its twist
identification assumptions. It remains a statement dependency, and the existing public
`Sheaf.Paper.IntrinsicCoefficientTwists` import remains necessary for the signature.
No other node or module is withdrawn. The semilinear-localization tool approval remains.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. Typeclass search does not unfold the
canonical localization abbreviation to find its shift-comparison instance, so the proof
installs exactly the existing `sfRationalLocalizationCommShift` instance locally.
The DAG's final step overstates the required proof work: its Lean conclusion repeats
already established inverse-isomorphism assertions. The proof now records this reuse.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
