## What changed

Retained and completed the previous attempt's proofs in
`lean/Sheaf/Paper/FiniteCoefficientPoint.lean`. Seven existing theorem holes are
closed. Module universe lift and coefficient restriction are exact by Mathlib;
finite and integral sections use `point_proEtale_sections_exact` and exact
restriction of scalars. Fraction-field extension is exact by localization flatness,
transported along the ULift ring equivalences. Cancellation of coefficient lifts
uses the restriction-of-scalars composition and identity isomorphisms, and its
uniqueness is proved on every lifted module element. The coefficient square is
proved by cancelling the Shrink algebra equivalences.

Added proof-only imports of
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`,
`Mathlib.Algebra.Category.ModuleCat.Descent`, and
`Mathlib.RingTheory.Flat.Localization`. Existing definitions, public imports and
statement signatures are unchanged. Explicit universe arguments resolve the
localization theorem's otherwise unconstrained auxiliary module universe and the
extension/restriction adjunction's module universe. The coefficient-square proof
retains the original algebraic-closure instance and section context.

Validation: the complete item compiles through `lcompile.py`, with no errors or
warnings. The retained LeanFinder and Loogle searches found the restriction-of-
scalars API; the Mathlib change-of-rings, descent and localization source was read
for the proof declarations used.

## Proved and sorry left

Closed 7 of the original 16 holes, with no holes added and no split-offs:

- `WeilConjectures.pointFibreModuleLift_exact`
- `WeilConjectures.pointFibreFinite_exact`
- `WeilConjectures.pointFibreIntegral_exact`
- `WeilConjectures.pointFibreFraction_exact`
- `WeilConjectures.pointFibreCoefficientDown_exact`
- `WeilConjectures.pointFibreLiftDown_existsUnique`
- `WeilConjectures.pointStageCoefficientSquare`

The following 9 original named theorem holes remain unchanged; all are attached
to `def-weil-finite-coefficient-point` and retain their complete source/proof
docstrings:

- `WeilConjectures.pointFibreModuleLift_mem`
- `WeilConjectures.pointFibreSizeLift_equivalence`
- `WeilConjectures.pointFibre_sections_mem`
- `WeilConjectures.pointIntegralFibre_linear`
- `WeilConjectures.pointRationalFibre_existsUnique`
- `WeilConjectures.pointFibreRationalDown_existsUnique`
- `WeilConjectures.pointFibreTensorLift_existsUnique`
- `WeilConjectures.pointRationalFibreScalar_existsUnique`
- `WeilConjectures.pointQbarFibre_existsUnique`

## No longer needed

None. No existing import, node or module is removed. The seven completed proofs
follow their existing docstring arguments. The remaining obligations still use
the recorded finiteness, scalar extension, localization and common-stage APIs.
No new helper statement or alternative DAG route is introduced.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox lacked its report, and its fraction-field proof did not
compile because of unresolved universe metavariables. These are repaired. The
original DAG has no numbered proof steps for this definition node; the existing
Lean theorem docstrings specify the construction obligations. No mathematical
statement error or change to the unit route was found.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
