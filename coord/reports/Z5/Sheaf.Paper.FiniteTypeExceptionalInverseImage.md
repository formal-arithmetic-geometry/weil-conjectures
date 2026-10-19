## What changed

Proved all five pending theorems in `Sheaf.Paper.FiniteTypeExceptionalInverseImage`.
`finiteCoefficient` applies `Padic.finite_coefficientExtensionRing` at the recorded
positive level and transports finiteness through ULift. `exceptionalBoundedBelow`
uses the existing etale instance for finite coefficients over a quasi-compact target;
a Noetherian target supplies that compactness. `noetherian` combines Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian` with
`QuasiCompact.compactSpace_of_compactSpace`. `unitPlus` supplies the lower bound zero:
the derived tensor unit is the image of the coefficient tensor unit as a single
cochain complex in degree zero, so the existing IsGE instances apply.
`finiteTypeHasBoundedBelowUpperShriek` obtains quasi-compactness of Y from its
finite-type structure map to Spec k, then applies the same existing etale instance.

All signatures, definitions, visibility, docstrings and imports are unchanged.
The single-file remote compile through lcompile.py passed without warnings (9.4 s).
Searches through msearch.py used LeanFinder, Loogle and grep; local source searches
confirmed the coefficient finiteness theorem, the quasi-compact etale instance,
and Mathlib's Noetherian and single-complex interfaces.

## Proved and sorry left

Closed 5 original holes:

- `WeilConjectures.PurityFiniteSetting.finiteCoefficient`
- `WeilConjectures.PurityFiniteSetting.exceptionalBoundedBelow`
- `WeilConjectures.PurityFiniteSetting.noetherian`
- `WeilConjectures.PurityFiniteSetting.unitPlus`
- `AlgebraicGeometry.ProEtale.finiteTypeHasBoundedBelowUpperShriek`

There are zero remaining holes in this module, zero holes added, and zero splits.
These proofs use existing library results; this does not claim that their transitive
dependencies are free of sorry.

## No longer needed

None. No imports removed and no nodes or modules withdrawn. The coefficient
finiteness, geometric compactness and Noetherianity, degree-zero tensor unit, and
etale bounded-below preservation arguments use their existing published interfaces.
The original public imports supply the module's existing exported types and instance
infrastructure and are retained.

## Where the brief, the DAG or earlier work was wrong

The current DAG has no primary lean.module attachment to this module.
The definition node `def-weil-exceptional-inverse-image` named in its docstrings now
records `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, with an empty
proof and proof_deps. The only node mentioning this module is
`prop-sf-closed-immersion-unit`, whose lean.note cites the finite-type bounded-below
helper; its own realization remains the upstream ClosedUpperShriek module.
Accordingly there is no attached proof plan to rewrite, and no unrelated node record
is changed. The unit `sk-def-sf-operations` has empty realized statement and steps.

The existing library has already generalized bounded-below preservation to a
quasi-compact target. Consequently the two bounded-below holes require only
specializing that theorem, rather than rebuilding its cohomological-dimension
argument here. Empty schemes, the zero coefficient ring, and arbitrary fields
remain allowed by the unchanged signatures and the existing results used.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
