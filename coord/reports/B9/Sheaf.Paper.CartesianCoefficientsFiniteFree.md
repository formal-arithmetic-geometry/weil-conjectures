## What changed

Filled `AlgebraicGeometry.ProEtale.cartesianCoefficients_finiteFree` without changing its
statement, the existing definitions, or public imports. All added helpers are private and
proved. The integer inclusion is finite by the adopted source's
`PadicAlgCl.finite_integersMap`. Normality and the fraction-field instances identify the
upper integer ring as the integral closure; Mathlib supplies freeness and the degree/rank
identity. Compactness makes the inverse basis coordinates continuous. The coordinate and
basis-sum maps give an internal condensed-module isomorphism, with exactly the prescribed
summands. Additive monoidal transport gives the integral sheaf isomorphism.

For every chosen integral basis, `Basis.localizationLocalization` produces its field basis.
Its coordinates are continuous because they are linear over the p-adic base field. The
same condensed-module and pullback constructions give the rational sheaf isomorphism.
The integral-to-rational square is checked on continuous functions and transported by
functoriality. Both inverse-image equations are naturality of `upperStarFromPointComp`.
For integral flatness, the generic coordinate isomorphism of the existing finite-free
scalar-coordinate module identifies restriction of scalar extension with finite powers;
the forgetful functor creates and reflects limits. Rational flatness is already an adopted
source instance. No construction is chosen from an unproved mere-existence theorem.

Validation: unchanged definitions and theorem signature checked by text comparison;
import-pruning check passed. The delivery command performs the final full compile and
axiom/preflight checks before any push. The private proof-context
commands and consumer check are documented in
`coord/changes/B9-cartesian-finite-free-proof-context.md`.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.cartesianCoefficients_finiteFree`
(node `det-prop-sfb-cartesian-coefficients-finite-free`). Added zero holes; split off zero
statements. No `sorry` remains in the delivered module.

## No longer needed

Removed these unused private proof imports:

- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.RingTheory.Polynomial.RationalRoot`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Paper.PadicIntegersInvertEll`
- `Sheaf.Topology.ProfiniteCondensedRing`

Several of these remain available through necessary public imports. This report does not
claim their global withdrawal. No adopted-source declaration or module is removed. The updated node removes obsolete
tool-use approvals for `lem-weil-l-adic-extension-integers-dvr` and
`lem-sfb-grothendieck-sheafification`.

The direct source/Mathlib algebra argument does not import
`Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`
(`lem-sfb-local-field-integral-basis`). The explicit field localization and its
sectionwise compatibility avoid `Sheaf.CategoryTheory.LocalizedBasisCoefficients`
(`lem-sfb-localized-basis-coefficients`) and the sequential sheaf-localization result
`det-prop-sfb-qlbar-colimit-x-invert-ell`. The proof uses the generic coordinate construction
inside `FiniteFreeScalarCoordinates` and implements the forgetful-functor finite-limit
argument directly, so the packaged `ScalarCoordinateLimitCriterion` specialization need
not be imported. The separate general sheafification existence theorem is not used:
the source's existing sheaf categories already carry the needed instances. The canonical
point pullback and comparison from the adopted source replace their specification aliases.
These changes retain the unit's finite integral basis, topological/condensed basis,
monoidal pullback, compatible rational basis, and inverse-image argument.

## Where the brief, the DAG or earlier work was wrong

The original expanded DVR/integral-closure construction was unnecessary for the actual
integer rings: the adopted source already proves finiteness of their inclusion, and
Mathlib identifies integral closures, their ranks and localized bases. The integral
coordinate homeomorphism follows directly from compactness, as in the blueprint proof.
No statement or definition repair was needed. The left-adjoint colimit approval remains.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
