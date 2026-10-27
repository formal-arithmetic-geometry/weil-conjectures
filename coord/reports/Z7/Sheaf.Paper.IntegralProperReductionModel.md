## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.integralProperReductionModel` with a
proof combining positive-reduction constructibility, normalized finite coefficient
encoding, fixed-module bounded constructible etale origin, and ordinary direct-image
comparisons. The existing theorem signature and every public definition are unchanged.

Added the proved module `Sheaf.Paper.IntegralPositiveReductionConstructible`. Its theorem
`integralReduction_constantModelBoundedConstructible` extends the existing
`FiniteModelQuotient.finite_model_sheaf_quotient_constructible` from degree-zero sheaves
to all bounded constructible integral complexes by finite truncation induction. A proved
private criterion identifies quotient constant-model constructibility with the fixed
finite-module etale-origin property. The derived scalar-extension adjunction supplies
triangulatedness without completeness or finite Tor-amplitude assumptions.

Added `Sheaf.Paper.IntegralReductionUnderlyingDirectImage` for the independent ordinary
perfect-quotient projection and scalar-forgetting step. In the item, proved private
helpers retain the underlying abelian sheaf under the specified normalized encoding,
construct a bounded-below etale antecedent, and combine bounded-below module/abelian and
etale/pro-etale direct-image comparisons in the ambient unbounded derived categories.
Every new proof import is private to its module. No source-library file is changed.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.integralProperReductionModel`.
The item now contains zero `sorry` occurrences.

Also proved the new theorem
`AlgebraicGeometry.ProEtale.integralReduction_constantModelBoundedConstructible`
(node `lem-sfb-integral-positive-reduction-constructible`) from existing declared
finite-model and fixed-module constructible-origin results. This adds zero holes.

Added one named remaining hole:
`AlgebraicGeometry.ProEtale.integralReduction_underlying_directImage`
(node `lem-sfb-integral-reduction-underlying-direct-image`), in its own new module.
This is only reduction versus ordinary direct image on underlying abelian complexes.
It neither constructs an etale model nor asserts its constructibility; its hypotheses
and conclusion do not repackage the assigned theorem. Thus this delivery is a genuine
decomposition: one original hole closed and one smaller hole added, net zero new closure.
Existing dependency theorems may themselves still have holes, as intended at stage 3.

## No longer needed

The item's former direct proof dependencies below are replaced:

- `det-ctf-finite-comparison-localizing` / `Sheaf.Paper.FiniteComparisonLocalizing`:
  normalized finite coefficient encoding and fixed-module constructible origin give the
  required antecedent directly, with no algebraically closed base or Tor restriction.
- `lem-weil-pbc-finite-ring-constructible-derived-origin` /
  `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`: its fixed-module bounded-origin
  ingredient `lem-weil-pbc-fixed-module-bounded-constructible-origin` suffices directly.
- `det-pe-classical-derived-equivalence` /
  `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`: no separate classical-derived
  equivalence is needed after applying the fixed-module origin theorem.

- `sk-thm-pe-direct-image-comparison` /
  `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: the existing source-library
  bounded-below abelian direct-image comparison (`prop-weil-pbc-comparison-direct-image`)
  provides exactly the isomorphism used, so the broader discrete-coefficient theorem
  is unnecessary as a direct dependency.

No existing module is withdrawn. `det-pe-derived-nakayama-resolution` and
`lemma-weil-pbc-perfect-projection-formula` move from direct dependencies of the item to
proof dependencies of the smaller ordinary-image comparison; they remain needed.
`det-prop-integral-criterion-reductions` remains a dependency because its proved private
finite-quotient topology and encoding comparison helpers are reused. There is no
universe-zero coefficient shrinking or finite-type coefficient transport step.
No original public import was removed; the existing coefficient exactness and derived
functor infrastructure is retained. No planned source-library declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The old node proposed applying the first-reduction constructibility criterion directly.
Its theorem assumes derived completeness and a first-reduction hypothesis; neither is
part of the assigned bounded-constructibility assumption. The existing degree-zero
finite-model quotient calculation followed by bounded truncation gives the needed
positive reductions without those additional hypotheses.

The old plan's universe-zero shrinking is unnecessary: the fixed-module theorem already
accepts the finite quotient in the scheme's universe. Its finite-localizing comparison
also has geometric/Tor hypotheses absent from this item, whereas normalized finite
encoding applies here. The unit route is preserved: reduce coefficients, obtain the
classical finite model, and compare ordinary images. All target signatures are unchanged.

Edge cases checked in the statements and argument: exponent one (`n = 0`), torsion
integral scalar models, zero complexes, zero-rank matrices, empty schemes and strata,
and bounded complexes with negative degrees. The image comparison does not assert any
cohomological upper bound, completed image, or constructibility of the direct image.

## New nodes

`lem-sfb-integral-positive-reduction-constructible` records the proved bounded-complex
extension of the existing degree-zero finite-model quotient calculation. Its Lean module
is `Sheaf.Paper.IntegralPositiveReductionConstructible`. It introduces no hole.

`lem-sfb-integral-reduction-underlying-direct-image` records the remaining ordinary
perfect-quotient projection and scalar-forgetting comparison, with its complete proof
in words. Its Lean module is `Sheaf.Paper.IntegralReductionUnderlyingDirectImage`.
It introduces one hole. Both nodes belong to the item's chapter and unit, and the item
node's proof and dependencies now follow the actual Lean argument. No change record is
required: no existing statement, definition, or public import has been changed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
