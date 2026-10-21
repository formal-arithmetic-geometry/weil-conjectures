## What changed

Prove `AlgebraicGeometry.ProEtale.RationalLocalizedHom.rationalLocalizedHom` using the existing bounded-constructible localization, the proved continuous integral-model theorem, and the proved qcqs continuous integral push comparison. The Hom proof transports the statement's actual constant-section scalar actions through the continuous module encoding, proves scalar extension linear by its derived adjunction, and applies module localization/base change. It treats shifts by postcomposition with the canonical `commShiftIso`. The compact-support proof uses the chosen Nagata compactification and the actual canonical comparison, evaluated on the open extension of the integral input.

Validation: the complete proof compiled through `lcompile.py` in 48.7 seconds with exit code 0 and no warnings before the final instance-locality and unit-route-import corrections. The corrected file is rechecked by delivery.

All public definitions, original instance bodies, public imports, and the theorem signature are unchanged. The nine added private instances are local to this file. The proof elaboration settings are documented in `coord/changes/rational-localized-hom-proof-elaboration.md`. The added helpers are private and proved. The item node's proof, proof dependencies, and proof origin follow this route. No other library module is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.RationalLocalizedHom.rationalLocalizedHom` (the original one hole).

Added: zero holes. Split off: zero. No `sorry` remains in the delivered module. The existing localization and coefficient preservation statements are used as the named dependencies of this stage; this report does not claim their proofs are completed here.

## No longer needed

The original private imports `Sheaf.Paper.CartesianCoefficients`, `Sheaf.Paper.IntegralModelsOperations`, and `Sheaf.SixFunctors.IntegralModelsGenerators` are retained because preflight identifies them as unit-route modules. Their declarations and unit realizations are preserved.

The existing localization node `thm-sfb-extend-scalars-localization` retains the telescope and `lem-sfb-integral-localization-hom-colimit` in its proof dependencies (its fourth proof step). This delivery uses that API and leaves all unit records and their realizations unchanged.

Removed direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `Sheaf.Paper.BoundedConstructiblePushforwardRestriction`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.SixFunctors.IntegralExtHomContinuity`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The generic localization/fraction API replaces the direct integral Ext-continuity and generator argument. The proved continuous push-comparison API replaces a second telescope/continuity argument in this module. Direct open and proper preservation replace the compact-support restriction compatibility argument. The retained public imports still expose the original statement dependencies; no source declaration or module is withdrawn.

Removed direct proof dependencies in the item node:

- `def-sfb-derived-comap-lower-star-iso`
- `def-weil-abstract-derived-category`
- `def-weil-l-adic-coefficient-extension`
- `def-weil-pbc-proetale-site`
- `def-weil-triangulated-category`
- `det-lem-int-ext-continuity`
- `det-lem-integral-models-generators`
- `det-lem-integral-models-operations`
- `det-pe-bounded-continuity-direct-image`
- `det-prop-sfb-qlbar-colimit-x-invert-ell`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-sf-triangle-morphism-iso`
- `sk-def-sfb-constructible`
- `sk-def-sfb-dc-restricted-functors`
- `sk-def-sfb-derived-categories`
- `sk-prop-sfb-cartesian-coefficients`

These dependencies may remain needed by the unchanged public definitions or by the imported theorems. No claim of whole-library withdrawal is made.

## Where the brief, the DAG or earlier work was wrong

The planned telescope argument is unnecessary at this node: the source library already states the required bounded-constructible localization, and the continuous integral-model and push-comparison theorems are proved. The integral model used here is the actual bounded-constructible internal-module model, rather than the different constant-model predicate. The prescribed coefficient encoding is essential for matching the Hom scalar actions; an abstract additive equivalence alone would not establish the pure-tensor formula. The DAG was updated accordingly. No statement dispute or definition repair is introduced by this delivery.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
