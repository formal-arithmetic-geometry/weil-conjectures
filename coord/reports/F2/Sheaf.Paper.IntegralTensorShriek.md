## What changed

Completed both original proofs in `Sheaf.Paper.IntegralTensorShriek`, preserving every
public declaration signature and the coefficient construction.

`integralTensorShriek_preserves` uses exact derived homology comparisons, bounded maps,
the existing open/closed constructible-image theorems, and the right-derived/map-derived
comparison for closed direct image. The locally closed case composes these assertions.

`integralTensorShriek_generated` proves membership first for locally finite free single
sheaves using actual single complexes on finite free coefficient-point modules. An
explicit three-stratum presentation makes each locally closed extension an allowed
stratum generator. A proved coefficient isomorphism transports the existing integral
locally finite free resolution theorem: equip E with its spectral norm, shrink its carrier
using finite dimensionality, identify the integer subrings isometrically, and map their
continuous-function sheaves. Short exact triangles then handle locally finitely presented
pieces. The existing finite open/closed extension tower handles constructible sheaves,
and bounded canonical-truncation devissage handles K. Contractible triangles provide the
shift closure required by that devissage. Zero ranks, zero sheaves, and empty strata are
included. All new helpers are private and proved; no arbitrary resolution object is
defined by choosing from an unproved existence theorem.

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool
approvals to match the complete proof. Updated the proof explanations in the theorem
docstrings. Added only proof imports. No definitions or statements used by consumers
change, and no consumer adaptations are needed.

The preflight scanner requires a change record for the local elaboration commands:
`coord/changes/F2-integral-tensor-shriek-local-elaboration.md`. It documents the
local attributes, universe and scope commands, the private stratification construction,
and every transitive consumer. No consumer file is adapted.

## Proved and sorry left

Original holes: 2. Closed: 2:

- `AlgebraicGeometry.ProEtale.integralTensorShriek_preserves`
- `AlgebraicGeometry.ProEtale.integralTensorShriek_generated`

Added holes: 0. Split-offs: 0. No `sorry` remains in the assigned module. The proofs use
existing declarations in the library; this reports closure of this module's own holes,
not that all transitive dependencies are axiom-free.

Validation: the complete module compiled successfully through `lcompile.py` against
current published dependencies (42.2 seconds after performance improvements). Removed
the development profiler option after this check. The resumed delivery dry run also
passed compilation and the axiom probe against current server dependencies. Its static
preflight required the local-command change record above; that record is now included,
and final preflight follows.
The private continuous-function sheaf comparison now works over abstract coefficient
rings, avoiding repeated expansion of induced norm and ring structures. A named local
zero-object proof similarly avoids expensive backwards elaboration for rank zero.

## No longer needed

Removed proof-only imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`
- `Mathlib.CategoryTheory.MorphismProperty.Limits`
- `Mathlib.CategoryTheory.Sites.Precoverage`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CoefficientHeartCommonStratification`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedSurjectiveClosedEquivalence`
- `Sheaf.Paper.DerivedNakayamaResolution`
- `Sheaf.Paper.IntegralHeartLocalModel`
- `Sheaf.Paper.IntegralModels`
- `Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`
- `WeilConjectures.ConstructibleSheaf.Pullback`

Removed direct proof dependency edges:

- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `det-sf-open-closed-extension-zero-limits`
- `sk-def-sfb-module-pushforward-pullback`
- `lem-weil-pbc-right-adjoint-preserves-limits`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-derived-limit-products-core`
- `def-weil-derived-limit`
- `det-pe-derived-nakayama-resolution`
- `sk-def-sfb-module-lower-shriek`
- `sk-def-pe-derived-completion`
- `sk-lem-integral-models`
- `sk-def-sfb-constructible`
- `sk-thm-pe-constructible-comparison`
- `lemma-constructible-pullback-stratification`
- `lem-weil-pbc-weakly-etale-composition-base-change`
- `lem-galois-fpqc-covering-base-change`
- `def-weil-pbc-proetale-covering`
- `det-lem-int-integral-heart-local-model`
- `new-lem-weil-pbc-condensed-surjective-closed-equivalence`
- `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement`
- `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`
- `def-weil-closed-immersion`
- `def-pc-fibre-product`
- `lem-weil-pbc-proper-fp-permanence`
- `det-lem-coefficient-heart-common-stratification`
- `def-sfb-module-lower-star-comp`

Removed obsolete top-level tool approvals (the surviving approvals keep their order):

- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `det-sf-open-closed-extension-zero-limits`
- `sk-def-sfb-module-pushforward-pullback`
- `lem-weil-pbc-right-adjoint-preserves-limits`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-derived-limit-products-core`
- `def-weil-derived-limit`
- `det-pe-derived-nakayama-resolution`
- `sk-def-sfb-module-lower-shriek`
- `sk-def-pe-derived-completion`
- `sk-lem-integral-models`
- `sk-def-sfb-constructible`
- `sk-thm-pe-constructible-comparison`
- `lemma-constructible-pullback-stratification`
- `lem-weil-pbc-weakly-etale-composition-base-change`
- `lem-galois-fpqc-covering-base-change`
- `def-weil-pbc-proetale-covering`
- `det-lem-int-integral-heart-local-model`
- `new-lem-weil-pbc-condensed-surjective-closed-equivalence`
- `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement`
- `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`
- `def-weil-closed-immersion`
- `def-pc-fibre-product`
- `lem-weil-pbc-proper-fp-permanence`
- `det-lem-coefficient-heart-common-stratification`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `def-sfb-module-lower-star-comp`

The completion, product, reduction-tower and finite-coefficient preservation calculations
are unnecessary for this Lean statement because the exact image APIs already establish
constructibility. For generation, resolving single-sheaf pieces and then using bounded
truncation avoids simultaneous whole-complex local models, common ordered refinements,
and descent through changed stratum scheme structures. Finite open/closed localization
along strata and the integral-heart finite-free resolution remain the argument. This
prunes direct dependencies of this item; it does not claim every listed module disappears
from the targets' entire transitive import closure. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old report described a partial proof and an unresolved coefficient presentation.
The coefficient transport is now proved explicitly, and generation is completed.
The original detail proof was longer than needed given the landed constructible image,
locally finite free resolution, extension-tower and bounded-devissage APIs. No
mathematical error in the source statement is asserted. The unit's integral-heart and
finite open/closed localization steps are retained; the chapter and unit are unchanged.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
