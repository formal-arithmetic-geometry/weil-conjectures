## What changed

Filled existing proofs in `Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars`.
All original public signatures, definitions, instances and public imports are preserved.
The proof uses the already normalized evaluation mate, its derived resolution factorization,
the exchange-mate cube, constant inverse-image naturality, and the arbitrary-ring
fixed-coefficient inverse-mate helpers. Scalar open normalization is transported through
exact localization; the projector equality is checked through the clopen pullback adjunction.
Private proof imports expose the existing helper lemmas without exporting new dependencies.
The node copy records the actual shorter arguments. There are no definition changes,
consumer adaptations, new modules, or new statements with holes.

## Proved and sorry left

Original holes: 14. Holes added: 0. Split off: 0.

Proved declarations, in namespace
`AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars`:

- `evaluation_resolution`
- `evaluation_transpose`
- `evaluation_units_counits`
- `gamma_formula`
- `evaluation_gamma`
- `coefficient_square`
- `scalarJInv_isIso`
- `scalar_open_normalized`
- `scalar_projector`
- `scalar_transpose`

The proof of `evaluation_gamma` uses the existing `evaluation_alpha` statement.
The scalar projector proof uses the proved ordinary part of scalar normalization.
No finiteness, flatness, boundedness, or preservation of K-injectives by scalar
restriction is assumed.

Remaining original holes, all attached to
`lem-cbc-tower-mate-evaluation-scalars`:

- `evaluation_open_transpose`
- `evaluation_alpha`
- `scalar_alpha`
- `scalar_gamma`

## No longer needed

Removed private direct imports:

- `Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization`: constant-section
  compatibility is obtained directly from inverse-image naturality.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: reuse the existing
  `evalR_isIso` and the proved derived-mate factorization instead of rebuilding resolutions.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`: the same existing
  evaluation mate supplies the precise normalization needed here.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the arbitrary-ring scalar
  open comparison is proved through the fixed-coefficient equivalences and their inverse mates.

The completed proofs also remove these direct proof dependencies from the node:
`lem-cbc-tower-adjunction-realization`, `prop-pur-kinjective-resolutions-exist`,
`lem-weil-tower-category-levelwise-abelian`,
`lem-weil-pbc-tower-derived-evaluation-normalization`, and
`lem-weil-proetale-weakly-etale-localization`. The obsolete top-level tool-use entries
for tower-derived evaluation normalization and levelwise abelian categories are removed;
the ring-sheaf-change approval is retained.

No module is withdrawn and no globally unreachable node is claimed. Dependencies needed
by the remaining original alpha arguments are retained. The ringed open scalar import
is retained with private helper visibility for the normalization equations.

## Where the brief, the DAG or earlier work was wrong

The stated mathematical assertions are unchanged. Several steps had already been
implemented as normalized helper lemmas in dependencies: rebuilding their resolutions
and section models is unnecessary. The finite-open scalar module's relevant private
helpers do not require finite rings; the invertibility argument applies to arbitrary
coefficient homomorphisms. The DAG now records this route. The remaining ordinary alpha
compatibility still needs its stated compositor and projector argument.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
