## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.properOpenComparisonNormalization`
in `Sheaf.Paper.ProperOpenTowerComparison`. The proof covers invertibility of the
explicit restriction map, its cartesian normalization, and its open-adjunction
normalization. It uses the existing strict-tower operations and their mate API.

For the pullback square, iterating mates identifies exchange with the conjugate
of the invertible open comparison. Naturality, the open-unit equation for beta,
and the normalized direct-image compositor prove that the open transpose of
gamma is inverse to the explicit restriction. The cartesian case uses
`alpha_cartesian` and the proper-adjunction triangle. The open adjunction's
hom-equivalence then identifies the adjunct. Private proved categorical helpers
and component equations keep these calculations explicit.

All existing public signatures, public imports, and definition bodies are
unchanged. Updated the two existing DAG proof descriptions and proof dependencies
to record this argument. No other modules were adapted. Scoped elaboration settings
and the private categorical constructions are documented in
`coord/changes/P1-proper-open-normalization-proof-settings.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.StrictTower.properOpenComparisonNormalization`
(node `lem-sp-proper-open-comparison-normalization`).

Zero holes remain in the item; zero holes were added elsewhere; zero results
were split off. The imported `alpha_cartesian` theorem remains an existing
stated dependency. This delivery proves the item from that declaration; it
does not claim to prove all imported dependencies or remove all axioms from the
project's targets.

## No longer needed

Removed these 17 private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.LocalizeRingedSiteMorphism`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`

The strict-tower open-extension and finite-comparison APIs remain available
through the unchanged public calculus import. The extra direct imports are
redundant. The resolution/localization modules are not used by this proof:
invertibility is obtained by conjugation of betaInv instead of a new
K-injective diagram-site calculation.

Removed these obsolete proof dependencies from the parent node (their
statement dependencies and all library declarations remain intact):

- `lem-weil-proetale-weakly-etale-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `def-cbc-strict-tower-open-extension`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-cbc-proper-open-interchange-coherence`

Removed these unused entries from the parent's approved tool-use list:

- `lem-weil-proetale-weakly-etale-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-diagram-site-realization`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`

No module is withdrawn, and no claim is made that these modules are unused
elsewhere in the target closure. The unit's proper/open route remains intact.

## Where the brief, the DAG or earlier work was wrong

The normalization node proposed an additional K-injective diagram-site
calculation. The existing open comparison and Mathlib's iterated-mate
conjugation identity already prove the required invertibility. The normalized
compositor is itself defined by adjunction conjugation, so its compatibility
follows formally. No statement or definition repair was needed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
