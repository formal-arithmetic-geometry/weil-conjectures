## What changed

Proved `AlgebraicGeometry.ProEtale.comparison_direct_image_resolution_mate` with its
signature and every definition unchanged. Added proved private calculation helpers in
the item module. The chain transpose factors as the ordinary comparison followed by
the direct image of `t`. The generic `baseChange_resolutions` calculation applies the
existing right-derived base-change factorization and naturality, cancelling precisely
the augmentations used by the statement's resolution isomorphisms. The existing fixed
mate counit theorem then gives the derived transpose. Evaluation of restriction and
of the adjunction inverse identity gives both section formulas.

Updated the item's DAG proof to this shorter route. No other module changes, public
interface changes, new declarations visible to consumers, or new modules. The required
change record for the added section-local variables is
`coord/changes/W6-comparison-resolution-private-section.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.comparison_direct_image_resolution_mate`
(node `lem-pur-comparison-direct-image-resolution-mate`).

Single-file validation: `lcompile.py` passed cleanly in 25.6 seconds before restoring
the original unit-route import; delivery preflight validates the final file.

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none. This is a proof,
not a decomposition. All new helpers are private and fully proved.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`

The bounded-below termwise-injective calculation already provided by the source
library avoids these planned proof dependencies:
`prop-weil-pbc-inverse-image-modules-exact`,
`prop-weil-pbc-proetale-constant-ring-map`, `lem-sf-comparison-pullback-exact`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-total-derived`,
and `lem-pc-pre-derived-adjoint-functors-general`.
They remain valid library declarations and may still be needed elsewhere.
`lem-weil-pbc-conjugate-iso-unit-equation` is replaced by the Mathlib iterated-mate
and unit identities already used in the fixed-mate library proof. The canonical
pullback and mate nodes remain needed. No library module is withdrawn.

The unit-route import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and all four
original public imports are retained. Some removed proof modules remain
transitively imported through existing public interfaces; this report claims no
whole-library withdrawal or net closure pruning without the ledger's measurement.

## Where the brief, the DAG or earlier work was wrong

The planned general pre-derived adjunction/K-injective argument is unnecessary here.
The fixed comparison is already constructed as right-derived base change, whose
normalization theorem computes it directly on the supplied injective resolutions.
This also avoids any need to prove preservation of injectives by comparison inverse
image. The original statement and all its normalization clauses are preserved.

Searches: LeanFinder for derived adjunction counits on injective resolutions; Loogle
for adjunction counits; Mathlib grep for right-derived base change and Hom-equivalence
naturality; direct source searches found `rightDerivedFunctorPlusBaseChange_fac`,
`unit_mateEquiv_symm`, and the fixed mate counit normalization. Small cases require
no special exclusions: zero coefficients, zero complexes, identity morphisms, and
empty schemes use the same categorical equations and section evaluation.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
