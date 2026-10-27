## What changed

Proved `AlgebraicGeometry.WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso`
using a native open-base-change comparison and the counit of the localized native open
adjunction. The restriction comparison is assembled through the proper clopen map into
`X′ ×_X U`. The existing native Weil-complex proper-base-change theorem supplies vanishing
on the reduced closed complement. A cone argument makes the counit invertible.

All auxiliary declarations are proved private helpers in the assigned module.
The complete implementation compiled in 17.6 seconds before diagnostic cleanup;
the delivery checks validate the cleaned module.
Updated `lem-sf-native-weil-open-proper-interchange` to record this route. No existing
statement or data definition changes, and no source-library file changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso`.
Added zero holes. There are zero `sorry`s in the delivered Lean files. This is a proof
from existing named statements; in particular the existing
`AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`
remains a dependency with its own existing hole and DAG node
`lem-weil-pbc-weil-complex-proper-base-change`.

## No longer needed

The item no longer directly imports the following old-route modules:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`

Explicit private imports of `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction`,
`WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`
are also omitted: the remaining source imports already supply their APIs.

The following dependencies of the old explicit coefficient-model and resolution route
are unnecessary for this item's proof; their declarations remain in the library:

- `def-weil-proper-morphism`
- `lem-weil-pbc-proper-immersion-closed`
- `lem-sfb-finite-type-composition-base-change`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sf-native-weil-constructible-abelian`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-pur-clopen-ringed-module-gluing`
- `lem-weil-pbc-kinjective-functorial-existence`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-sf-fixed-pair-derived-forget-comparison`
- `lem-sf-continuous-adic-proper-base-change-restriction`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-truncation-triangle`
- `lem-sp-grothendieck-enough-injectives`

The source comparisons replace the explicit clopen product-category construction,
functorial choice of resolutions, coefficient-model transport, and finite Postnikov
induction from the old plan. No module is withdrawn. Global reachability and other
consumers determine whether the maintainer can prune any of these modules.

## Where the brief, the DAG or earlier work was wrong

The original statement is unchanged. The old plan was longer than necessary: native
proper base change is already stated in the adopted source library and has an existing
DAG attachment. Its import graph and DAG have no path back to this item. Applying it
only to closed-complement vanishing avoids reconstructing the ordinary ring-module
coefficient bridge. Naturality is constructed independently via native open base change
and the adjunction counit; no naturality is inferred from objectwise proper-base-change
isomorphisms, and no derived morphism is lifted through forgetting.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
