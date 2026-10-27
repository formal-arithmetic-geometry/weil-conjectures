## What changed

Partial proof delivery in Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent.
All existing statements and definitions are unchanged. Two proved private helpers normalize
adjunction transposition first on homotopy categories and then on complexes. The open
K-injective proof transports localized restriction through the site equivalence and scalar
extension along the coefficient isomorphism. The open representative equation specializes
the existing resolution theorem to identity maps. The identity direct-image isomorphism
is constructed from pullbackId and its uniqueness is checked on sections.

## Proved and sorry left

Closed 5 of the original 15 holes; added 0 holes and split off 0 statements:

- transpose_normalization
- open_inverseImage_isKInjective
- open_upper_isKInjective
- open_representative
- identityDirect_existsUnique

The following 10 original holes remain, all attached to
lem-sf-ringed-restriction-exchange-open-descent:

- actualCoefficients_coherent
- resolution_formula
- degreeZero_normalization
- open_comparison
- open_sectionwise
- openCube_exists
- open_restriction
- open_descent
- identityCoefficients_coherent
- identity_normalization

The open representative proof uses resolution_formula, which remains unproved.
The other proofs use existing library results; no new axioms or hollow definitions occur.

## No longer needed

Removed unused private proof imports:

- Sheaf.CategoryTheory.SiteInverseImageTensor
- WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- WeilConjectures.CategoryTheory.SiteMorphismComposition
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.CategoryTheory.KInjectiveTotalDerived
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- Mathlib.Algebra.Homology.DerivedCategory.KInjective
- Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
- Sheaf.Paper.RingedRestrictionLocalIso

No node or entire module is withdrawn: the ten unfinished declarations still retain their
recorded proof plans and dependencies. No adopted source-library declaration is changed.
The transpose proof uses the defining derived-unit equation instead of reproving the
chosen adjunction through K-injective Hom-set comparisons.

## Where the brief, the DAG or earlier work was wrong

The module initially had 15 holes. The transpose normalization has a shorter proof using
Adjunction.derivedη_fac_app and naturality of the right-derived unit. The current compiled
scalar-extension adjunction uses the reductionChange presentation, so its composite is
not definitionally the module's changeOfRings presentation; the proved scalar-extension
ring-isomorphism theorem supplies the required natural isomorphism directly.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
