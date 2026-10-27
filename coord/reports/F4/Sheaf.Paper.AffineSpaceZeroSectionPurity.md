## What changed

Proved six supporting theorems in `Sheaf.Paper.AffineSpaceZeroSectionPurity` without
changing any existing declaration signature or construction. The endpoint equalities
are computations. Two left-endpoint equalities remain original holes because their
full kernel conversion exceeds the fixed file limit; this partial delivery retains
the other six completed arguments. The identity exceptional unit is invertible by naturality of
the actual exceptional Hom bijection and the specified compact-support identity.
The zero square is proved Cartesian by the universal property of the ordered affine
tower, including dimension zero and arbitrary nonflat base maps.

The proof uses two proved private helpers, `tower_hom_ext` and `zero_spaceMap`.
Local irreducibility attributes bound the compact-support identity comparison and
identity-unit construction for endpoint conversions; no exported attribute
or definition is changed. All existing public imports are retained. No private proof import is added.

## Proved and sorry left

Closed 6 of the original 12 holes, all in namespace
`AlgebraicGeometry.ProEtale.AffineZeroPurity`:

- `targetSourceRaw_right`
- `zero_proj`
- `identityUnit_isIso`
- `zero_zero`
- `normalizationRaw_right`
- `zero_square`

No holes added or split off. Six original public theorem holes remain
unchanged, each attached to `cor-pur-affine-space-zero-section-purity`:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.targetSourceRaw_left`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.normalizationRaw_left`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.unit_finiteTor`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_untwisted`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_baseChange`

## No longer needed

Removed the following unused private proof imports:

- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Paper.VectorIntegrationSiteComparison`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

These removals concern this partial proof only: no mathematical dependency of the
three unfinished main theorems is withdrawn, no DAG node is pruned, and no module
is proposed for deletion. In particular the five existing planned proof dependencies
remain needed for the unfinished assembly. The public import closure is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned modules `CoordinateTowerNormalizationInduction` and
`CoordinateSectionProductRecursion` already import this item, the latter through
`CoordinateZeroBaseChange` and `CoordinateSectionArrows`. Importing them here as
requested would form a module cycle. A later assembly needs to extract this
module's existing construction API into a lower module, re-export it here, and
retarget those dependency imports; this delivery does not attempt that interface
refactor or replace the planned lemmas with equivalent new holes.

The current blueprint proof explicitly distinguishes the positive Cartier-Chern
class (integral one) from the positive localization-boundary orientation (integral
minus one in rank one). This module's existing `supportedClass` is constructed
from Cartier maps. No signed orientation identification, target signature, or
normalization claim is changed in this delivery.

At the start of this resumed session the sandbox already contained an uncompiled
candidate closing eight holes; compiler errors in its identity-adjunction and
Cartesian-square arguments were repaired, and the finite-Tor proof was explored. Its canonical monoidal transport elaborated,
but increased kernel-checking time beyond the fixed file limit, so its original
hole remains unchanged in this partial delivery.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
