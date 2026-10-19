## What changed

Proved `AlgebraicGeometry.Etale.sf_directImage_ctf_open_tor` in
`lean/Sheaf/Paper/DirectImageCtfOpenTor.lean`, preserving its signature and all public imports.
Two proved private helpers establish the canonical scalar projection formula by generation
from A[0], and transfer the numerical torsion cohomological bound to module higher direct
images. The main proof tests Tor amplitude on the Jacobson quotient and uses the existing
bounded-below etale/pro-etale comparison. No definition, statement, consumer, or visibility
changed. Updated the item's proof route and attached one already proved source theorem.

The source module-generation criterion is the natural-transformation interface to
`lem-pc-derived-module-free-generation`; it avoids reconstructing its abstract closure
predicate. The source comparison interfaces cover the coefficient universe and all integer
intervals directly. The unit-level direct-image/Tor route remains intact; its unit record has
no realized statement or steps to bypass.

Validation: the final main module compiled cleanly through lcompile.py (25.5 seconds).
The proof handles arbitrary constant modules, a>b, the zero object, and the zero coefficient
ring through the general source interfaces. The existing declaration docstring still records
the old ten-step plan; the updated DAG is the exact implemented route.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.sf_directImage_ctf_open_tor`
(node `det-cor-sf-direct-image-ctf-open-tor`). The delivered module has zero `sorry` tokens.
Added zero holes and split off zero statements. Both private helpers are fully proved.
The new DAG attachment names a theorem already proved in the source library; it adds no Lean
file. Imported named dependencies retain their existing proofs or holes as allowed by stage 3;
this report does not claim that the entire target import closure is axiom-closed.

## No longer needed

Removed proof imports (public imports are unchanged):

- `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The following original proof dependencies are no longer used by this proof. This is edge
pruning for this item; it does not assert that these modules have no other consumers.
The generation argument replaces localization, K-injective scalar-mate calculations and
geometric-stalk detection. The upper-amplitude theorem replaces the spectral-sequence
implementation. The Jacobson criterion replaces the geometric-stalk all-sheaf upgrade.

- `def-kun-derived-tensor` — `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-kun-etale-lfp` — `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`
- `def-weil-etale-morphism` — `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `def-sbc-locally-finite-presentation` — `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `def-weil-finite-type-morphism` — `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `lem-weil-pbc-ring-sheaves-grothendieck` — `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `lem-weil-pbc-dplus-injective-representative`
- `thm-sp-truncation-e2` — `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `lem-weil-pbc-etale-site-localization-open` — `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `def-pur-localized-ringed-site` — `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `lem-pur-kinjective-restrict-localized` — `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `prop-weil-pbc-inverse-image-modules-exact` — `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `lem-weil-pbc-right-adjoint-preserves-kinjective` — `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` — `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `lem-weil-pbc-kinjective-total-derived` — `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `def-kun-constant-projection-morphism` — `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`
- `lem-kun-0f12` — `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`
- `prop-weil-pbc-kinjective-resolutions-exist` — `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `lem-weil-pbc-sheafification-exact`
- `lem-kun-stalk-as-pullback` — `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `lem-kun-inverse-image-monoidal` — `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `lem-kun-stalks-of-cohomology` — `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `lem-weil-pbc-constant-sheaf-geometric-stalk` — `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `lemma-weil-pbc-geometric-stalk-conservative` — `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

Removed obsolete approved tool-use entries (remaining entries retain their original order):

- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-kun-etale-lfp`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-dplus-injective-representative`
- `thm-sp-truncation-e2`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-pur-kinjective-restrict-localized`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-kun-0f12`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-weil-pbc-sheafification-exact`
- `lem-kun-stalk-as-pullback`
- `lem-kun-inverse-image-monoidal`
- `lem-kun-stalks-of-cohomology`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lemma-weil-pbc-geometric-stalk-conservative`

## Where the brief, the DAG or earlier work was wrong

The old lower-level proof route was longer than necessary. No false target or changed
hypothesis was needed. The existing DVR residue-test node is insufficient for the arbitrary
finite ring A in this item: its Jacobson radical need not be principal. The source library
already proves the general ideal-based test, so the new node attaches that result exactly.
The generic ring-generation statement already exists and is used through its equivalent
source natural-transformation API; no duplicate generation statement is added.

## New nodes

`lem-sfb-finite-ring-jacobson-tor-test` attaches
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`
in `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitudeResidue`. It tests all-sheaf Tor
amplitude against the constant Jacobson quotient for every finite commutative ring, every
complex, and all interval endpoints. The source proof uses a K-flat representative, exactness
on radical-annihilated sheaves and the finite radical filtration. Searches found no exact
Mathlib or blueprint match; the source theorem itself needs no new proof or hole.
No change record is required because no public interface changes.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
