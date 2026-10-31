/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositorRealization
public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonNormalization

/-! # The single-support site coordinate square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
`sk-prop-sp-composition-comparisons.proof.md`, (3), first sentence; Stacks Tags 09A6,
09AF and 00YV (blueprint: lem-sp-single-support-site-coordinate-square).

All coordinates are the published section-normalized constructions. The etale
bounded-below output is placed in the ambient category using its specified compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- For a single compactification, the site comparison commutes with the specified
finite support coordinates and the inverse realization unit, naturally on all
bounded-below etale objects.
Source: blueprint composition comparisons proof (3), first sentence; Stacks Tags
09A6, 09AF and 00YV (blueprint: lem-sp-single-support-site-coordinate-square).

Proof:
1. Expand the section-normalized direct image and the open realization cancellation.
   The identity on sections identifies `reductionCompactSupportFixedIso` with
   `sfIntrinsicCompactSupportComparison` after `finiteSupportCoordinates`.
2. Expand `fixedSupportCoordinates` using `compInverseIso` and `isoInverseComp`.
   Its component inserts the inverse realization counit at the source, applies the
   intrinsic support comparison, and cancels the realization unit at the target.
3. By `lem-coef-compact-support-comparison-normalization`, the fixed proper/open
   comparison, with the etale output inclusion inserted, is exactly the inverse of
   `compactSupportSiteComparison`. Expanding `finiteAdjointSiteSupportIso` realizes
   this same comparison after the support realization of step 1.
4. Apply the realization triangle identity at the etale-origin object. Naturality
   of the intrinsic support comparison and of the inverse unit rewrites the fixed
   support coordinates followed by the image of the inverse source unit as the
   inverse target unit followed by the inverse realization of step 1.
5. Apply naturality of the inverse target unit to the proper/open site comparison
   in step 3 and cancel that comparison with its inverse. Both sides become the
   expression in step 4. Every map is a natural-transformation component, so the
   equality is natural in the bounded-below input. No other input condition is used.
-/
theorem singleSupportSiteCoordinateSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (z : SpTowerCalculus.FiniteCoordinates l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))))) :
    (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse.map
        ((finiteAdjointSiteSupportIso (SpTowerShriek.R l E n) c).hom.app L) ≫
      (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).unitIso.inv.app
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) Y).mapDerivedCategory.obj
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus
              (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) c).obj L).obj) ≫
      (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) Y).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) c).hom.app L) ≫
      (compactSupportSiteComparison
        (ULift.{u + 1, u} (SpTowerShriek.R l E n)) c).inv.app L =
      (SpTowerCalculus.fixedSupportCoordinatesFinite l E z c n).hom.app
        ((reductionSite (SpTowerShriek.R l E n) X).obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) c).map
        ((sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).unitIso.inv.app
          ((comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (SpTowerShriek.R l E n))) X).mapDerivedCategory.obj
              L.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale
