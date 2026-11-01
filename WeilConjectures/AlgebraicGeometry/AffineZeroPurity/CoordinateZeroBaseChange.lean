/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: def-pur-coordinate-zero-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-! The coordinate base-change map g_c, its Cartesian zero square and the chosen
pullback identification are the existing `spaceMap`, `zero_square` and `zeroSquare`
of Sheaf.Paper.AffineSpaceZeroSectionPurity; they are reused here, not restated
(blueprint: def-pur-coordinate-zero-base-change). -/

/-- The normalized closed constant-source pullback, derived by the exact pullback.
Source: proof Step 7 (blueprint: def-pur-coordinate-zero-base-change). -/
@[irreducible]
def coordinateSourcePullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    (inverseImage (setting P n).Coefficient (spaceMap g c)).obj
      ((cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
          ((setting P n).constant B))) ≅
    (cupSingle (setting P n) (iteratedAffineLine B' c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)).obj
        ((setting P n).constant B')) :=
  (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (setting P n).Coefficient) (spaceMap g c)).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} (setting P n).Coefficient)
      (spaceMap g c)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (cupSingle (setting P n) (iteratedAffineLine B' c)).mapIso
      ((setting P n).functorialCupExchange true (zero B c) (zero B' c)
        (spaceMap g c) g (zeroSquare g c))

/-- Proper closed exchange on each actual etale-origin object, using the derived
base-change mate and the proper identifications on its two sides.
Source: proof Step 8 (blueprint: def-pur-coordinate-zero-base-change). -/
@[irreducible]
def closedExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [HasCompactification i] [HasCompactification i'] (sq : IsPullback g i' i h)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z K) :
    (inverseImage A h).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj K) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i').obj ((inverseImage A g).obj K) :=
  letI := isIso_derivedBaseChangeMap_app_of_isProper A sq K hK
  (inverseImage A h).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) i).app K) ≪≫
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K) ≪≫
    ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) i').app ((inverseImage A g).obj K)).symm

end AlgebraicGeometry.ProEtale.AffineZeroPurity
