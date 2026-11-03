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

/-- The pulled-back exceptional target remains in the bounded etale-origin class.
Source: proof Steps 8--9 (blueprint: def-pur-coordinate-zero-base-change).
Proof: the exceptional inverse image of the finite Tate object is bounded below
of etale origin. Exact pullback commutes with the site comparison, so preserves
that property. This uses no exceptional-base-change isomorphism. -/
theorem pulledExceptional_origin (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (setting P n).Coefficient) B'
      ((inverseImage (setting P n).Coefficient g).obj
        ((rightDerivedUpperShriek (setting P n).Coefficient
          (zero B c)).obj (target P n (iteratedAffineLine B c) c))) := by
  let := tower_noetherian (setting P n) B aB c
  obtain ⟨L, ⟨d, hd⟩, ⟨e⟩⟩ :=
    plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
      (target_plus P n _ (towerBase aB c) c)
  refine ⟨(Etale.upperStar
    (ModuleCat.{u + 1} (setting P n).Coefficient) g).mapDerivedCategory.obj L,
    ⟨d, ?_⟩, ⟨?_⟩⟩
  · exact (Etale.upperStar
      (ModuleCat.{u + 1} (setting P n).Coefficient) g).isGE_mapDerivedCategory_obj L d
  · exact ((Etale.upperStar _ g).mapDerivedCategoryCompIso _).symm.app L ≪≫
      (Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (setting P n).Coefficient) g).symm).app L ≪≫
      ((comparisonUpperStar _ B).mapDerivedCategoryCompIso _).app L ≪≫
      (upperStar
        (ModuleCat.{u + 1} (setting P n).Coefficient) g).mapDerivedCategory.mapIso e ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (setting P n).Coefficient) g).app _).symm

/-- Exact pullback of the finite Tate object is bounded below.
Source: proof Steps 7--9 (blueprint: def-pur-coordinate-zero-base-change).
Proof: use the factorwise canonical Tate pullback isomorphism to identify this
object with target on the new tower, which is bounded below by target_plus. -/
theorem pulledTarget_plus (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    DerivedCategory.TStructure.t.plus
      ((inverseImage (setting P n).Coefficient (spaceMap g c)).obj
        (target P n (iteratedAffineLine B c) c)) := by
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).symm
    (target_plus P n _ (towerBase (g ≫ aB) c) c)

/-- The specified exceptional base-change mate, with no assumed invertibility.
It transposes inverse closed exchange followed by pullback of the exceptional counit.
Source: proof Step 8 (blueprint: def-pur-coordinate-zero-base-change). -/
@[irreducible]
def coordinateExceptionalExchange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (inverseImage (setting P n).Coefficient g).obj
      ((rightDerivedUpperShriek (setting P n).Coefficient
        (zero B c)).obj (target P n (iteratedAffineLine B c) c)) ⟶
    (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B' c)).obj
        ((inverseImage (setting P n).Coefficient (spaceMap g c)).obj
          (target P n (iteratedAffineLine B c) c)) :=
  letI := tower_noetherian (setting P n) B aB c
  letI := tower_noetherian (setting P n) B' (g ≫ aB) c
  rightDerivedUpperShriekHomEquiv (zero B' c)
    (pulledExceptional_origin P n g aB c) (pulledTarget_plus P n g aB c)
    ((closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
        (spaceMap g c) (zero_square g c) _
        (plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
          (target_plus P n _ (towerBase aB c) c))).inv ≫
      (inverseImage (setting P n).Coefficient (spaceMap g c)).map
        (rightDerivedUpperShriekCounit (zero B c) _
          (target_plus P n _ (towerBase aB c) c)))

end AlgebraicGeometry.ProEtale.AffineZeroPurity
