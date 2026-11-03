/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateAdjunctionComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import Mathlib.GroupTheory.Perm.Sign
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerDescent
import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateClosedSourceExchange
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductConsEquation
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductHeadInterchange
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductsAgree.CoordinateProductComparison
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateShiftedLineSymmetry
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSupportedProductPullback
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSupportedProductSuccessor
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSupportedProductZero
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint latest, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: lem-pur-coordinate-section-product-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option maxRecDepth 2048 in
section CoordinateBaseChangeProof

private theorem compactProduct_adjunct (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
      (target_plus P n _ (towerBase aB c) c) (compactProduct P n B aB c) =
        thom P n B aB c := by
  let := tower_noetherian (setting P n) B aB c
  unfold compactProduct
  exact (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).apply_symm_apply _

/-- Rank-zero normalization and the two recursive identities for the actual maps.
Source: proof Steps 1--6 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: coordinate nonzerodivisors remain Cartier after adjoining or killing the
other coordinates. Pull back the first r factors. The cup coefficient map and
the proper projection at the supported coefficient unit both multiply restricted
sections, so agree, with the tensor symmetry. Naturality of projection at C_r
then gives the supported recursion. Transpose it: substitute both exceptional
counits, use their naturality, and paste them to the composite-adjunction counit.
Conjugating the compact-support compositor gives precisely the displayed
exceptional recursion. At zero, the empty product and identity adjunction give
the two identity formulas. All reordered shifts are even, with sign +1. -/
theorem coordinate_section_product_recursion (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    compactProduct P n B aB 0 = coordinateIdentity P n B ∧
    thom P n B aB 0 =
      coordinateIdentityAdjunct P n B aB ∧
    (∀ r : ℕ, compactProduct P n B aB (r + 1) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r) ∧
    ∀ r : ℕ, thom P n B aB (r + 1) =
      thom P n B aB r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r := by
  obtain ⟨h₀, hC⟩ := coordinate_supported_product_recursion P n B aB
  refine ⟨h₀, ?_, hC, ?_⟩
  · rw [← compactProduct_adjunct P n B aB 0, h₀]
    unfold coordinateIdentityAdjunct
    rfl
  · intro r
    let := isNoetherian_of_locallyOfFiniteType aB
    let := tower_noetherian (setting P n) B aB r
    let := tower_noetherian (setting P n) B aB (r + 1)
    rw [← compactProduct_adjunct P n B aB (r + 1), hC r]
    rw [coordinateAdjunction_composition P n B aB r,
      compactProduct_adjunct P n B aB r]

private theorem transpose_composite
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (F : C ⥤ D) (G : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D') (R' : D' ⥤ C')
    {K R : C} {L : D} {K' : C'} {L' : D'}
    (s : K' ⟶ U.obj K) (θ : K ⟶ R) (m : U.obj R ⟶ R'.obj (V.obj L))
    (t : V.obj L ⟶ L') (ε : F.obj R ⟶ L)
    (ε₀ : G.obj (R'.obj (V.obj L)) ⟶ V.obj L)
    (ε₁ : G.obj (R'.obj L') ⟶ L')
    (eK : G.obj (U.obj K) ⟶ V.obj (F.obj K))
    (eR : G.obj (U.obj R) ⟶ V.obj (F.obj R))
    (a : F.obj K ⟶ L)
    (ha : F.map θ ≫ ε = a)
    (hm : G.map m ≫ ε₀ = eR ≫ V.map ε)
    (hn : G.map (U.map θ) ≫ eR = eK ≫ V.map (F.map θ))
    (ht : G.map (R'.map t) ≫ ε₁ = ε₀ ≫ t) :
    G.map (s ≫ U.map θ ≫ m ≫ R'.map t) ≫ ε₁ =
      G.map s ≫ eK ≫ V.map a ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, reassoc_of% hm, reassoc_of% hn, ← V.map_comp_assoc, ha]

private theorem pullback_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (V : C ⥤ D) {K S T : C} {K' S' T' : D}
    (e : K ⟶ S) (a : S ⟶ T) (p : K' ⟶ V.obj K) (q : S' ⟶ V.obj S)
    (t : V.obj T ⟶ T') (e' : K' ⟶ S') (a' : S' ⟶ T')
    (he : p ≫ V.map e = e' ≫ q) (ha : q ≫ V.map a ≫ t = a') :
    p ≫ V.map (e ≫ a) ≫ t = e' ≫ a' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc p, he, Category.assoc, ha]

private theorem closedExchange_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [HasCompactification i] [HasCompactification i'] (sq : IsPullback g i' i h)
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z K)
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z L) (f : K ⟶ L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i').map
        ((inverseImage A g).map f) ≫ (closedExchange A g i' i h sq L hL).inv =
      (closedExchange A g i' i h sq K hK).inv ≫
        (inverseImage A h).map ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).map f) := by
  let e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) i ⋙ inverseImage A h ⟶
      inverseImage A g ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} A) i' :=
    Functor.whiskerRight
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) i).hom (inverseImage A h) ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq ≫
      Functor.whiskerLeft (inverseImage A g)
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) i').inv
  have hn := e.naturality f
  have hnh :
      (inverseImage A h).map ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).map f) ≫
          (closedExchange A g i' i h sq L hL).hom =
        (closedExchange A g i' i h sq K hK).hom ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i').map
            ((inverseImage A g).map f) := by
    simpa only [e, closedExchange, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.comp_map,
      Category.assoc] using hn
  apply (cancel_epi (closedExchange A g i' i h sq K hK).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hnh]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem thom_transpose (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    let := zero_exact P n B aB c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).map (thom P n B aB c) ≫
        rightDerivedUpperShriekCounit (zero B c) _
          (target_plus P n _ (towerBase aB c) c) =
      (closedSingleIso (setting P n).Coefficient (zero B c)
        ((setting P n).constant B)).hom ≫ supportedClass P n B aB c := by
  let := tower_noetherian (setting P n) B aB c
  let := zero_exact P n B aB c
  unfold thom coordinateThomAdjunct
  change (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).symm
      ((rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
        (target_plus P n _ (towerBase aB c) c)) _) = _
  exact Equiv.symm_apply_apply _ _

private theorem coordinate_mate_transpose (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    let := tower_noetherian (setting P n) B' (g ≫ aB) c
    let := zero_exact P n B aB c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B' c)).map
      ((unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (setting P n).Coefficient (zero B' c)).map
          (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom) ≫
      rightDerivedUpperShriekCounit (zero B' c) _
        (target_plus P n _ (towerBase (g ≫ aB) c) c) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map (unitPullback P n g).inv ≫
        (closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
          (spaceMap g c) (zero_square g c) _ (unit_origin P n B)).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          ((closedSingleIso (setting P n).Coefficient (zero B c)
            ((setting P n).constant B)).hom ≫ supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom := by
  let := tower_noetherian (setting P n) B aB c
  let := tower_noetherian (setting P n) B' (g ≫ aB) c
  let := zero_exact P n B aB c
  let hM := pulledExceptional_origin P n g aB c
  let hT := pulledTarget_plus P n g aB c
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)
  let U := inverseImage (setting P n).Coefficient g
  let V := inverseImage (setting P n).Coefficient (spaceMap g c)
  let R' := rightDerivedUpperShriek (setting P n).Coefficient (zero B' c)
  let t := (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom
  let ε := rightDerivedUpperShriekCounit (zero B c) _
    (target_plus P n _ (towerBase aB c) c)
  let ε₀ := rightDerivedUpperShriekCounit (zero B' c) _ hT
  let ε₁ := rightDerivedUpperShriekCounit (zero B' c) _
    (target_plus P n _ (towerBase (g ≫ aB) c) c)
  let eK := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _ (unit_origin P n B)
  let eR := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _
      (plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
        (target_plus P n _ (towerBase aB c) c))
  have hm : G.map (coordinateExceptionalExchange P n g aB c) ≫ ε₀ =
      eR.inv ≫ V.map ε := by
    refine (rightDerivedUpperShriekHomEquiv_symm_apply (zero B' c) hM hT
      (coordinateExceptionalExchange P n g aB c)).symm.trans ?_
    unfold coordinateExceptionalExchange
    exact (rightDerivedUpperShriekHomEquiv (zero B' c) hM hT).symm_apply_apply _
  exact transpose_composite F G U V R' (unitPullback P n g).inv (thom P n B aB c)
    (coordinateExceptionalExchange P n g aB c) t ε ε₀ ε₁ eK.inv eR.inv
    ((closedSingleIso (setting P n).Coefficient (zero B c)
      ((setting P n).constant B)).hom ≫ supportedClass P n B aB c)
    (thom_transpose P n B aB c) hm
    (closedExchange_naturality (setting P n).Coefficient g (zero B' c) (zero B c)
      (spaceMap g c) (zero_square g c) (unit_origin P n B)
      (plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
        (target_plus P n _ (towerBase aB c) c)) (thom P n B aB c))
    (rightDerivedUpperShriekCounit_naturality (zero B' c) hT
      (target_plus P n _ (towerBase (g ≫ aB) c) c) t)

/-- Arbitrary base-change identities for the actual supported product and its
specified exceptional adjunct, with canonical source and Tate identifications.
Source: proof Steps 7--9 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: the first equality is coordinate_supported_product_pullback. For the
second, transpose both sides through the closed exceptional adjunction, whose
counit-composition map is bijective. The mate's defining counit equation,
naturality of inverse closed exchange and counit naturality turn the left
transpose into the pullback of closedSingleIso followed by the supported class.
coordinate_closed_source_exchange identifies the pulled-back source with
coordinateSourcePullback; the first equality then gives the primed supported
class, which is the transpose of the primed Thom map. Invertibility of the
exceptional mate is not used. -/
theorem coordinate_section_product_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      supportedClass P n B' (g ≫ aB) c ∧
    (unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B' c)).map
            (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      thom P n B' (g ≫ aB) c := by
  have hC := coordinate_supported_product_pullback P n g aB c
  refine ⟨hC, ?_⟩
  let := tower_noetherian (setting P n) B aB c
  let := tower_noetherian (setting P n) B' (g ≫ aB) c
  let := zero_exact P n B aB c
  let := zero_exact P n B' (g ≫ aB) c
  apply (bijective_rightDerivedLowerShriek_map_comp_counit (zero B' c)
    (unit_origin P n B') (target_plus P n _ (towerBase (g ≫ aB) c) c)).injective
  let V := inverseImage (setting P n).Coefficient (spaceMap g c)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)
  let s := (unitPullback P n g).inv
  let eK := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _ (unit_origin P n B)
  let e := (closedSingleIso (setting P n).Coefficient (zero B c)
    ((setting P n).constant B)).hom
  let e' := (closedSingleIso (setting P n).Coefficient (zero B' c)
    ((setting P n).constant B')).hom
  let t := (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom
  have he : (G.map s ≫ eK.inv) ≫ V.map e =
      e' ≫ (coordinateSourcePullback P n g c).inv :=
    (Category.assoc (G.map s) eK.inv (V.map e)).trans
      (coordinate_closed_source_exchange P n g aB c)
  have hcomp := pullback_comp V e (supportedClass P n B aB c) (G.map s ≫ eK.inv)
    (coordinateSourcePullback P n g c).inv t e' (supportedClass P n B' (g ≫ aB) c) he hC
  have hθ : G.map (thom P n B' (g ≫ aB) c) ≫
      rightDerivedUpperShriekCounit (zero B' c) _
        (target_plus P n _ (towerBase (g ≫ aB) c) c) =
      e' ≫ supportedClass P n B' (g ≫ aB) c :=
    thom_transpose P n B' (g ≫ aB) c
  exact (coordinate_mate_transpose P n g aB c).trans
    ((Category.assoc (G.map s) eK.inv
      (V.map (e ≫ supportedClass P n B aB c) ≫ t)).symm.trans (hcomp.trans hθ.symm))

end CoordinateBaseChangeProof

attribute [local irreducible] comparisonUpperStar lowerStar

set_option maxHeartbeats 1000000 in
-- Comparing simultaneous realization witnesses needs a larger elaboration budget.
end AlgebraicGeometry.ProEtale.AffineZeroPurity
