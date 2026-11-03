/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCoefficientTensor
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSingleCupUnit
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import all WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Localization.Monoidal.Basic
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits
/-! # The singleton last-section product and its boundary

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, the ordered exterior product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity
attribute [local implicit_reducible] Etale.cartierAbelianEtale Etale.cartierAbelianPro

attribute [local implicit_reducible] PurityFiniteSetting.Coefficient
  PurityFiniteSetting.coefficientCommRing PurityFiniteSetting.Ring
  PurityFiniteSetting.ringCommRing

attribute [local implicit_reducible] AlgebraicGeometry.iteratedAffineLine
attribute [local implicit_reducible] cupSingle supportIso AffineSpacePurity.action supportData
-- Expose the cached source and finite-list calculation only in these proof conversions.
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] classSource List.ofFn Fin.foldr Fin.foldr.loop

private local instance support_closed_here (B : Scheme.{u}) (c : ℕ)
    (is : List (Fin c)) : IsClosedImmersion (supportMap B c is) := support_closed B c is

-- Normalize the selected-site Hom presentation before using ordinary functor laws.
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  PurityFiniteSetting.functorialCupSource PurityFiniteSetting.functorialCupConstant

-- Match the generated operation wrappers in the two presentations of the same ring.
-- The adjustment is local to these proofs; the coefficient construction is unchanged.
set_option linter.auxLemma false in
attribute [local implicit_reducible]
  PurityFiniteSetting.coefficientCommRing._aux_1
  PurityFiniteSetting.coefficientCommRing._aux_4
  PurityFiniteSetting.coefficientCommRing._aux_8
  PurityFiniteSetting.coefficientCommRing._aux_13
  PurityFiniteSetting.coefficientCommRing._aux_16
  PurityFiniteSetting.coefficientCommRing._aux_20
  PurityFiniteSetting.coefficientCommRing._aux_28
  PurityFiniteSetting.coefficientCommRing._aux_30
  PurityFiniteSetting.coefficientCommRing._aux_32
  PurityFiniteSetting.coefficientCommRing._aux_34
  PurityFiniteSetting.coefficientCommRing._aux_41
  PurityFiniteSetting.ringCommRing._aux_1
  PurityFiniteSetting.ringCommRing._aux_4
  PurityFiniteSetting.ringCommRing._aux_8
  PurityFiniteSetting.ringCommRing._aux_13
  PurityFiniteSetting.ringCommRing._aux_16
  PurityFiniteSetting.ringCommRing._aux_20
  PurityFiniteSetting.ringCommRing._aux_28
  PurityFiniteSetting.ringCommRing._aux_30
  PurityFiniteSetting.ringCommRing._aux_32
  PurityFiniteSetting.ringCommRing._aux_34
  PurityFiniteSetting.ringCommRing._aux_41

private theorem prefix_cancel_iso {C : Type (u + 2)} [Category.{u + 1} C]
    {W M N T U : C} (p : W ⟶ N) (e : M ≅ N) (a : N ⟶ T) (b : T ⟶ U) :
    (p ≫ e.inv) ≫ (e.hom ≫ a) ≫ b = p ≫ a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem supportMap_comp_eq (P : PurityFiniteSetting.{u})
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
    (g : D ⟶ C) (h : E ⟶ D) (m : E ⟶ C)
    (hg : g ≫ i = j) (hh : h ≫ j = k) (hm : m ≫ i = k) :
    P.functorialCupSupportMap true i j g hg ≫
      P.functorialCupSupportMap true j k h hh =
        P.functorialCupSupportMap true i k m hm := by
  have h₁ : P.functorialCupRestriction true i ≫
      P.functorialCupSupportMap true i j g hg = P.functorialCupRestriction true j :=
    (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.1
  have h₂ : P.functorialCupRestriction true j ≫
      P.functorialCupSupportMap true j k h hh = P.functorialCupRestriction true k :=
    (P.functorialCupSupportMap_existsUnique true j k h hh).choose_spec.1
  apply (P.functorialCupSupportMap_existsUnique true i k m hm).choose_spec.2
  rw [← Category.assoc, h₁, h₂]

private theorem compactProduct_closedSingle (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := zero_exact P n B aB c
    compactProduct P n B aB c =
      (closedSingleIso (setting P n).Coefficient (zero B c)
        ((setting P n).constant B)).hom ≫ supportedClass P n B aB c := by
  let := zero_exact P n B aB c
  let := tower_noetherian (setting P n) B aB c
  unfold compactProduct thom coordinateThomAdjunct
  exact (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).symm_apply_apply _

private theorem oneTargetIso_eq (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    oneTargetIso P n X = tensorIso (setting P n).Coefficient X (coefficientUnitIso P n X)
      (Iso.refl (shiftedLine (setting P n) X)) ≪≫
        tensorUnitLeftIso (setting P n).Coefficient X (shiftedLine (setting P n) X) := by
  unfold oneTargetIso
  exact eq_of_heq (oneTargetIso_existsUnique P n X).exists.choose_spec

private theorem fixed_tensorIso_hom (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (e : M ≅ M') (f : N ≅ N') :
    (tensorIso A X e f).hom = e.hom ⊗ₘ f.hom := by rfl
private theorem fixed_tensorUnitLeft_hom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (tensorUnitLeftIso A X K).hom = (λ_ K).hom := by
  unfold tensorUnitLeftIso
  change 𝟙 _ ≫ (λ_ K).hom = _
  exact Category.id_comp _
private theorem constant_unit_normalization (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient))).hom =
        𝟙 (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) := by
  change Functor.LaxMonoidal.ε (presheafToSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) ≫
    (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)).map
      (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem coefficientUnitIso_without_sheafification_unit
    (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    coefficientUnitIso P n X =
      (cupSingle (setting P n) X).mapIso (cupConstantIso (setting P n) X) ≪≫
        DerivedCategory.singleFunctorObjUnitIso _ := by
  unfold coefficientUnitIso
  have he := constant_unit_normalization (setting P n) X
  have hi : (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (setting P n).Coefficient))).inv = 𝟙 _ := by
    apply (cancel_mono (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (setting P n).Coefficient))).hom).mp
    rw [Iso.inv_hom_id, he]
    erw [Category.id_comp]
    rfl
  apply Iso.ext
  change (cupSingle (setting P n) X).map (cupConstantIso (setting P n) X).hom ≫
      (cupSingle (setting P n) X).map
        (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (setting P n).Coefficient))).inv ≫
      (DerivedCategory.singleFunctorObjUnitIso _).hom =
    (cupSingle (setting P n) X).map (cupConstantIso (setting P n) X).hom ≫
      (DerivedCategory.singleFunctorObjUnitIso _).hom
  erw [hi, (cupSingle (setting P n) X).map_id, Category.id_comp]

private theorem successor_boundary_rank_one (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    boundary P n (iteratedAffineLine B r) (towerBase aB r) 1 0 =
      boundary P n B aB (r + 1) 0 := by
  unfold boundary ordinaryBoundary
  rfl

private theorem last_support_comp (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (r : ℕ) :
    (setting P n).functorialCupSupportMap true (inclusion B (r + 1) 0)
        (lastSection B r) (successorLastCoordinateIso B r).hom
        (successorLastCoordinateIso_hom_inclusion B r) ≫
      (setting P n).functorialCupSupportMap true (lastSection B r)
        (supportMap (iteratedAffineLine B r) 1 (List.finRange 1))
        (supportIso (iteratedAffineLine B r) 1).hom
        (supportIso_existsUnique (iteratedAffineLine B r) 1).exists.choose_spec =
      (setting P n).functorialCupSupportMap true (inclusion B (r + 1) 0)
        (cupIntersection (𝟙 (iteratedAffineLine B (r + 1))) (inclusion B (r + 1) 0))
        (pullback.snd (𝟙 (iteratedAffineLine B (r + 1))) (inclusion B (r + 1) 0))
        pullback.condition.symm := by
  exact supportMap_comp_eq (setting P n) _ _ _ _ _ _ _ _ _

private theorem oneTargetIso_hom_unit (P : PurityFiniteSetting.{u}) (n : ℕ)
    (X : Scheme.{u}) :
    (oneTargetIso P n X).hom =
      (coefficientUnitIso P n X).hom ▷ shiftedLine (setting P n) X ≫
        (λ_ (shiftedLine (setting P n) X)).hom := by
  erw [oneTargetIso_eq, Iso.trans_hom, fixed_tensorIso_hom, fixed_tensorUnitLeft_hom]
  erw [Iso.refl_hom, tensorHom_id]

set_option maxHeartbeats 2000000 in
-- Checking the expanded coefficient transports and dependent fold needs extra heartbeats.
/-- The singleton supported product at the last section is the newest Cartier boundary.
Source: the singleton case of the ordered exterior product in the zero-section proof.
(blueprint: lem-pur-coordinate-successor-boundary-unit).

Proof: the closed Hom bijection recovers compactProduct as closedSingleIso followed by
supportedClass. Cancel that single comparison against successorLastCoefficient. The two
successive support maps equal the direct support map because both preserve the epic
restriction of constant coefficients. The singleton fold is a binary cup with the empty
product. Apply the proved canonical single-cup unit law. The rank-one Cartier divisor and
its boundary are the same as the newest coordinate divisor, by their definitions. -/
theorem coordinate_successor_boundary_unit (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    successorLastCoefficient P n B aB r ≫ lastProduct P n B aB r ≫
        (oneTargetIso P n (iteratedAffineLine B (r + 1))).hom =
      boundary P n B aB (r + 1) 0 := by
  let : LocallyOfFiniteType (towerBase aB r) := (tower_geometry aB r).1
  let : QuasiCompact (towerBase aB r) := (tower_geometry aB r).2.1
  let : IsSeparated (towerBase aB r) := (tower_geometry aB r).2.2
  let : PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (lastSection B r)) :=
    zero_exact P n (iteratedAffineLine B r) (towerBase aB r) 1
  have hl : lastProduct P n B aB r =
      compactProduct P n (iteratedAffineLine B r) (towerBase aB r) 1 := by
    unfold lastProduct
    exact eq_of_heq (lastProduct_existsUnique P n B aB r).exists.choose_spec
  erw [hl, compactProduct_closedSingle, oneTargetIso_hom_unit]
  unfold successorLastCoefficient
  erw [prefix_cancel_iso]
  unfold supportedClass coordinateSupportedCompose
  simp only [Category.assoc]
  unfold product coordinateProductFold coordinateProductTransport coordinateProductStart
  dsimp only [List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.rec, List.length_cons,
    List.length_nil]
  unfold classSource
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [cupZero_tensor]
  unfold zeroCupTensor
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, last_support_comp]
  erw [successor_boundary_rank_one, coefficientUnitIso_without_sheafification_unit]
  exact coordinate_single_cup_unit (setting P n) (inclusion B (r + 1) 0) _ _

end AlgebraicGeometry.ProEtale.AffineZeroPurity
