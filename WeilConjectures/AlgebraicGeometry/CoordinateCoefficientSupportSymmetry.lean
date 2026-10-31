/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedCupFunctorialityModels

/-! # Symmetry of normalized coefficient multiplication

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior products
(blueprint: lem-pur-coordinate-coefficient-support-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem mul_comm_of_unit {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {L : C} (e : L ≅ 𝟙_ C) :
    (β_ L L).hom ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ C)).hom ≫ e.inv =
      (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ C)).hom ≫ e.inv := by
  have hU : (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
    apply (cancel_mono (λ_ (𝟙_ C)).hom).mp
    simpa only [Category.id_comp, unitors_equal] using braiding_leftUnitor (𝟙_ C)
  rw [← BraidedCategory.braiding_naturality_assoc, hU, Category.id_comp]

private theorem coefficient_mul_comm (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (β_ (P.constant X) (P.constant X)).hom ≫ cupCoefficientMultiplication P X =
      cupCoefficientMultiplication P X := by
  exact mul_comm_of_unit (cupConstantIso P X)

private theorem support_map_normalized (P : PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (hg : g ≫ i = j) :
    cupCoefficientRestriction P i ≫ P.functorialCupSupportMap true i j g hg =
      cupCoefficientRestriction P j :=
  (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.1

private theorem support_map_unique (P : PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (hg : g ≫ i = j)
    (f : P.functorialCupSource true i ⟶ P.functorialCupSource true j)
    (hf : cupCoefficientRestriction P i ≫ f = cupCoefficientRestriction P j) :
    f = P.functorialCupSupportMap true i j g hg :=
  (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.2 f hf

private theorem support_map_comp (P : PurityFiniteSetting.{u})
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
    (g : D ⟶ C) (hg : g ≫ i = j) (h : E ⟶ D) (hh : h ≫ j = k) :
    P.functorialCupSupportMap true i j g hg ≫
        P.functorialCupSupportMap true j k h hh =
      P.functorialCupSupportMap true i k (h ≫ g)
        (by rw [Category.assoc, hg, hh]) := by
  apply (P.functorialCupSupportMap_existsUnique true i k (h ≫ g)
    (by rw [Category.assoc, hg, hh])).choose_spec.2
  have hi := (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.1
  have hj := (P.functorialCupSupportMap_existsUnique true j k h hh).choose_spec.1
  change P.functorialCupRestriction true i ≫
    (P.functorialCupSupportMap true i j g hg ≫
      P.functorialCupSupportMap true j k h hh) = P.functorialCupRestriction true k
  change P.functorialCupRestriction true i ≫
    P.functorialCupSupportMap true i j g hg = P.functorialCupRestriction true j at hi
  change P.functorialCupRestriction true j ≫
    P.functorialCupSupportMap true j k h hh = P.functorialCupRestriction true k at hj
  rw [← Category.assoc, hi, hj]

private theorem support_map_id (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (g : C ⟶ C) (hg : g ≫ i = i) :
    P.functorialCupSupportMap true i i g hg = 𝟙 _ := by
  symm
  apply support_map_unique
  exact Category.comp_id _

/-- The normalized coefficient multiplication commutes with exchange of its supports.
Source: the ordered exterior-product argument in the affine-space purity proof.
(blueprint: lem-pur-coordinate-coefficient-support-symmetry).

Proof: compose with the reverse normalized support map. On the tensor of the
constant restriction maps, naturality moves the braiding to the constant
coefficients. Their multiplication is commutative, so this composite has the
normalization characterizing cupCoefficientMap. Uniqueness identifies it with
that map. The two normalized support maps compose to identity, again by their
restriction characterization; postcomposing cancels the reverse map. -/
theorem coordinate_coefficient_support_symmetry (P : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (g : pullback j i ⟶ pullback i j)
    (hg : g ≫ cupIntersection i j = cupIntersection j i)
    (h : pullback i j ⟶ pullback j i)
    (hh : h ≫ cupIntersection j i = cupIntersection i j) :
    cupCoefficientMap P i j ≫ P.functorialCupSupportMap true
        (cupIntersection i j) (cupIntersection j i) g hg =
      (β_ ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z))
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W))).hom ≫
        cupCoefficientMap P j i := by
  let s : (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection j i)).obj
      (P.constant (pullback j i)) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
      (P.constant (pullback i j)) :=
    P.functorialCupSupportMap true (cupIntersection j i) (cupIntersection i j) h hh
  let t : (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
      (P.constant (pullback i j)) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection j i)).obj
      (P.constant (pullback j i)) :=
    P.functorialCupSupportMap true (cupIntersection i j) (cupIntersection j i) g hg
  have hst : s ≫ t = 𝟙 _ := by
    dsimp only [s, t]
    exact (support_map_comp P (cupIntersection j i) (cupIntersection i j)
      (cupIntersection j i) h hh g hg).trans (support_map_id P _ _ _)
  have hmu : (β_ ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z))
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W))).hom ≫
      cupCoefficientMap P j i ≫ s = cupCoefficientMap P i j := by
    apply (cupCoefficientMap_existsUnique P i j).unique ?_
      (cupCoefficientMap_existsUnique P i j).exists.choose_spec
    have hn := (cupCoefficientMap_existsUnique P j i).exists.choose_spec
    change (cupCoefficientRestriction P j ⊗ₘ cupCoefficientRestriction P i) ≫
      cupCoefficientMap P j i = cupCoefficientMultiplication P X ≫
        cupCoefficientRestriction P (cupIntersection j i) at hn
    have hr := support_map_normalized P (cupIntersection j i) (cupIntersection i j) h hh
    change cupCoefficientRestriction P (cupIntersection j i) ≫ s =
      cupCoefficientRestriction P (cupIntersection i j) at hr
    calc
      (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫
          (β_ _ _).hom ≫ cupCoefficientMap P j i ≫ s =
          (β_ _ _).hom ≫
            (cupCoefficientRestriction P j ⊗ₘ cupCoefficientRestriction P i) ≫
            cupCoefficientMap P j i ≫ s := by
        rw [BraidedCategory.braiding_naturality_assoc]
      _ = (β_ _ _).hom ≫ cupCoefficientMultiplication P X ≫
          cupCoefficientRestriction P (cupIntersection j i) ≫ s := by
        rw [← Category.assoc _ (cupCoefficientMap P j i), hn, Category.assoc]
      _ = cupCoefficientMultiplication P X ≫
          cupCoefficientRestriction P (cupIntersection i j) := by
        rw [← Category.assoc _ (cupCoefficientMultiplication P X),
          coefficient_mul_comm, hr]
  calc
    cupCoefficientMap P i j ≫ t =
        ((β_ _ _).hom ≫ cupCoefficientMap P j i ≫ s) ≫ t := by rw [hmu]
    _ = (β_ _ _).hom ≫ cupCoefficientMap P j i := by
      simp only [Category.assoc, hst, Category.comp_id]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
