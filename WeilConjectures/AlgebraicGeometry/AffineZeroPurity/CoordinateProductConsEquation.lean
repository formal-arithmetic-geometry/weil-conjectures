/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductsAgree.CoordinateProductComparison
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateCoefficientSupportNaturality
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSingleTensorLax

/-! # The successor product equation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product, support
normalization and even shifts
(blueprint: lem-pur-coordinate-product-cons-equation).
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
open AffineSpacePurity AffineLinePurity

private theorem single_tensor_natural
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C]
    {L L' M : C} (t : L ⟶ L') :
    cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map (t ⊗ₘ 𝟙 M) =
      ((DerivedCategory.singleFunctor C 0).map t ⊗ₘ 𝟙 _) ≫ cupSingleTensorMap L' M := by
  obtain ⟨m, hm⟩ := coordinate_single_tensor_lax (C := C)
  let := m
  simpa only [tensorHom_id, hm] using
    (Functor.LaxMonoidal.μ_natural_left (DerivedCategory.singleFunctor C 0) t M).symm

private theorem derived_coefficient_square
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C]
    {L L' M N N' : C} (μ : L ⊗ M ⟶ N) (μ' : L' ⊗ M ⟶ N')
    (t : L ⟶ L') (s : N ⟶ N') (h : μ ≫ s = (t ⊗ₘ 𝟙 M) ≫ μ') :
    cupDerivedCoefficientMap μ ≫ (DerivedCategory.singleFunctor C 0).map s =
      ((DerivedCategory.singleFunctor C 0).map t ⊗ₘ 𝟙 _) ≫
        cupDerivedCoefficientMap μ' := by
  unfold cupDerivedCoefficientMap
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  rw [single_tensor_natural]
  simp only [Category.assoc]

private theorem derived_support_square (P : PurityFiniteSetting.{u})
    {Z Z' W X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
    (g : Z' ⟶ Z) (hg : g ≫ i = i')
    (q : pullback i' j ⟶ pullback i j)
    (hq : q ≫ cupIntersection i j = cupIntersection i' j) :
    cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
        (cupCoefficientMap P i j) ≫
      (cupSingle P X).map (P.functorialCupSupportMap true
        (cupIntersection i j) (cupIntersection i' j) q hq) =
    ((cupSingle P X).map (P.functorialCupSupportMap true i i' g hg) ⊗ₘ 𝟙 _) ≫
      cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
        (cupCoefficientMap P i' j) := by
  let t : (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i').obj (P.constant Z') :=
    P.functorialCupSupportMap true i i' g hg
  let s : (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
      (P.constant (pullback i j)) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i' j)).obj
        (P.constant (pullback i' j)) :=
    P.functorialCupSupportMap true (cupIntersection i j) (cupIntersection i' j) q hq
  have h := coordinate_coefficient_support_naturality P i i' j g hg q hq
  change cupCoefficientMap P i j ≫ s = (t ⊗ₘ 𝟙 _) ≫ cupCoefficientMap P i' j at h
  exact derived_coefficient_square (cupCoefficientMap P i j)
    (cupCoefficientMap P i' j) t s h

private theorem drop_comp_id {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y) (hh : f ≫ g ≫ 𝟙 Y = h) :
    f ≫ g = h := by
  simpa only [Category.comp_id] using hh

private theorem postcompose_factor {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y) (k : Y ⟶ Z) (hh : f ≫ g = h) :
    f ≫ (g ≫ k) = h ≫ k := by
  rw [← Category.assoc, hh]

private theorem inverse_tensor_square {C : Type*} [Category C] [MonoidalCategory C]
    {L L' M N N' F G H I : C}
    (θ : L ⊗ M ⟶ N) (θ' : L' ⊗ M ⟶ N') [IsIso θ] [IsIso θ']
    (t : L ⟶ L') (s : N ⟶ N') (hs : θ ≫ s = (t ⊗ₘ 𝟙 M) ≫ θ')
    (α' : L' ⟶ F) (α : L ⟶ F) (β : M ⟶ G) (hα : t ≫ α' = α)
    (r : F ⊗ G ⟶ H) (v : H ⟶ I) :
    s ≫ ((inv θ' ≫ (α' ⊗ₘ β) ≫ r) ≫ v) ≫ 𝟙 I =
      (inv θ ≫ (α ⊗ₘ β) ≫ r) ≫ v := by
  have hi : s ≫ inv θ' = inv θ ≫ (t ⊗ₘ 𝟙 M) := by
    apply (cancel_epi θ).mp
    rw [← Category.assoc, hs]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [Category.comp_id, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [hα, Category.id_comp]

private theorem cancel_source_target_eqs {C : Type*} [Category C]
    {W X Y : C} (p : W = X) (q : X = W) (r : Y = Y) (f : W ⟶ Y) :
    eqToHom p ≫ (eqToHom q ≫ f ≫ eqToHom r) = f := by
  subst X
  simp

private theorem cupZero_support_transport (P : PurityFiniteSetting.{u})
    {Z Z' W X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (i' : Z' ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
    (g : Z' ⟶ Z) (hg : g ≫ i = i')
    (q : pullback i' j ⟶ pullback i j)
    (hq : q ≫ cupIntersection i j = cupIntersection i' j)
    (F F' G : CupPlus P X) (hF : F.obj = F'.obj)
    (α' : (cupSingle P X).obj (P.functorialCupSource true i') ⟶ F.obj)
    (α : (cupSingle P X).obj (P.functorialCupSource true i) ⟶ F'.obj)
    (β : (cupSingle P X).obj (P.functorialCupSource true j) ⟶ G.obj)
    (hα : (cupSingle P X).map (P.functorialCupSupportMap true i i' g hg) ≫
      α' ≫ eqToHom hF = α) :
    (cupSingle P X).map (P.functorialCupSupportMap true
        (cupIntersection i j) (cupIntersection i' j) q hq) ≫
      cupZero P aX i' j F G α' β ≫
        eqToHom (congrArg (fun T ↦ cupTensorObject P X T G.obj) hF) =
      cupZero P aX i j F' G α β := by
  rcases F with ⟨F, hplus⟩
  rcases F' with ⟨F', hplus'⟩
  dsimp only at hF
  subst F'
  simp only [eqToHom_refl] at hα ⊢
  let θ := cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
    (hDM := cupMonoidal P X) (cupCoefficientMap P i j)
  let θ' := cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
    (hDM := cupMonoidal P X) (cupCoefficientMap P i' j)
  let t := (cupSingle P X).map (P.functorialCupSupportMap true i i' g hg)
  let s := (cupSingle P X).map (P.functorialCupSupportMap true
    (cupIntersection i j) (cupIntersection i' j) q hq)
  let hθ : IsIso θ := cupDerivedCoefficientMap_isIso P i j
  let hθ' : IsIso θ' := cupDerivedCoefficientMap_isIso P i' j
  have hs : θ ≫ s = (t ⊗ₘ 𝟙 _) ≫ θ' :=
    derived_support_square P i i' j g hg q hq
  have hα₀ : t ≫ α' = α := drop_comp_id t α' α hα
  have hαu : t ≫ (α' ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app F) =
      α ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app F :=
    postcompose_factor t α' α _ hα₀
  dsimp only [cupZero, supportedCup]
  exact @inverse_tensor_square (CupDerivedCategory P X) _ (cupMonoidal P X)
    _ _ _ _ _ _ _ _ _ θ θ' hθ hθ' t s hs _ _ _ hαu _ _

private theorem normalized_product_cons (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i : Fin c) (is : List (Fin c)) :
    coordinateProductOnSupport P n B aB c (i :: is) =
      cupZero (setting P n) (towerBase aB c) (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (towerBase aB c) is.length⟩
        ⟨shiftedLine (setting P n) (iteratedAffineLine B c), boundary_plus P n _⟩
        (coordinateProductOnSupport P n B aB c is) (boundary P n B aB c i) := by
  unfold coordinateProductOnSupport product
  dsimp only [coordinateProductFold, coordinateProductTransport, coordinateProductStart]
  exact cancel_source_target_eqs (classSource_eq P n B c (i :: is)).symm
    (classSource_cons P n B c i is) (target_succ P n (iteratedAffineLine B c) is.length) _

end AlgebraicGeometry.ProEtale.AffineZeroPurity
