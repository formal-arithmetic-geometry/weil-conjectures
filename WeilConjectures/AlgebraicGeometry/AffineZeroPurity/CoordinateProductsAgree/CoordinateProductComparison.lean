/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows

/-! # Comparing products on their literal supports

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: def-pur-coordinate-product-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

/-- The product with its support source written literally.
Source: ordered coordinate product (blueprint: def-pur-coordinate-product-comparison). -/
def coordinateProductOnSupport (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (is : List (Fin c)) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      (((setting P n).functorialCupSource true (supportMap B c is))) ⟶
        target P n (iteratedAffineLine B c) is.length :=
  eqToHom (classSource_eq P n B c is).symm ≫ product P n B aB c is

/-- Equality of two supported products through an isomorphism over the affine tower.
Source: support normalization (blueprint: def-pur-coordinate-product-comparison). -/
def CoordinateProductsAgree (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (is js : List (Fin c)) : Prop :=
  ∃ (e : support B c is ≅ support B c js)
    (he : e.hom ≫ supportMap B c js = supportMap B c is) (hlen : is.length = js.length),
    (cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((setting P n).functorialCupSupportMap true (supportMap B c js)
          (supportMap B c is) e.hom he) ≫
      coordinateProductOnSupport P n B aB c is ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c)) hlen) =
      coordinateProductOnSupport P n B aB c js

private theorem supportMap_comp (P : PurityFiniteSetting.{u})
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
    P.functorialCupSupportMap true i j g hg = P.functorialCupRestriction true j at hi
  change P.functorialCupRestriction true j ≫
    P.functorialCupSupportMap true j k h hh = P.functorialCupRestriction true k at hj
  change P.functorialCupRestriction true i ≫
    (P.functorialCupSupportMap true i j g hg ≫
      P.functorialCupSupportMap true j k h hh) = P.functorialCupRestriction true k
  rw [← Category.assoc, hi, hj]

private theorem supportMap_id (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupSupportMap true i i (𝟙 _) (Category.id_comp _) = 𝟙 _ := by
  symm
  apply (P.functorialCupSupportMap_existsUnique true i i (𝟙 _)
    (Category.id_comp _)).choose_spec.2
  exact Category.comp_id _

/-- Every product agrees with itself.
Source: support identity (blueprint: def-pur-coordinate-product-comparison). -/
theorem CoordinateProductsAgree.refl (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (is : List (Fin c)) :
    CoordinateProductsAgree P n B aB c is is := by
  refine ⟨Iso.refl _, Category.id_comp _, rfl, ?_⟩
  simp only [Iso.refl_hom]
  rw [supportMap_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem compose_transport {C : Type*} [Category C]
    {X Y Z U V W : C} (a : X ⟶ Y) (b : X ⟶ Z) (t : Z ⟶ Y)
    (f : Y ⟶ U) (g : Z ⟶ V) (h : U = V) (k : V = W)
    (ht : a = b ≫ t) (hp : t ≫ f ≫ eqToHom h = g) :
    a ≫ f ≫ eqToHom (h.trans k) = b ≫ g ≫ eqToHom k := by
  rw [ht, ← eqToHom_trans h k]
  calc
    (b ≫ t) ≫ f ≫ eqToHom h ≫ eqToHom k =
        b ≫ (t ≫ f ≫ eqToHom h) ≫ eqToHom k := by simp only [Category.assoc]
    _ = b ≫ g ≫ eqToHom k := by rw [hp]

/-- Compose comparisons with the specified support and length transports.
Source: support composition (blueprint: def-pur-coordinate-product-comparison). -/
theorem CoordinateProductsAgree.trans (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    {is js ks : List (Fin c)} (h₁ : CoordinateProductsAgree P n B aB c is js)
    (h₂ : CoordinateProductsAgree P n B aB c js ks) :
    CoordinateProductsAgree P n B aB c is ks := by
  obtain ⟨e, he, hl, hp⟩ := h₁
  obtain ⟨f, hf, hm, hq⟩ := h₂
  refine ⟨e ≪≫ f, ?_, hl.trans hm, ?_⟩
  · change (e.hom ≫ f.hom) ≫ _ = _
    rw [Category.assoc, hf, he]
  · have ht := supportMap_comp (setting P n) (supportMap B c ks)
      (supportMap B c js) (supportMap B c is) f.hom hf e.hom he
    have ht' := congrArg
      ((cupSingle (setting P n) (iteratedAffineLine B c)).map) ht
    rw [CategoryTheory.Functor.map_comp] at ht'
    have h := compose_transport _ _ _ _ _
      (congrArg (target P n (iteratedAffineLine B c)) hl)
      (congrArg (target P n (iteratedAffineLine B c)) hm) ht'.symm hp
    exact h.trans hq

end AlgebraicGeometry.ProEtale.AffineZeroPurity
