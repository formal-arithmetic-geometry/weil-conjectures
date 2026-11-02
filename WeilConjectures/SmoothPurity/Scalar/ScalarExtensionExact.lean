/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi

import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

/-! # Exactness of finite scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-pf-reduction`, order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated).
The shift comparison is specified on integral representatives, including its sign.
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

section CommShiftHelpers

variable {C' D' : Type*} [Category* C'] [Category* D'] {A : Type*} [AddMonoid A]
  [HasShift C' A] [HasShift D' A]

/-- Two shift comparisons with the same components coincide.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem commShift_ext {G : C' ⥤ D'} (c₁ c₂ : G.CommShift A)
    (h : ∀ (a : A) (X : C'), (G.commShiftIso (self := c₁) a).hom.app X =
      (G.commShiftIso (self := c₂) a).hom.app X) : c₁ = c₂ := by
  cases c₁
  cases c₂
  congr
  funext a
  ext X
  exact h a X

/-- A shift comparison compatible with an isomorphism is the conjugated one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem commShiftIso_hom_app_of_natTrans {F G : C' ⥤ D'} (e : F ≅ G)
    [F.CommShift A] [c : G.CommShift A] [h : NatTrans.CommShift e.hom A] (a : A) (X : C') :
    (G.commShiftIso a).hom.app X =
      e.inv.app (X⟦a⟧) ≫ (F.commShiftIso a).hom.app X ≫ (e.hom.app X)⟦a⟧' := by
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), ← NatTrans.shift_app_comm, e.hom_inv_id_app_assoc]

end CommShiftHelpers

section SubcategoryShift

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private theorem ι_commShiftIso_hom_app {C' : Type*} [Category* C'] [HasShift C' ℤ]
    (R : ObjectProperty C') [R.IsStableUnderShift ℤ] (n : ℤ) (X : R.FullSubcategory) :
    (R.ι.commShiftIso n).hom.app X = 𝟙 _ := rfl

/-- The full subcategory inherits the ordinary derived tensor shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the ambient termwise exact tensor functor has its canonical derived shift
comparison. Full faithfulness of the inclusions lifts it uniquely. The ambient zero
and addition coherence equations imply the same equations after this lift. -/
theorem integralConstructibleScalarCommShift_existsUnique :
    ∃! c : (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ,
      (fun [commInst :
          (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) K,
          HEq (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso n).hom.app K).hom
            (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj))
        (commInst := c) := by
  let P := boundedConstructibleDerivedCompleteIntegral D l hl L Y
  let Q := boundedConstructibleDerivedCompleteIntegral D l hl E Y
  let G := integralOrdinaryDerivedScalar l E L ι Y
  have hF : ∀ K : Q.FullSubcategory, P ((Q.ι ⋙ G).obj K) :=
    fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property
  let c : (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
    (inferInstance : (P.lift (Q.ι ⋙ G) hF).CommShift ℤ)
  refine existsUnique_of_exists_of_unique ⟨c, ?_⟩ ?_
  · intro n K
    have h := NatTrans.shift_app_comm (P.liftCompιIso (Q.ι ⋙ G) hF).hom n K
    rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
      ι_commShiftIso_hom_app, ι_commShiftIso_hom_app] at h
    apply heq_of_eq
    simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
      ObjectProperty.ι_map] at h
    refine Eq.trans ?_ (h.trans ?_)
    · erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
      try rfl
    · erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
      try rfl
  · intro c₁ c₂ h₁ h₂
    apply commShift_ext
    intro n K
    apply ObjectProperty.hom_ext
    exact eq_of_heq ((h₁ n K).trans (h₂ n K).symm)

end SubcategoryShift

/-- The uniquely normalized integral shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance integralConstructibleScalarCommShift :
    (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
  (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The rational shift comparison is the integral one tensored with one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: localize the integral shift comparison and inverse. Naturality on pure tensors
extends by additivity. The rational shift by one is the tensor-induced integral shift;
its localization comparison is the identity. Thus the displayed normalization holds.
Iteration and inverse shifts give a coherent comparison for every integer. A coherent
comparison for integer shifts is determined by its component at one, proving uniqueness. -/
theorem rationalOrdinaryScalarCommShift_existsUnique :
    ∃! c : (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst :
          (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        ∀ K, HEq
          (((rationalOrdinaryScalarExtension D l hl E Y L ι).commShiftIso (1 : ℤ)).hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
            (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
              (1 : ℤ)).hom.app K.obj))) (commInst := c) := by
  sorry

/-- The normalized rational shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalOrdinaryScalarCommShift :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose


/-- The published completed functor carries the unique shift comparison making its
normalized comparison with ordinary tensor commute with every integer shift.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: conjugate the ordinary derived tensor comparison by rationalOrdinaryComparison.
The ordinary comparison satisfies zero and addition coherence; naturality of the
conjugating isomorphism carries both equations to the completed functor. The displayed
commutation fixes every component uniquely, including the signed shift by one. -/
theorem rationalConstructibleScalarCommShift_existsUnique :
    ∃! c : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ)
        (commInst := c) := by
  let e := rationalOrdinaryComparison D l hl E Y L ι
  refine existsUnique_of_exists_of_unique
    ⟨Functor.CommShift.ofIso e ℤ, Functor.CommShift.ofIso_compatibility e ℤ⟩ ?_
  intro c₁ c₂ h₁ h₂
  apply commShift_ext
  intro n K
  exact (commShiftIso_hom_app_of_natTrans (c := c₁) (h := h₁) e n K).trans
    (commShiftIso_hom_app_of_natTrans (c := c₂) (h := h₂) e n K).symm

/-- The shift comparison transported through the canonical completion comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalarCommShift :
    (rationalScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The existing completed scalar functor is exact for its specified shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: ordinary finite free tensor is exact on sheaves and hence on derived complexes.
Restriction to the constructible full subcategories and rationalization preserve its
image triangles, proving rationalOrdinaryScalar_exact. The normalized natural
isomorphism rationalOrdinaryComparison commutes with the displayed shifts, so its
triangle isomorphisms transport preservation to the published completed functor. -/
theorem rationalConstructibleScalar_exact :
    (rationalScalarExtension D l hl E Y L ι).IsTriangulated := by
  sorry

/-- The published scalar functor is additive by its original tensor-Hom specification.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalar_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  rationalScalarExtension_additive D l hl E Y L ι

attribute [instance] rationalConstructibleScalar_exact

end WeilConjectures
