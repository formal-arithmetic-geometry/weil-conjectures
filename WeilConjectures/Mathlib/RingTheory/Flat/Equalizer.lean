/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-!
# Flat base change preserves equalisers of rings

Let `φ : R ⟶ R'` be a flat ring map and let `A ⟶ B ⇉ C` be an equaliser diagram of
`R`-algebras. If `B` and `C` are compatibly base changed to `B'` and `C'` along `φ`, and
`A ⟶ A'` sits over an injective `A' ⟶ B'` equalising the two maps `B' ⇉ C'`, then `A'` is the
base change of `A`.

Both base change conditions are phrased as `CategoryTheory.IsPushout` squares in `CommRingCat`,
which avoids having to equip the rings involved with `Algebra` instances in the statement.

## Main results

- `CommRingCat.isPushout_of_isEqualizer`
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace CommRingCat

/-- **Flat base change preserves equalisers.**

If `A ⟶ B ⇉ C` is an equaliser diagram of `R`-algebras, `φ : R ⟶ R'` is flat, the squares over
`B` and `C` are pushouts, and `A' ⟶ B'` is injective and equalises `B' ⇉ C'`, then the square
over `A` is a pushout as well. -/
theorem isPushout_of_isEqualizer {R R' A B C A' B' C' : CommRingCat.{u}} {φ : R ⟶ R'}
    (hφ : φ.hom.Flat)
    {rA : R ⟶ A} {rB : R ⟶ B} {rC : R ⟶ C} {a : A ⟶ B} {b₁ b₂ : B ⟶ C}
    {r'A : R' ⟶ A'} {r'B : R' ⟶ B'} {r'C : R' ⟶ C'} {a' : A' ⟶ B'} {b₁' b₂' : B' ⟶ C'}
    {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
    (e₁ : rA ≫ a = rB) (e₂ : rB ≫ b₁ = rC) (e₃ : rB ≫ b₂ = rC)
    (e₁' : r'A ≫ a' = r'B) (e₂' : r'B ≫ b₁' = r'C) (e₃' : r'B ≫ b₂' = r'C)
    (hab : a ≫ b₁ = a ≫ b₂) (ha : Function.Injective a)
    (hex : ∀ x : B, b₁ x = b₂ x → ∃ y : A, a y = x)
    (hab' : a' ≫ b₁' = a' ≫ b₂') (ha' : Function.Injective a')
    (hα : a ≫ β = α ≫ a') (hβ₁ : b₁ ≫ γ = β ≫ b₁') (hβ₂ : b₂ ≫ γ = β ≫ b₂')
    (hB : IsPushout rB φ β r'B) (hC : IsPushout rC φ γ r'C)
    (w : rA ≫ α = φ ≫ r'A) :
    IsPushout rA φ α r'A := by
  let : Algebra ↥R ↥R' := φ.hom.toAlgebra
  let : Algebra ↥R ↥A := rA.hom.toAlgebra
  let : Algebra ↥R ↥B := rB.hom.toAlgebra
  let : Algebra ↥R ↥C := rC.hom.toAlgebra
  have hflat : Module.Flat ↥R ↥R' := hφ
  let aA : ↥A →ₐ[↥R] ↥B :=
    { a.hom with
      commutes' := fun r => by
        simpa [RingHom.algebraMap_toAlgebra] using ConcreteCategory.congr_hom e₁ r }
  let bA₁ : ↥B →ₐ[↥R] ↥C :=
    { b₁.hom with
      commutes' := fun r => by
        simpa [RingHom.algebraMap_toAlgebra] using ConcreteCategory.congr_hom e₂ r }
  let bA₂ : ↥B →ₐ[↥R] ↥C :=
    { b₂.hom with
      commutes' := fun r => by
        simpa [RingHom.algebraMap_toAlgebra] using ConcreteCategory.congr_hom e₃ r }
  have hexact : Function.Exact aA.toLinearMap (bA₁.toLinearMap - bA₂.toLinearMap) := by
    intro x
    constructor
    · intro hx
      exact hex x (by simpa [sub_eq_zero, bA₁, bA₂] using hx)
    · rintro ⟨y, rfl⟩
      have := ConcreteCategory.congr_hom hab y
      simp only [LinearMap.sub_apply, sub_eq_zero]
      simpa [aA, bA₁, bA₂] using this
  have hinj : Function.Injective (aA.toLinearMap.lTensor ↥R') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ ha
  have hex2 : Function.Exact (aA.toLinearMap.lTensor ↥R')
      ((bA₁.toLinearMap - bA₂.toLinearMap).lTensor ↥R') :=
    Module.Flat.lTensor_exact _ hexact
  have hB' : IsPushout (ofHom (algebraMap ↥R ↥R')) (ofHom (algebraMap ↥R ↥B)) r'B β := hB.flip
  have hC' : IsPushout (ofHom (algebraMap ↥R ↥R')) (ofHom (algebraMap ↥R ↥C)) r'C γ := hC.flip
  let eB := (isPushout_tensorProduct ↥R ↥R' ↥B).isoIsPushout _ _ hB'
  let eC := (isPushout_tensorProduct ↥R ↥R' ↥C).isoIsPushout _ _ hC'
  have hBt (r : ↥R') (b : ↥B) : eB.hom (r ⊗ₜ[↥R] b) = r'B r * β b :=
    isoIsPushout_tensorProduct_hom_tmul hB' r b
  have hCt (r : ↥R') (c : ↥C) : eC.hom (r ⊗ₜ[↥R] c) = r'C r * γ c :=
    isoIsPushout_tensorProduct_hom_tmul hC' r c
  have sqb₁ (z : ↥R' ⊗[↥R] ↥B) :
      eC.hom (bA₁.toLinearMap.lTensor ↥R' z) = b₁' (eB.hom z) := by
    induction z with
    | zero => simp
    | tmul r b =>
      have h₁ : b₁' (r'B r) = r'C r := ConcreteCategory.congr_hom e₂' r
      have h₂ : γ (b₁ b) = b₁' (β b) := ConcreteCategory.congr_hom hβ₁ b
      simp only [LinearMap.lTensor_tmul, hCt, hBt, map_mul, h₁, ← h₂]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have sqb₂ (z : ↥R' ⊗[↥R] ↥B) :
      eC.hom (bA₂.toLinearMap.lTensor ↥R' z) = b₂' (eB.hom z) := by
    induction z with
    | zero => simp
    | tmul r b =>
      have h₁ : b₂' (r'B r) = r'C r := ConcreteCategory.congr_hom e₃' r
      have h₂ : γ (b₂ b) = b₂' (β b) := ConcreteCategory.congr_hom hβ₂ b
      simp only [LinearMap.lTensor_tmul, hCt, hBt, map_mul, h₁, ← h₂]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have ptA := isPushout_tensorProduct ↥R ↥R' ↥A
  let Ψ : CommRingCat.of (↥R' ⊗[↥R] ↥A) ⟶ A' := ptA.desc r'A α w.symm
  have hAl (r : ↥R') : Ψ (r ⊗ₜ[↥R] (1 : ↥A)) = r'A r := by
    have := ConcreteCategory.congr_hom (ptA.inl_desc r'A α w.symm) r
    simp only [comp_apply, hom_ofHom, Algebra.TensorProduct.includeLeftRingHom_apply] at this
    exact this
  have hAr (x : ↥A) : Ψ ((1 : ↥R') ⊗ₜ[↥R] x) = α x := by
    have := ConcreteCategory.congr_hom (ptA.inr_desc r'A α w.symm) x
    simp only [comp_apply, hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply] at this
    exact this
  have hAt (r : ↥R') (x : ↥A) : Ψ (r ⊗ₜ[↥R] x) = r'A r * α x := by
    have h : (r ⊗ₜ[↥R] x : ↥R' ⊗[↥R] ↥A) = (r ⊗ₜ[↥R] (1 : ↥A)) * ((1 : ↥R') ⊗ₜ[↥R] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, hAl, hAr]
  have sqa (z : ↥R' ⊗[↥R] ↥A) : eB.hom (aA.toLinearMap.lTensor ↥R' z) = a' (Ψ z) := by
    induction z with
    | zero => simp
    | tmul r x =>
      have h₁ : a' (r'A r) = r'B r := ConcreteCategory.congr_hom e₁' r
      have h₂ : β (a x) = a' (α x) := ConcreteCategory.congr_hom hα x
      simp only [LinearMap.lTensor_tmul, hBt, hAt, map_mul, h₁, ← h₂]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hΨinj : Function.Injective Ψ := by
    intro z z' hz
    apply hinj
    apply (ConcreteCategory.bijective_of_isIso eB.hom).1
    rw [sqa, sqa, hz]
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso eB.hom).2 (a' y)
    have hxeq : (bA₁.toLinearMap - bA₂.toLinearMap).lTensor ↥R' x = 0 := by
      have hb : bA₁.toLinearMap.lTensor ↥R' x = bA₂.toLinearMap.lTensor ↥R' x := by
        apply (ConcreteCategory.bijective_of_isIso eC.hom).1
        rw [sqb₁, sqb₂, hx]
        exact ConcreteCategory.congr_hom hab' y
      simp [LinearMap.lTensor_sub, hb]
    obtain ⟨z, hz⟩ := (hex2 x).mp hxeq
    refine ⟨z, ha' ?_⟩
    rw [← sqa, hz, hx]
  have : IsIso Ψ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hΨinj, hΨsurj⟩
  refine ptA.flip.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso Ψ).symm ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
    rw [IsIso.eq_comp_inv]
    exact ptA.inr_desc r'A α w.symm
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
    rw [IsIso.eq_comp_inv]
    exact ptA.inl_desc r'A α w.symm

end CommRingCat
