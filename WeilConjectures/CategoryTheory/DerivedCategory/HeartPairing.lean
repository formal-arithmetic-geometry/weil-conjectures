/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Evaluation pairings against an object which is projective and injective

Let `C` be an `R`-linear abelian category and `U : C` an object which is both projective and
injective, placed in degree `0` in the derived category: `T = U[0]`. For every `M ∈ D(C)`, the
evaluation pairing

`Hom(T, M) × Hom(M, T) ⟶ End(T)`, `(x, f) ↦ x ≫ f`

is identified with the evaluation pairing `Hom_C(U, H) × Hom_C(H, U) ⟶ End_C(U)` of an object
`H` of `C` (the cohomology `H⁰(M)`): maps from `T` only see `τ^{≥ 0} M` by projectivity of `U`,
maps to `T` only see `τ^{≤ 0} M` by injectivity, and the heart is `C`.

## Main statements

- `DerivedCategory.singleFunctor_obj_hom_eq_zero_of_projective`: `Hom(P[0], N) = 0` for `P`
  projective and `N ∈ D^{≤ n}`, `n < 0`.
- `DerivedCategory.hom_singleFunctor_obj_eq_zero_of_injective`: `Hom(N, I[0]) = 0` for `I`
  injective and `N ∈ D^{≥ n}`, `0 < n`.
- `DerivedCategory.exists_linearEquiv_hom_singleFunctor_obj`: the identification of the
  evaluation pairing with that of an object of the heart.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u t

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For `P` projective, there are no nonzero morphisms `P[0] ⟶ N` to an object `N ∈ D^{≤ n}` with
`n < 0`. -/
lemma singleFunctor_obj_hom_eq_zero_of_projective {P : C} [Projective P] {N : DerivedCategory C}
    (n : ℤ) (hn : n < 0) [N.IsLE n] (φ : (singleFunctor C 0).obj P ⟶ N) : φ = 0 := by
  obtain ⟨K, _, ⟨e⟩⟩ := N.exists_iso_Q_obj_of_isLE n
  have := from_singleFunctor_obj_eq_zero_of_projective
    ((singleFunctorIsoCompQ C 0).inv.app P ≫ φ ≫ e.hom) n hn
  rw [← cancel_mono e.hom, zero_comp, ← cancel_epi ((singleFunctorIsoCompQ C 0).inv.app P),
    comp_zero]
  simpa only [Category.assoc] using this

/-- For `I` injective, there are no nonzero morphisms `N ⟶ I[0]` from an object `N ∈ D^{≥ n}` with
`0 < n`. -/
lemma hom_singleFunctor_obj_eq_zero_of_injective {I : C} [Injective I] {N : DerivedCategory C}
    (n : ℤ) (hn : 0 < n) [N.IsGE n] (φ : N ⟶ (singleFunctor C 0).obj I) : φ = 0 := by
  obtain ⟨K, _, ⟨e⟩⟩ := N.exists_iso_Q_obj_of_isGE n
  have := to_singleFunctor_obj_eq_zero_of_injective
    (e.inv ≫ φ ≫ (singleFunctorIsoCompQ C 0).hom.app I) n hn
  rw [← cancel_epi e.inv, comp_zero, ← cancel_mono ((singleFunctorIsoCompQ C 0).hom.app I),
    zero_comp]
  simpa only [Category.assoc] using this

variable (R : Type t) [Ring R] [Linear R C]

/-- Let `U` be projective and injective and `T = U[0]`. For every `M ∈ D(C)` there are an object
`H` of `C` (the cohomology `H⁰(M)`) and `R`-linear bijections `α : Hom(U, H) ≃ Hom(T, M)` and
`β : Hom(M, T) ≃ Hom(H, U)` identifying the evaluation pairing `(x, f) ↦ x ≫ f` of `M` against
`T` with the evaluation pairing of `H` against `U`. -/
theorem exists_linearEquiv_hom_singleFunctor_obj (U : C) [Projective U] [Injective U]
    (M : DerivedCategory C) :
    ∃ (H : C) (α : (U ⟶ H) ≃ₗ[R] ((singleFunctor C 0).obj U ⟶ M))
      (β : (M ⟶ (singleFunctor C 0).obj U) ≃ₗ[R] (H ⟶ U)),
      ∀ s f, α s ≫ f = (singleFunctor C 0).map (s ≫ β f) := by
  let t := TStructure.t (C := C)
  set T := (singleFunctor C 0).obj U
  obtain ⟨A, M', hA, hM', i₁, p₁, d₁, h₁⟩ := t.exists_triangle M (-1) 0 (by norm_num)
  have : t.IsLE A (-1) := ⟨hA⟩
  have : t.IsGE M' 0 := ⟨hM'⟩
  obtain ⟨N, B, hN, hB, i₂, p₂, d₂, h₂⟩ := t.exists_triangle M' 0 1 (by norm_num)
  have : t.IsLE N 0 := ⟨hN⟩
  have : t.IsGE B 1 := ⟨hB⟩
  have : t.IsLE (A⟦(1 : ℤ)⟧) (-2) := t.isLE_shift A (-1) 1 (-2)
  have : t.IsGE (B⟦(-1 : ℤ)⟧) 2 := t.isGE_shift B 1 (-1) 2
  have h₂' := inv_rot_of_distTriang _ h₂
  have : t.IsGE N 0 := t.isGE₂ _ h₂' 0 (t.isGE_of_ge _ 0 2) (by dsimp; infer_instance)
  obtain ⟨H, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE N 0
  -- the four bijections
  let L₁ : (U ⟶ H) ≃ₗ[R] (T ⟶ (singleFunctor C 0).obj H) :=
    LinearEquiv.ofBijective ((singleFunctor C 0).mapLinearMap R)
      ⟨(singleFunctor C 0).map_injective, (singleFunctor C 0).map_surjective⟩
  let L₂ : (T ⟶ (singleFunctor C 0).obj H) ≃ₗ[R] (T ⟶ N) := Linear.homCongr R (Iso.refl _) e.symm
  let L₃ : (T ⟶ N) ≃ₗ[R] (T ⟶ M') := LinearEquiv.ofBijective (Linear.rightComp R T i₂) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ _ h₂' z hz
      rw [t.zero g 0 2, zero_comp]
    · obtain ⟨z, rfl⟩ := Triangle.coyoneda_exact₂ _ h₂ g (t.zero _ 0 1)
      exact ⟨z, rfl⟩
  let L₄ : (T ⟶ M) ≃ₗ[R] (T ⟶ M') := LinearEquiv.ofBijective (Linear.rightComp R T p₁) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₂ _ h₁ x hx
      rw [singleFunctor_obj_hom_eq_zero_of_projective (-1) (by norm_num) y, zero_comp]
    · obtain ⟨x, rfl⟩ := Triangle.coyoneda_exact₃ _ h₁ g
        (singleFunctor_obj_hom_eq_zero_of_projective (-2) (by norm_num) _)
      exact ⟨x, rfl⟩
  let K₁ : (H ⟶ U) ≃ₗ[R] ((singleFunctor C 0).obj H ⟶ T) :=
    LinearEquiv.ofBijective ((singleFunctor C 0).mapLinearMap R)
      ⟨(singleFunctor C 0).map_injective, (singleFunctor C 0).map_surjective⟩
  let K₂ : ((singleFunctor C 0).obj H ⟶ T) ≃ₗ[R] (N ⟶ T) := Linear.homCongr R e.symm (Iso.refl _)
  let K₃ : (M' ⟶ T) ≃ₗ[R] (N ⟶ T) := LinearEquiv.ofBijective (Linear.leftComp R T i₂) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun f hf ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ f hf
      rw [hom_singleFunctor_obj_eq_zero_of_injective 1 (by norm_num) g, comp_zero]
    · obtain ⟨f, rfl⟩ := Triangle.yoneda_exact₂ _ h₂' g
        (hom_singleFunctor_obj_eq_zero_of_injective 2 (by norm_num) _)
      exact ⟨f, rfl⟩
  let K₄ : (M' ⟶ T) ≃ₗ[R] (M ⟶ T) := LinearEquiv.ofBijective (Linear.leftComp R T p₁) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun f hf ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ _ h₁ f hf
      rw [t.zero g (-2) 0, comp_zero]
    · obtain ⟨f, rfl⟩ := Triangle.yoneda_exact₂ _ h₁ g (t.zero _ (-1) 0)
      exact ⟨f, rfl⟩
  refine ⟨H, L₁ ≪≫ₗ L₂ ≪≫ₗ L₃ ≪≫ₗ L₄.symm, K₄.symm ≪≫ₗ K₃ ≪≫ₗ K₂.symm ≪≫ₗ K₁.symm,
    fun s f ↦ ?_⟩
  obtain ⟨f', rfl⟩ := K₄.surjective f
  have h₁ : (L₁ ≪≫ₗ L₂ ≪≫ₗ L₃ ≪≫ₗ L₄.symm) s ≫ p₁ = L₃ (L₂ (L₁ s)) :=
    L₄.apply_symm_apply _
  have h₂ : K₁ ((K₄.symm ≪≫ₗ K₃ ≪≫ₗ K₂.symm ≪≫ₗ K₁.symm) (K₄ f')) = K₂.symm (K₃ f') := by
    simp
  have h₃ : (singleFunctor C 0).map ((K₄.symm ≪≫ₗ K₃ ≪≫ₗ K₂.symm ≪≫ₗ K₁.symm) (K₄ f')) =
      e.inv ≫ i₂ ≫ f' := by
    simpa [K₁, K₂, K₃] using h₂
  rw [Functor.map_comp, h₃]
  simpa [L₁, L₂, L₃, K₄] using congrArg (· ≫ f') h₁

end DerivedCategory
