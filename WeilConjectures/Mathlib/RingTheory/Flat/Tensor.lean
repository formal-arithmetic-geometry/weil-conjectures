/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Pure maps into flat modules, and complexes of flat modules

A linear map `f : N → P` into a flat module whose base changes `f ⊗ R ⧸ I` are all injective has
a flat cokernel. As an application, for a complex `K⁰ → K¹ → K²` of flat modules which stays
exact at `K¹` after every base change `- ⊗ R ⧸ I`, forming the kernel of `K⁰ → K¹` commutes with
every base change: `ker d⁰ ⊗ M → K⁰ ⊗ M` is injective for every module `M`.

This is the algebra behind cohomology and base change in degree `0`: if the Čech complex of a
module which is flat over the base computes a cohomology which vanishes in degree `1` after every
base change, then its global sections commute with base change.

## Main results

- `Module.Flat.quotient_range_of_rTensor_injective`: the cokernel of a pure map into a flat
  module is flat.
- `Module.Flat.lTensor_ker_subtype_injective`: the kernel of the first map of a complex of flat
  modules which is universally exact in the middle commutes with base change.
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {R N P : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup P] [Module R N]
  [Module R P]

/-- **The cokernel of a pure map into a flat module is flat.** If `P` is flat and
`f ⊗ R ⧸ I : N ⊗ R ⧸ I → P ⊗ R ⧸ I` is injective for every ideal `I`, then `P ⧸ f(N)` is
flat. -/
theorem quotient_range_of_rTensor_injective [Module.Flat R P] (f : N →ₗ[R] P)
    (hf : ∀ I : Ideal R, Function.Injective (f.rTensor (R ⧸ I))) :
    Module.Flat R (P ⧸ LinearMap.range f) := by
  set Q := P ⧸ LinearMap.range f
  set q := (LinearMap.range f).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hfq : Function.Exact f q := LinearMap.exact_map_mkQ_range f
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- lift `x` to `P ⊗ I`
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective I hq x
  have h1 : q.rTensor R (I.subtype.lTensor P y) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx]
  obtain ⟨z, hz⟩ := (_root_.rTensor_exact R hfq hq _).mp h1
  -- `z` comes from `N ⊗ I`, by purity of `f` for `R ⧸ I`
  have h2 : (Submodule.mkQ I).lTensor N z = 0 := by
    apply hf I
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hz, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp]
    have : (Submodule.mkQ I).comp (Submodule.subtype I) = 0 := by
      ext a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr a.2
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w, rfl⟩ := (_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ I)
    (Submodule.mkQ_surjective I) z).mp h2
  -- hence `y` comes from `N ⊗ I`, by flatness of `P`
  have h3 : y = f.rTensor I w := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) I.subtype
      Subtype.val_injective
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [h3, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfq.linearMap_comp_eq_zero,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

variable {K₀ K₁ K₂ : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
  [Module R K₀] [Module R K₁] [Module R K₂]

/-- **The kernel of a universally exact complex of flat modules commutes with base change.**
Let `K⁰ → K¹ → K²` be a complex of flat `R`-modules which stays exact at `K¹` after base change
to `R ⧸ I` for every ideal `I`. Then `M ⊗ ker d⁰ → M ⊗ K⁰` is injective for every module `M`.

Writing `C = K¹ ⧸ d⁰(K⁰)`, the exactness says that `C → K²` stays injective after every base
change `- ⊗ R ⧸ I`, so `K² ⧸ C` is flat (`Module.Flat.quotient_range_of_rTensor_injective`),
hence so are `C`, the image `d⁰(K⁰)` and the conclusion follows from the flatness of the image. -/
theorem lTensor_ker_subtype_injective [Module.Flat R K₀] [Module.Flat R K₁] [Module.Flat R K₂]
    (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
    (hex : ∀ I : Ideal R, Function.Exact (d₀.lTensor (R ⧸ I)) (d₁.lTensor (R ⧸ I)))
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((LinearMap.ker d₀).subtype.lTensor M) := by
  -- the case `I = ⊥` is the exactness of the complex itself
  have hex₀ : Function.Exact d₀ d₁ := by
    let e : (R ⧸ (⊥ : Ideal R)) ≃ₗ[R] R := Submodule.quotEquivOfEqBot ⊥ rfl
    refine Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := (TensorProduct.congr e (LinearEquiv.refl R K₀)).trans (TensorProduct.lid R K₀))
      (e₂ := (TensorProduct.congr e (LinearEquiv.refl R K₁)).trans (TensorProduct.lid R K₁))
      (e₃ := (TensorProduct.congr e (LinearEquiv.refl R K₂)).trans (TensorProduct.lid R K₂))
      ?_ ?_ (hex ⊥)
    · exact TensorProduct.ext' fun x y ↦ by simp
    · exact TensorProduct.ext' fun x y ↦ by simp
  -- `C = K¹ ⧸ d⁰(K⁰)` and the induced injection `C → K²`
  have hle : LinearMap.range d₀ ≤ LinearMap.ker d₁ := fun _ ⟨y, hy⟩ ↦
    hy ▸ hex₀.apply_apply_eq_zero y
  set c := (LinearMap.range d₀).mkQ
  set d₁' := (LinearMap.range d₀).liftQ d₁ hle
  have hd₁' : d₁'.comp c = d₁ := Submodule.liftQ_mkQ _ _ _
  have hc : Function.Surjective c := Submodule.mkQ_surjective _
  have hd₁'inj : Function.Injective d₁' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hc x
    obtain ⟨z, rfl⟩ := (hex₀ y).mp (by rw [← hx, ← hd₁', LinearMap.comp_apply])
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
  have hpure (I : Ideal R) : Function.Injective (d₁'.rTensor (R ⧸ I)) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (R ⧸ I) hc x
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hd₁'] at hx
    obtain ⟨z, rfl⟩ := (hex I y).mp hx
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      (LinearMap.exact_map_mkQ_range d₀).linearMap_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  -- flatness of `K² ⧸ C`, `C` and `d⁰(K⁰)`
  have : Module.Flat R (K₂ ⧸ LinearMap.range d₁') := quotient_range_of_rTensor_injective d₁' hpure
  have : Module.Flat R (K₁ ⧸ LinearMap.range d₀) :=
    Module.Flat.of_exact_of_flat_of_flat_right d₁' (LinearMap.range d₁').mkQ hd₁'inj
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range d₁')
  have : Module.Flat R (LinearMap.range d₀) :=
    Module.Flat.of_exact_of_flat_of_flat_right (LinearMap.range d₀).subtype c
      Subtype.val_injective hc (LinearMap.exact_subtype_mkQ _)
  exact LinearMap.lTensor_injective_of_exact_of_flat d₀.rangeRestrict
    (LinearMap.surjective_rangeRestrict d₀) (LinearMap.ker d₀).subtype Subtype.val_injective
    (LinearMap.ker_rangeRestrict d₀ ▸ LinearMap.exact_subtype_ker_map d₀.rangeRestrict)
    M

end Module.Flat
