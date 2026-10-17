/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.LiftComplete
public import WeilConjectures.RingTheory.Etale.DepthTwo.Local
public import WeilConjectures.RingTheory.Smooth.SectionTruncation
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Regular pairs on the infinitesimal neighbourhoods of a section

Let `O` be a local ring and `R` a Noetherian formally smooth `O`-algebra with a section
`R → O` of kernel `I`. If `(a, b)` is a regular pair on an `O`-module `T`, then
`(a, c)` is a regular pair on `(R / Iⁿ) ⊗_O T` for every `c ∈ R` with `c ≡ b` modulo `I`
(`RingTheory.DepthTwo.isRegularPair_quotient_pow_tensor`). The proof filters `R / Iⁿ` by the
powers of `I`: the graded pieces `Iᵏ / Iᵏ⁺¹` are flat over `O` and killed by `I`, so that `c`
acts on them as `b`, and regular pairs extend along short exact sequences
(`RingTheory.DepthTwo.IsRegularPair.of_ker_of_surjective`).
-/

@[expose] public section

open scoped Pointwise

open TensorProduct

namespace RingTheory.DepthTwo

section Exact

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- An element regular on the kernel and on the target of a linear map is regular on the
source. -/
lemma isSMulRegular_of_ker {r : R} (g : M →ₗ[R] N) (hK : IsSMulRegular (LinearMap.ker g) r)
    (hN : IsSMulRegular N r) : IsSMulRegular M r := by
  intro x y h
  have h' : r • x = r • y := h
  have h1 : g x = g y := hN (by simp only [← map_smul, h'])
  have hmem : x - y ∈ LinearMap.ker g := by simp [h1]
  have : (⟨x - y, hmem⟩ : LinearMap.ker g) = 0 := hK (by ext; simp [smul_sub, h'])
  exact sub_eq_zero.1 (congrArg Subtype.val this)

/-- **Regular pairs extend along short exact sequences.** If `g : M → N` is surjective and
`(a, b)` is a regular pair on `ker g` and on `N`, then it is a regular pair on `M`. -/
lemma IsRegularPair.of_ker_of_surjective {a b : R} (g : M →ₗ[R] N)
    (hg : Function.Surjective g) (hK : IsRegularPair a b (LinearMap.ker g))
    (hN : IsRegularPair a b N) : IsRegularPair a b M := by
  refine ⟨isSMulRegular_of_ker g hK.1 hN.1, isSMulRegular_of_ker g hK.2.1 hN.2.1,
    fun m hm ↦ ?_⟩
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and] at hm ⊢
  obtain ⟨m', hm'⟩ := hm
  have h1 : b • g m ∈ a • (⊤ : Submodule R N) := by
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    exact ⟨g m', by rw [← map_smul, hm', map_smul]⟩
  have h2 := hN.2.2 _ h1
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and] at h2
  obtain ⟨y'', hy''⟩ := h2
  obtain ⟨y, rfl⟩ := hg y''
  have hk : m - a • y ∈ LinearMap.ker g := by simp [← hy'']
  have hbk : b • (m - a • y) = a • (m' - b • y) := by
    rw [smul_sub, smul_sub, hm', smul_comm a b]
  have hk' : m' - b • y ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    refine hN.1 ?_
    have : g (b • (m - a • y)) = 0 := by rw [map_smul, LinearMap.mem_ker.1 hk, smul_zero]
    simp only [smul_zero]
    rw [← map_smul, ← hbk, this]
  have h3 : (⟨m - a • y, hk⟩ : LinearMap.ker g) ∈ a • (⊤ : Submodule R (LinearMap.ker g)) := by
    refine hK.2.2 _ ?_
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    exact ⟨⟨_, hk'⟩, Subtype.ext (by simp [hbk])⟩
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and] at h3
  obtain ⟨z, hz⟩ := h3
  refine ⟨y + z, ?_⟩
  have := congrArg Subtype.val hz
  simp only [SetLike.val_smul] at this
  rw [smul_add, this, add_sub_cancel]

/-- If two elements act in the same way on `M`, they form regular pairs with the same
elements. -/
lemma IsRegularPair.congr_right {a c d : R} (h : ∀ m : M, c • m = d • m)
    (hM : IsRegularPair a c M) : IsRegularPair a d M := by
  obtain ⟨ha, hc, hac⟩ := hM
  refine ⟨ha, fun x y hxy ↦ hc ?_, fun m hm ↦ hac m ?_⟩
  · have : d • x = d • y := hxy
    simpa only [h] using this
  · rwa [h]

/-- The kernel of a surjection between flat modules is flat. -/
lemma flat_ker_of_surjective {P : Type*} [AddCommGroup P] [Module R P] [Module.Flat R N]
    [Module.Flat R P] (f : N →ₗ[R] P) (hf : Function.Surjective f) :
    Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ L hL
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
    (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) X
  have h2 : Function.Injective (L.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  have h3 : (L.rTensor N).comp ((LinearMap.ker f).subtype.lTensor X) =
      ((LinearMap.ker f).subtype.lTensor Y).comp (L.rTensor (LinearMap.ker f)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h4 : Function.Injective (((LinearMap.ker f).subtype.lTensor Y).comp
      (L.rTensor (LinearMap.ker f))) := by
    rw [← h3]
    exact h2.comp h1
  exact Function.Injective.of_comp h4

end Exact

section Main

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] [Algebra R O]
  [IsScalarTower O R O] [IsLocalRing O] [IsNoetherianRing R] [Algebra.FormallySmooth O R]
  {T : Type*} [AddCommGroup T] [Module O T]

/-- Regular pairs on the infinitesimal neighbourhoods `(R / Iⁿ) ⊗_O T` of a section of a
formally smooth algebra. -/
theorem isRegularPair_quotient_pow_tensor {a b : O} (hT : IsRegularPair a b T) (n : ℕ) {c : R}
    (hc : c - algebraMap O R b ∈ RingHom.ker (algebraMap R O)) :
    IsRegularPair (algebraMap O R a) c ((R ⧸ RingHom.ker (algebraMap R O) ^ n) ⊗[O] T) := by
  set I := RingHom.ker (algebraMap R O)
  induction n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    refine ⟨fun x y _ ↦ Subsingleton.elim _ _, fun x y _ ↦ Subsingleton.elim _ _,
      fun m _ ↦ ?_⟩
    rw [Subsingleton.elim m 0]
    exact zero_mem _
  | succ n ih =>
    let f : (R ⧸ I ^ (n + 1)) →ₗ[R] R ⧸ I ^ n :=
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) n.le_succ)).toLinearMap
    have hf : Function.Surjective f :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := I) n.le_succ)
    let f₀ : (R ⧸ I ^ (n + 1)) →ₗ[O] R ⧸ I ^ n := f.restrictScalars O
    let F := LinearMap.ker f₀
    let g := AlgebraTensorModule.rTensor O T f
    have hg : Function.Surjective g := by
      rw [AlgebraTensorModule.coe_rTensor]
      exact LinearMap.rTensor_surjective T (g := f₀) hf
    let j : F ⊗[O] T →ₗ[O] (R ⧸ I ^ (n + 1)) ⊗[O] T := F.subtype.rTensor T
    have : Module.Flat O (R ⧸ I ^ (n + 1)) := Algebra.FormallySmooth.flat_quotient_pow_ker O R _
    have : Module.Flat O (R ⧸ I ^ n) := Algebra.FormallySmooth.flat_quotient_pow_ker O R _
    have hFflat : Module.Flat O F := flat_ker_of_surjective f₀ hf
    -- `j` is injective with image `ker g`
    have hj : Function.Injective j :=
      (LinearMap.lTensor_inj_iff_rTensor_inj T _).1
        (LinearMap.lTensor_injective_of_exact_of_flat f₀ hf F.subtype F.subtype_injective
          (LinearMap.exact_subtype_ker_map f₀) T)
    have hrange (k : (R ⧸ I ^ (n + 1)) ⊗[O] T) : g k = 0 ↔ k ∈ Set.range j :=
      rTensor_exact T (LinearMap.exact_subtype_ker_map f₀) hf k
    -- `I` kills `ker g`
    have hIF (i : R) (hi : i ∈ I) (x : F ⊗[O] T) : i • j x = 0 := by
      induction x with
      | zero => rw [map_zero, smul_zero]
      | tmul y t =>
        obtain ⟨y, hy⟩ := y
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hr : r ∈ I ^ n := Ideal.Quotient.eq_zero_iff_mem.1 hy
        have : i • (Ideal.Quotient.mk (I ^ (n + 1)) r) = 0 := by
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
          exact Ideal.Quotient.eq_zero_iff_mem.2
            (by rw [pow_succ']; exact Ideal.mul_mem_mul hi hr)
        simp only [j, LinearMap.rTensor_tmul, Submodule.coe_subtype]
        rw [TensorProduct.smul_tmul', this, TensorProduct.zero_tmul]
      | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    have hIK (k : LinearMap.ker g) : c • k = algebraMap O R b • k := by
      obtain ⟨x, hx⟩ := (hrange k).1 k.2
      have : (c - algebraMap O R b) • (k : (R ⧸ I ^ (n + 1)) ⊗[O] T) = 0 := by
        rw [← hx, hIF _ hc]
      apply Subtype.ext
      rw [sub_smul, sub_eq_zero] at this
      exact this
    -- the pair on `ker g`
    have hFT : IsRegularPair a b (F ⊗[O] T) :=
      isRegularPair_of_isWeaklyRegular
        (isWeaklyRegular_of_isRegularPair hT).isWeaklyRegular_lTensor (hT.2.1.lTensor F)
    let e : F ⊗[O] T ≃ₗ[O] (LinearMap.ker g).restrictScalars O :=
      (LinearEquiv.ofInjective j hj).trans
        (LinearEquiv.ofEq _ _ (Submodule.ext fun k ↦ by
          rw [LinearMap.mem_range, Submodule.restrictScalars_mem, LinearMap.mem_ker, hrange,
            Set.mem_range]))
    have hK : IsRegularPair a b (LinearMap.ker g) := hFT.of_linearEquiv e
    have hK' : IsRegularPair (algebraMap O R a) c (LinearMap.ker g) :=
      (isRegularPair_algebraMap_iff.2 hK).congr_right fun k ↦ (hIK k).symm
    exact IsRegularPair.of_ker_of_surjective g hg hK' ih

end Main

end RingTheory.DepthTwo
