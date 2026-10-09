/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Frobenius-equivariant linear maps and weights

A linear map `g : M → N` between Frobenius modules intertwining the two Frobenius
automorphisms carries eigenvectors to eigenvectors. Hence if `g` is injective, every eigenvalue
of the Frobenius of `M` is one of `N`; if `g` is surjective, every eigenvalue of the Frobenius of
`N` is one of `M`, since the kernel of `g` is stable under the Frobenius. In particular purity
passes to Frobenius-stable subspaces and quotients.

## Main results

- `FrobeniusModule.hasEigenvalue_of_injective` and
  `FrobeniusModule.hasEigenvalue_of_surjective`: the transfer of eigenvalues.
- `FrobeniusModule.IsPureOfWeight.of_injective` and
  `FrobeniusModule.IsPureOfWeight.of_surjective`: purity of subobjects and quotients.
-/

@[expose] public section

universe u v

namespace FrobeniusModule
variable {K : Type v} [Field K] {M N : FrobeniusModule.{u, v} K}
  (g : M.carrier →ₗ[K] N.carrier) (hg : ∀ x, g (M.frobenius x) = N.frobenius (g x))
include hg

/-- An injective Frobenius-equivariant linear map carries eigenvalues of the Frobenius of its
source to eigenvalues of the Frobenius of its target. -/
theorem hasEigenvalue_of_injective (hinj : Function.Injective g) {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : N.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := g x) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, (map_ne_zero_iff _ hinj).2 hx.2⟩
  change N.frobenius (g x) = α • g x
  rw [← hg, ← map_smul]
  exact congrArg g hx.1

/-- Every eigenvalue of the Frobenius of the target of a surjective Frobenius-equivariant linear
map `g` is one of the Frobenius of its source: otherwise `F - α` is injective, hence bijective on
the Frobenius-stable subspace `ker g`, and an eigenvector `g x` would give `x ∈ ker g`. -/
theorem hasEigenvalue_of_surjective (hsurj : Function.Surjective g) {α : K}
    (hα : N.frobeniusEnd.HasEigenvalue α) : M.frobeniusEnd.HasEigenvalue α := by
  by_contra hM
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  let T : Module.End K M.carrier := M.frobeniusEnd - α • LinearMap.id
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    by_contra h0
    refine hM (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, h0⟩
    have : M.frobeniusEnd v - α • v = 0 := hv
    exact sub_eq_zero.1 this
  have hgT : ∀ v, g (T v) = N.frobeniusEnd (g v) - α • g v := fun v ↦ by
    simp [T, frobeniusEnd, hg]
  have hmaps : ∀ v ∈ LinearMap.ker g, T v ∈ LinearMap.ker g := fun v hv ↦ by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hgT, hv, map_zero, smul_zero, sub_zero]
  have hT'inj : Function.Injective (T.restrict hmaps) := fun a b hab ↦
    Subtype.ext (hTinj (congrArg Subtype.val hab))
  have hT'surj := LinearMap.injective_iff_surjective.mp hT'inj
  obtain ⟨x, rfl⟩ := hsurj y
  have hTx : T x ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker, hgT, hy.1, sub_self]
  obtain ⟨z, hz⟩ := hT'surj ⟨T x, hTx⟩
  have hzx : (z : M.carrier) = x := hTinj (congrArg Subtype.val hz)
  apply hy.2
  rw [← hzx]
  exact z.2

/-- A Frobenius-stable subspace of a pure Frobenius module is pure of the same weight. -/
theorem IsPureOfWeight.of_injective (hinj : Function.Injective g) {ι : K →+* ℂ} {q : ℕ} {w : ℝ}
    (h : N.IsPureOfWeight ι q w) : M.IsPureOfWeight ι q w :=
  fun α hα ↦ h α (hasEigenvalue_of_injective g hg hinj hα)

/-- A Frobenius-equivariant quotient of a pure Frobenius module is pure of the same weight. -/
theorem IsPureOfWeight.of_surjective (hsurj : Function.Surjective g) {ι : K →+* ℂ} {q : ℕ}
    {w : ℝ} (h : M.IsPureOfWeight ι q w) : N.IsPureOfWeight ι q w :=
  fun α hα ↦ h α (hasEigenvalue_of_surjective g hg hsurj hα)

end FrobeniusModule
