/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.Mathlib.LinearAlgebra.Trace

/-!
# Alternating sums of traces along long exact sequences

For a linear map `f : M → N` intertwining endomorphisms `φ` and `ψ`, the trace of `φ` is the sum
of the traces of `φ` on `ker f` and of `ψ` on `range f`
(`LinearMap.trace_eq_trace_restrict_ker_add_trace_restrict_range`).

Consequently, for a bounded long exact sequence `⋯ → Aʲ → Bʲ → Dʲ → Aʲ⁺¹ → ⋯` of
finite-dimensional vector spaces with compatible endomorphisms, the alternating sums of the
traces satisfy `∑ⱼ (-1)ʲ tr(φ_Bʲ) = ∑ⱼ (-1)ʲ tr(φ_Aʲ) + ∑ⱼ (-1)ʲ tr(φ_Dʲ)`
(`LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact`).
-/

@[expose] public section

namespace LinearMap

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- If `f ∘ φ = ψ ∘ f`, then `ker f` is stable under `φ`. -/
lemma apply_mem_ker_of_comp_eq (f : M →ₗ[k] N) {φ : Module.End k M} {ψ : Module.End k N}
    (h : f ∘ₗ φ = ψ ∘ₗ f) : ∀ x ∈ ker f, φ x ∈ ker f := fun x hx ↦ by
  rw [mem_ker] at hx ⊢
  rw [← comp_apply, h, comp_apply, hx, map_zero]

/-- If `f ∘ φ = ψ ∘ f`, then `range f` is stable under `ψ`. -/
lemma apply_mem_range_of_comp_eq (f : M →ₗ[k] N) {φ : Module.End k M} {ψ : Module.End k N}
    (h : f ∘ₗ φ = ψ ∘ₗ f) : ∀ y ∈ range f, ψ y ∈ range f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, by rw [← comp_apply, h, comp_apply]⟩

/-- The trace of the restriction of an endomorphism to a stable submodule only depends on
the submodule, not on the proof that it is stable. -/
lemma trace_restrict_eq_of_eq {φ : Module.End k M} {p q : Submodule k M} (hpq : p = q)
    (hp : ∀ x ∈ p, φ x ∈ p) (hq : ∀ x ∈ q, φ x ∈ q) :
    trace k p (φ.restrict hp) = trace k q (φ.restrict hq) := by
  subst hpq
  rfl

/-- For a linear map `f : M → N` with `f ∘ φ = ψ ∘ f`, the trace of `φ` is the sum of the trace
of `φ` on `ker f` and of the trace of `ψ` on `range f`. -/
theorem trace_eq_trace_restrict_ker_add_trace_restrict_range [FiniteDimensional k M]
    [FiniteDimensional k N] (f : M →ₗ[k] N) {φ : Module.End k M} {ψ : Module.End k N}
    (h : f ∘ₗ φ = ψ ∘ₗ f) (hφ : ∀ x ∈ ker f, φ x ∈ ker f)
    (hψ : ∀ y ∈ range f, ψ y ∈ range f) :
    trace k M φ = trace k (ker f) (φ.restrict hφ) + trace k (range f) (ψ.restrict hψ) := by
  refine trace_eq_trace_add_trace_of_exact (f := (ker f).subtype) (g := f.rangeRestrict) ?_
    (ker f).injective_subtype f.surjective_rangeRestrict ?_ ?_
  · intro x
    simp [Subtype.ext_iff]
  · ext x
    rfl
  · ext x
    simp only [comp_apply, codRestrict_apply, coe_restrict_apply]
    exact congr($h x)

/-- **Alternating sums of traces along long exact sequences.** Let
`⋯ → Aʲ → Bʲ → Dʲ → Aʲ⁺¹ → ⋯` be an exact sequence of finite-dimensional vector spaces, zero
outside a finite range of degrees, with endomorphisms `φ_A`, `φ_B`, `φ_D` commuting with all the
maps. Then `∑ⱼ (-1)ʲ tr(φ_Bʲ) = ∑ⱼ (-1)ʲ tr(φ_Aʲ) + ∑ⱼ (-1)ʲ tr(φ_Dʲ)`.

With `αⱼ`, `βⱼ`, `δⱼ` the traces on `ker uⱼ`, `ker vⱼ`, `ker wⱼ`, exactness gives
`tr(φ_Aʲ) = αⱼ + βⱼ`, `tr(φ_Bʲ) = βⱼ + δⱼ` and `tr(φ_Dʲ) = δⱼ + αⱼ₊₁`, and the sum telescopes. -/
theorem finsum_negOnePow_smul_trace_eq_add_of_exact {A B D : ℤ → Type*}
    [∀ j, AddCommGroup (A j)] [∀ j, Module k (A j)] [∀ j, FiniteDimensional k (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module k (B j)] [∀ j, FiniteDimensional k (B j)]
    [∀ j, AddCommGroup (D j)] [∀ j, Module k (D j)] [∀ j, FiniteDimensional k (D j)]
    (φA : ∀ j, Module.End k (A j)) (φB : ∀ j, Module.End k (B j))
    (φD : ∀ j, Module.End k (D j)) (u : ∀ j, A j →ₗ[k] B j) (v : ∀ j, B j →ₗ[k] D j)
    (w : ∀ j, D j →ₗ[k] A (j + 1)) (hu : ∀ j, u j ∘ₗ φA j = φB j ∘ₗ u j)
    (hv : ∀ j, v j ∘ₗ φB j = φD j ∘ₗ v j) (hw : ∀ j, w j ∘ₗ φD j = φA (j + 1) ∘ₗ w j)
    (ex₁ : ∀ j, Function.Exact (u j) (v j)) (ex₂ : ∀ j, Function.Exact (v j) (w j))
    (ex₃ : ∀ j, Function.Exact (w j) (u (j + 1)))
    (hbdd : ∃ a b : ℤ, ∀ j, (j < a ∨ b < j) →
      Subsingleton (A j) ∧ Subsingleton (B j) ∧ Subsingleton (D j)) :
    ∑ᶠ j, (j.negOnePow : ℤ) • trace k (B j) (φB j) =
      ∑ᶠ j, (j.negOnePow : ℤ) • trace k (A j) (φA j) +
        ∑ᶠ j, (j.negOnePow : ℤ) • trace k (D j) (φD j) := by
  obtain ⟨a, b, hab⟩ := hbdd
  set α : ℤ → k := fun j ↦ trace k _ ((φA j).restrict (apply_mem_ker_of_comp_eq _ (hu j)))
  set β : ℤ → k := fun j ↦ trace k _ ((φB j).restrict (apply_mem_ker_of_comp_eq _ (hv j)))
  set δ : ℤ → k := fun j ↦ trace k _ ((φD j).restrict (apply_mem_ker_of_comp_eq _ (hw j)))
  have eA (j : ℤ) : trace k (A j) (φA j) = α j + β j := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (u j) (hu j)
      (apply_mem_ker_of_comp_eq _ (hu j)) (apply_mem_range_of_comp_eq _ (hu j)),
      trace_restrict_eq_of_eq (exact_iff.1 (ex₁ j)).symm _ (apply_mem_ker_of_comp_eq _ (hv j))]
  have eB (j : ℤ) : trace k (B j) (φB j) = β j + δ j := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (v j) (hv j)
      (apply_mem_ker_of_comp_eq _ (hv j)) (apply_mem_range_of_comp_eq _ (hv j)),
      trace_restrict_eq_of_eq (exact_iff.1 (ex₂ j)).symm _ (apply_mem_ker_of_comp_eq _ (hw j))]
  have eD (j : ℤ) : trace k (D j) (φD j) = δ j + α (j + 1) := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (w j) (hw j)
      (apply_mem_ker_of_comp_eq _ (hw j)) (apply_mem_range_of_comp_eq _ (hw j)),
      trace_restrict_eq_of_eq (exact_iff.1 (ex₃ j)).symm _
        (apply_mem_ker_of_comp_eq _ (hu (j + 1)))]
  set c : ℤ → k := fun j ↦ (j.negOnePow : ℤ) • α j
  have key (j : ℤ) : (j.negOnePow : ℤ) • trace k (B j) (φB j) =
      ((j.negOnePow : ℤ) • trace k (A j) (φA j) + (j.negOnePow : ℤ) • trace k (D j) (φD j)) +
        (c (j + 1) - c j) := by
    simp only [c, eA, eB, eD, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_add]
    abel
  have hfin {f : ℤ → k} (hf : ∀ j, (j < a - 1 ∨ b < j) → f j = 0) : f.support.Finite :=
    (Set.finite_Icc (a - 1) b).subset fun j hj ↦ by
      by_contra h
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      exact hj (hf j h)
  have hout {j : ℤ} (hj : j < a - 1 ∨ b < j) :
      Subsingleton (A j) ∧ Subsingleton (B j) ∧ Subsingleton (D j) :=
    hab j (hj.imp (fun h ↦ by omega) fun h ↦ h)
  have hfA : (fun j ↦ (j.negOnePow : ℤ) • trace k (A j) (φA j)).support.Finite :=
    hfin fun j hj ↦ by
      have := (hout hj).1
      rw [trace_eq_zero_of_subsingleton, smul_zero]
  have hfD : (fun j ↦ (j.negOnePow : ℤ) • trace k (D j) (φD j)).support.Finite :=
    hfin fun j hj ↦ by
      have := (hout hj).2.2
      rw [trace_eq_zero_of_subsingleton, smul_zero]
  have hc {j : ℤ} (hj : j < a ∨ b < j) : c j = 0 := by
    have := (hab j hj).1
    simp only [c, α]
    rw [trace_eq_zero_of_subsingleton, smul_zero]
  have hfc : c.support.Finite := hfin fun j hj ↦ hc (hj.imp (fun h ↦ by omega) fun h ↦ h)
  have hfc' : (fun j ↦ c (j + 1)).support.Finite :=
    hfin fun j hj ↦ hc (hj.imp (fun h ↦ by omega) (fun h ↦ by omega))
  have hshift : ∑ᶠ j, c (j + 1) = ∑ᶠ j, c j := finsum_comp_equiv (Equiv.addRight 1)
  rw [finsum_congr key, finsum_add_distrib (hfA.union hfD |>.subset (Function.support_add _ _))
    (hfc'.union hfc |>.subset (Function.support_sub _ _)), finsum_add_distrib hfA hfD,
    finsum_sub_distrib hfc' hfc, hshift,
    sub_self, add_zero]

end LinearMap

end
