/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Weil numbers

An element `α` of a field of characteristic zero is a *`q`-Weil number of weight `w`*
(blueprint `def-weil-numbers`) if it is algebraic over `ℚ` and `|τ α| = q ^ (w / 2)` for every
field embedding `τ : ℚ(α) → ℂ`. Equivalently, every complex conjugate of `α` (every complex
root of its minimal polynomial over `ℚ`) has absolute value `q ^ (w / 2)`.

## Main statements

- `IsWeilNumber`: the predicate of being a `q`-Weil number of weight `w`.
- `isWeilNumber_iff`: characterization through the complex roots of the minimal polynomial.
- `isWeilNumber_algHom_apply_iff`, `isWeilNumber_algEquiv_apply_iff`: the Weil-number condition
  is invariant under `ℚ`-algebra embeddings, in particular under `Gal(ℚ̄/ℚ)`.
- `isUniversallyPureOfWeight_iff_isWeilNumber_inv`: a nonzero complex number is universally pure
  of weight `w` iff its inverse is a Weil number of weight `w`.
- `PadicAlgCl.isWeilNumber_of_forall_ringEquiv`: the intrinsic-weight clause of the blueprint
  lemma `lem-embedding-extension`.
-/

@[expose] public section

open IntermediateField Polynomial

section Defs

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Blueprint `def-weil-numbers`: `α` is a *`q`-Weil number of weight `w`* if it is algebraic
over `ℚ` and every `ℚ`-embedding `τ : ℚ(α) → ℂ` satisfies `‖τ α‖ = q ^ (w / 2)`. -/
def IsWeilNumber (q : ℕ) (w : ℝ) (α : K) : Prop :=
  IsIntegral ℚ α ∧ ∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ α)‖ = (q : ℝ) ^ (w / 2)

/-- For `α` integral over `ℚ`, a property holds for the images of `α` under all embeddings
`ℚ(α) → ℂ` iff it holds for all complex roots of the minimal polynomial of `α`. -/
theorem forall_algHom_adjoin_iff_forall_mem_roots {α : K} (hα : IsIntegral ℚ α)
    (P : ℂ → Prop) :
    (∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, P (τ (AdjoinSimple.gen ℚ α))) ↔
      ∀ y ∈ ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots, P y := by
  refine ⟨fun h y hy ↦ ?_, fun h τ ↦ h _ ?_⟩
  · have := h ((algHomAdjoinIntegralEquiv ℚ hα).symm ⟨y, hy⟩)
    rwa [algHomAdjoinIntegralEquiv_symm_apply_gen] at this
  · refine mem_aroots.2 ⟨minpoly.ne_zero hα, ?_⟩
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]

/-- Blueprint `def-weil-numbers`: `α` is a `q`-Weil number of weight `w` iff it is integral over
`ℚ` and every complex root of its minimal polynomial has absolute value `q ^ (w / 2)`. -/
theorem isWeilNumber_iff {q : ℕ} {w : ℝ} {α : K} :
    IsWeilNumber q w α ↔ IsIntegral ℚ α ∧
      ∀ y ∈ ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots, ‖y‖ = (q : ℝ) ^ (w / 2) :=
  and_congr_right fun hα ↦
    forall_algHom_adjoin_iff_forall_mem_roots hα fun y ↦ ‖y‖ = (q : ℝ) ^ (w / 2)

variable {K' : Type*} [Field K'] [Algebra ℚ K']

/-- Blueprint `def-weil-numbers`, `lem-embedding-extension`: the Weil-number condition is
invariant under `ℚ`-algebra embeddings, since these preserve minimal polynomials. -/
theorem isWeilNumber_algHom_apply_iff {q : ℕ} {w : ℝ} (f : K →ₐ[ℚ] K') {α : K} :
    IsWeilNumber q w (f α) ↔ IsWeilNumber q w α := by
  rw [isWeilNumber_iff, isWeilNumber_iff, isIntegral_algHom_iff f f.toRingHom.injective,
    minpoly.algHom_eq f f.toRingHom.injective]

/-- Blueprint `lem-embedding-extension`: the Weil-number condition is stable under
`ℚ`-algebra isomorphisms, in particular under `Gal(ℚ̄/ℚ)`. -/
theorem isWeilNumber_algEquiv_apply_iff {q : ℕ} {w : ℝ} (σ : K ≃ₐ[ℚ] K') {α : K} :
    IsWeilNumber q w (σ α) ↔ IsWeilNumber q w α :=
  isWeilNumber_algHom_apply_iff (σ : K →ₐ[ℚ] K')

/-- If `α β = 1`, a property of the images of `α` under the embeddings of `ℚ(α)` transfers to
the inverses of the images of `β` under the embeddings of `ℚ(β)`. -/
private theorem forall_algHom_adjoin_inv {α β : K} (hαβ : α * β = 1) {P : ℂ → Prop}
    (h : ∀ τ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, P (τ (AdjoinSimple.gen ℚ α))) (τ : ℚ⟮β⟯ →ₐ[ℚ] ℂ) :
    P (τ (AdjoinSimple.gen ℚ β))⁻¹ := by
  have hα : α = β⁻¹ := eq_inv_of_mul_eq_one_left hαβ
  have hmem : α ∈ ℚ⟮β⟯ := hα ▸ ℚ⟮β⟯.inv_mem (mem_adjoin_simple_self ℚ β)
  have hle : ℚ⟮α⟯ ≤ ℚ⟮β⟯ := adjoin_simple_le_iff.2 hmem
  have hgen : (⟨α, hmem⟩ : ℚ⟮β⟯) = (AdjoinSimple.gen ℚ β)⁻¹ :=
    Subtype.ext (hα.trans (by rw [IntermediateField.coe_inv, AdjoinSimple.coe_gen]))
  have := h (τ.comp (inclusion hle))
  rwa [AlgHom.comp_apply, show inclusion hle (AdjoinSimple.gen ℚ α) = ⟨α, hmem⟩ from rfl, hgen,
    map_inv₀] at this

end Defs

/-- The universal purity of `Weights.lean` versus Weil numbers (blueprint `def-weil-numbers`): a
nonzero complex number `z` is universally pure of weight `w` (its conjugates have absolute value
`q ^ (-w / 2)`) iff `z⁻¹` is a `q`-Weil number of weight `w`. -/
theorem isUniversallyPureOfWeight_iff_isWeilNumber_inv {q w : ℕ} {z : ℂ} (hz : z ≠ 0) :
    IsUniversallyPureOfWeight q w z ↔ IsWeilNumber q w z⁻¹ := by
  have hnorm : ∀ y : ℂ, ‖y‖ = (q : ℝ) ^ (-(w : ℝ) / 2) ↔ ‖y⁻¹‖ = (q : ℝ) ^ ((w : ℝ) / 2) := by
    intro y
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg q), norm_inv, inv_eq_iff_eq_inv]
  unfold _root_.IsUniversallyPureOfWeight IsWeilNumber
  rw [isAlgebraic_iff_isIntegral]
  refine ⟨fun ⟨hint, h⟩ ↦ ⟨hint.inv, ?_⟩, fun ⟨hint, h⟩ ↦ ⟨?_, ?_⟩⟩
  · rw [← forall_algHom_adjoin_iff_forall_mem_roots hint] at h
    intro τ
    have := forall_algHom_adjoin_inv (mul_inv_cancel₀ hz) (P := fun y ↦ ‖y⁻¹‖ = _)
      (fun τ ↦ (hnorm _).1 (h τ)) τ
    rwa [inv_inv] at this
  · simpa using hint.inv
  · have hint' : IsIntegral ℚ z := by simpa using hint.inv
    rw [← forall_algHom_adjoin_iff_forall_mem_roots hint']
    intro τ
    rw [hnorm]
    exact forall_algHom_adjoin_inv (inv_mul_cancel₀ hz) (P := fun y ↦ ‖y‖ = _) h τ

/-- The intrinsic-weight clause of blueprint `lem-embedding-extension`: if `α ∈ ℚ̄_p` is
algebraic over `ℚ` and `‖ι α‖ = q ^ (w / 2)` for every abstract field isomorphism
`ι : ℚ̄_p ≃ ℂ`, then `α` is a `q`-Weil number of weight `w`: every conjugate of `α` is the image
of `α` under such an isomorphism (`PadicAlgCl.exists_ringEquiv_complex_apply_eq`). -/
theorem PadicAlgCl.isWeilNumber_of_forall_ringEquiv (p : ℕ) [Fact p.Prime] {q : ℕ} {w : ℝ}
    {α : PadicAlgCl p} (hα : IsIntegral ℚ α)
    (h : ∀ ι : PadicAlgCl p ≃+* ℂ, ‖ι α‖ = (q : ℝ) ^ (w / 2)) : IsWeilNumber q w α := by
  refine isWeilNumber_iff.2 ⟨hα, fun y hy ↦ ?_⟩
  obtain ⟨ι, rfl⟩ := PadicAlgCl.exists_ringEquiv_complex_apply_eq p hα (mem_aroots.1 hy).2
  exact h ι
