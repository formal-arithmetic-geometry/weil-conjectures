/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# `ℚ̄_p` is abstractly isomorphic to `ℂ`

The field `ℚ_[p]` has the cardinality of the continuum: it is a complete nontrivially normed
field, so it has at least continuum many elements, and it is a quotient of the Cauchy sequences
of rationals, so it has at most that many. Its algebraic closure `PadicAlgCl p` is then an
algebraically closed field of characteristic zero and of cardinality `𝔠`, hence isomorphic to `ℂ`
by the classification of uncountable algebraically closed fields.

In particular field embeddings `ι : ℚ̄_ℓ →+* ℂ`, used to compare `ℓ`-adic eigenvalues with
complex absolute values, exist.

## Main statements

- `Padic.mk_eq_continuum`: `#ℚ_[p] = 𝔠`.
- `PadicAlgCl.mk_eq_continuum`: `#ℚ̄_p = 𝔠`.
- `PadicAlgCl.nonempty_ringEquiv_complex`: `ℚ̄_p ≃+* ℂ`.
-/

@[expose] public section

open Cardinal

variable (p : ℕ) [Fact p.Prime]

/-- The field `ℚ_[p]` has at most continuum many elements: it is a quotient of the Cauchy
sequences of rationals. -/
theorem Padic.mk_le_continuum : #ℚ_[p] ≤ 𝔠 := by
  have h₁ : #ℚ_[p] ≤ #(CauSeq ℚ (padicNorm p)) :=
    Cardinal.mk_le_of_surjective (f := fun f : CauSeq ℚ (padicNorm p) ↦ (Padic.mk f : ℚ_[p]))
      fun x ↦ (Quotient.exists_rep x).imp fun _ hf ↦ hf
  have h₂ : #(CauSeq ℚ (padicNorm p)) ≤ #(ℕ → ℚ) :=
    Cardinal.mk_le_of_injective (f := fun f : CauSeq ℚ (padicNorm p) ↦ (f : ℕ → ℚ))
      fun _ _ h ↦ Subtype.ext h
  have h₃ : #(ℕ → ℚ) = 𝔠 := by
    rw [← Cardinal.power_def, Cardinal.mkRat, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0]
  exact h₁.trans (h₂.trans h₃.le)

/-- The field `ℚ_[p]` has the cardinality of the continuum. -/
theorem Padic.mk_eq_continuum : #ℚ_[p] = 𝔠 :=
  le_antisymm (Padic.mk_le_continuum p) (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])

/-- The algebraic closure `ℚ̄_p` of `ℚ_[p]` has the cardinality of the continuum. -/
theorem PadicAlgCl.mk_eq_continuum : #(PadicAlgCl p) = 𝔠 := by
  refine le_antisymm ?_ ?_
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans ?_
    exact max_le (Padic.mk_le_continuum p) Cardinal.aleph0_le_continuum
  · rw [← Padic.mk_eq_continuum p]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

/-- The algebraic closure `ℚ̄_p` of `ℚ_[p]` is isomorphic to `ℂ` as a field: both are
algebraically closed of characteristic zero and of cardinality `𝔠`. -/
theorem PadicAlgCl.nonempty_ringEquiv_complex : Nonempty (PadicAlgCl p ≃+* ℂ) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [PadicAlgCl.mk_eq_continuum]
    exact Cardinal.aleph0_lt_continuum
  · rw [← Cardinal.eq, PadicAlgCl.mk_eq_continuum, Cardinal.mk_complex]

/-- There is a field embedding `ℚ̄_p →+* ℂ`. -/
theorem PadicAlgCl.nonempty_ringHom_complex : Nonempty (PadicAlgCl p →+* ℂ) :=
  (PadicAlgCl.nonempty_ringEquiv_complex p).map RingEquiv.toRingHom
