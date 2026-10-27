/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp

/-! # Algebraic extension gives torsion quotient of value groups

Source: literature/stacks-project/more-algebra.tex, Tag 0ASJ, lemma-etale-extension-valuation-ring,
first proof paragraph (blueprint: lem-trf-valuation-value-group-torsion).
-/

@[expose] public section

universe u v

namespace WeilConjectures

private theorem equal_value_terms {F Γ : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (s : Finset ℕ) (hs : s.Nonempty) (d : ℕ → F)
    (hd : ∀ i ∈ s, d i ≠ 0) (hz : ∑ i ∈ s, d i = 0) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ v (d i) = v (d j) := by
  classical
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i ↦ v (d i)) hs
  have hsecond : ∃ i ∈ s, i ≠ j ∧ v (d i) = v (d j) := by
    by_contra h
    have hlt : ∀ i ∈ s \ {j}, v (d i) < v (d j) := by
      intro i hi
      obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
      have hij' : i ≠ j := by simpa using hij
      exact lt_of_le_of_ne (hmax i his) (fun he ↦ h ⟨i, his, hij', he⟩)
    have he := v.map_sum_eq_of_lt hj hlt
    rw [hz, map_zero] at he
    exact ((v.ne_zero_iff).mpr (hd j hj)) he.symm
  obtain ⟨i, hi, hij, he⟩ := hsecond
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i, hi, j, hj, hij, he⟩
  · exact ⟨j, hj, i, hi, hji, he.symm⟩

/-- Source: Stacks Tag 0ASJ, lemma-etale-extension-valuation-ring, first proof paragraph;
(blueprint: lem-trf-valuation-value-group-torsion).

For an algebraic extension of fields equipped with a valuation subring, every nonzero
extension element has a positive power equal to a nonzero base element times a unit of
the valuation subring.  The final quotient statement in the source is represented by
this elementwise power-times-unit form.

Proof: choose a nonzero polynomial relation for `x`, normalize it at a term dividing all
other terms, and use closure of the nonunits under addition to force a unit ratio.  The
unit ratio gives the displayed equality, with the two possible orders of the exponents
handled by inversion.  This is the direct polynomial argument recorded in the DAG proof.
-/
theorem algebraic_extension_value_group_torsion
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] (V : Subring E)
    (hV : ∀ z : E, z ≠ 0 → z ∈ V ∨ z⁻¹ ∈ V) :
    ∀ x : E, x ≠ 0 →
      ∃ n : ℕ, 0 < n ∧ ∃ a : K, a ≠ 0 ∧ ∃ u : E,
        u ≠ 0 ∧ u ∈ V ∧ u⁻¹ ∈ V ∧ x ^ n = algebraMap K E a * u := by
  classical
  intro x hx
  let W : ValuationSubring E :=
    { V with
      mem_or_inv_mem' := fun z ↦ by
        by_cases hz : z = 0
        · exact Or.inl (hz ▸ V.zero_mem)
        · exact hV z hz }
  obtain ⟨p, hp, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  let d : ℕ → E := fun i ↦ algebraMap K E (p.coeff i) * x ^ i
  have hd : ∀ i ∈ p.support, d i ≠ 0 := by
    intro i hi
    exact mul_ne_zero ((map_ne_zero (algebraMap K E)).mpr
      (Polynomial.mem_support_iff.mp hi)) (pow_ne_zero i hx)
  have hz : ∑ i ∈ p.support, d i = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, d] using hpx
  obtain ⟨i, hi, j, hj, hij, he⟩ :=
    equal_value_terms W.valuation p.support (Polynomial.support_nonempty.mpr hp) d hd hz
  obtain ⟨u, hu⟩ := (W.valuation_eq_iff (d j) (d i)).mp he.symm
  have hci : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hcj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hcj' : algebraMap K E (p.coeff j) ≠ 0 :=
    (map_ne_zero (algebraMap K E)).mpr hcj
  let uE : Eˣ := u.map W.toSubring.subtype.toMonoidHom
  have hu0 : (u : E) ≠ 0 := uE.ne_zero
  have huinv : (u : E)⁻¹ ∈ V := by
    have hinv : ((u⁻¹ : Wˣ) : E) = (u : E)⁻¹ := by
      change (↑(uE⁻¹) : E) = (↑uE : E)⁻¹
      simp
    rw [← hinv]
    exact (u⁻¹).val.property
  refine ⟨j - i, Nat.sub_pos_of_lt hij, p.coeff i / p.coeff j,
    div_ne_zero hci hcj, (u : E), hu0, u.val.property, huinv, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hcj' (pow_ne_zero i hx))
  calc
    (algebraMap K E (p.coeff j) * x ^ i) * x ^ (j - i) =
        algebraMap K E (p.coeff j) * x ^ j := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hij.le]
    _ = (u : E) * (algebraMap K E (p.coeff i) * x ^ i) := hu.symm
    _ = (algebraMap K E (p.coeff j) * x ^ i) *
        (algebraMap K E (p.coeff i / p.coeff j) * (u : E)) := by
      rw [map_div₀]
      field_simp

end WeilConjectures
