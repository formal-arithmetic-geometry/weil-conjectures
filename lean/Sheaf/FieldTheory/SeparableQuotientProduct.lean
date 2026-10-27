/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.PolynomialDistinctLinearCRT

/-!
# Evaluation decomposition of a separable polynomial quotient

Source: Stacks Project, Algebra, Tag 00U3 (lemma-etale-over-field), separable polynomial
case and Chinese remainder factorization
(blueprint: lem-pc-separable-polynomial-alg-closed-quotient-product).
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Source: Stacks Project, Algebra, Tag 00U3 (lemma-etale-over-field), separable polynomial
case and Chinese remainder factorization
(blueprint: lem-pc-separable-polynomial-alg-closed-quotient-product).

Proof outline:
1. Apply `lem-pc-separable-polynomial-distinct-roots-alg-closed` to factor the mapped monic
polynomial into distinct linear factors and count its roots: there are exactly `n`.
2. Apply `lem-pc-polynomial-quotient-distinct-linear-crt` to these factors. The Chinese
remainder isomorphism sends the class of each polynomial `q` to its values at the roots.
3. Index the factors by the root set itself. The count from step 1 and the evaluation formula
from step 2 give both assertions. This also includes the empty product when `n = 0`. -/
theorem exists_eval_quotient_algEquiv_pi_of_separable
    {F : Type u} [Field F] {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (P : F[X]) (n : ℕ) (hmonic : P.Monic) (hsep : P.Separable) (hdegree : P.natDegree = n) :
    Nat.card {ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0} = n ∧
      ∃ e : (Ω[X] ⧸ Ideal.span {P.map (algebraMap F Ω)}) ≃ₐ[Ω]
          ({ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0} → Ω),
        ∀ (q : Ω[X]) (ρ : {ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0}),
          e (Ideal.Quotient.mk (Ideal.span {P.map (algebraMap F Ω)}) q) ρ = q.eval ρ.val := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_of_splits (algebraMap F Ω) hsep
    (IsAlgClosed.splits _)
  have hP : P.map (algebraMap F Ω) = ∏ a ∈ s, (X - C a) := by
    simpa [hmonic.leadingCoeff] using hs
  have hroots (a : Ω) : a ∈ s ↔ (P.map (algebraMap F Ω)).eval a = 0 := by
    rw [hP, eval_prod]
    simp [Finset.prod_eq_zero_iff, sub_eq_zero]
  let er : s ≃ {a : Ω // (P.map (algebraMap F Ω)).eval a = 0} :=
    { toFun := fun a ↦ ⟨a.val, (hroots a.val).1 a.property⟩
      invFun := fun a ↦ ⟨a.val, (hroots a.val).2 a.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let ef := (Fintype.equivFin s).symm
  let ρ : Fin (Fintype.card s) → Ω := fun i ↦ (ef i).val
  have hρ : Function.Injective ρ := Subtype.val_injective.comp ef.injective
  have hfactor : P.map (algebraMap F Ω) =
      ∏ i : Fin (Fintype.card s), (X - C (ρ i)) := by
    rw [hP, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv ef _ _ (fun _ ↦ rfl)).symm
  have hcard : Fintype.card s = n := by
    have hd := congrArg natDegree hfactor
    simpa [hdegree] using hd.symm
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr er, Nat.card_eq_fintype_card, hcard]
  obtain ⟨e, he⟩ := quotient_prod_X_sub_C_algEquiv_pi _ ρ hρ
  let eqQ := Ideal.quotientEquivAlgOfEq Ω (congrArg (fun p ↦ Ideal.span {p}) hfactor)
  let eidx := AlgEquiv.piCongrLeft' Ω (fun _ : Fin (Fintype.card s) ↦ Ω) (ef.trans er)
  refine ⟨(eqQ.trans e).trans eidx, ?_⟩
  intro q a
  change e (eqQ (Ideal.Quotient.mk _ q)) ((ef.trans er).symm a) = q.eval a.val
  rw [Ideal.quotientEquivAlgOfEq_mk, he]
  congr 1
  exact congrArg Subtype.val ((ef.trans er).apply_symm_apply a)

end Polynomial
