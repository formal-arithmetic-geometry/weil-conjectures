/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis
import WeilConjectures.FieldTheory.PBasisExtension

/-! # The differentials of a p-independent family are linearly independent

Source: Stacks Project, More on Algebra, Definition Tag 07P1 and Lemma Tag 07P2.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace FieldTheory

/-- The differentials of a p-independent family are linearly independent.
Source: Stacks Project, More on Algebra, Tags 07P1 and 07P2, implication (1) implies (2). -/
theorem pIndependent_differentials_linearIndependent
    (p : ℕ) [Fact p.Prime] (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] [CharP k p] [CharP K p]
    {I : Type w} (x : I → K)
    (h : LinearIndependent (IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p)))
      (fun E : {E : I →₀ ℕ // ∀ i : I, E i < p} ↦ E.val.prod (fun i e ↦ x i ^ e))) :
    LinearIndependent K (fun i : I => KaehlerDifferential.D k K (x i)) := by
  obtain ⟨J, y, bmon, hbmon⟩ := exists_pBasis_extension p x h
  obtain ⟨bd, hbd⟩ := KaehlerDifferential.exists_basis_differentials_of_pBasis
    p (Sum.elim x y) ⟨bmon, hbmon⟩
  have hli : LinearIndependent K
      (fun l : I ⊕ J ↦ KaehlerDifferential.D k K (Sum.elim x y l)) := by
    simpa only [← hbd] using bd.linearIndependent
  simpa only [Function.comp_def, Sum.elim_inl] using
    hli.comp Sum.inl Sum.inl_injective

end FieldTheory
