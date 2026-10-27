/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Analysis.Normed.Module.Basic
import Sheaf.NumberTheory.Padics.RationalAlgebraicGenerator
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # A countable closed finite-field cover of a p-adic algebraic closure

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3;
`WeilConjectures/NumberTheory/Padics/Extension.lean`, rational-algebraic generators
and closedness of finite intermediate fields
(blueprint: lem-sfb-algcl-countable-closed-finite-cover).

The normed algebra structure expresses that the norm on the algebraic closure
extends the p-adic norm. No completeness of the algebraic closure is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

/-- A p-adic algebraic closure is covered by an increasing sequence of closed finite
intermediate fields, all containing a prescribed finite intermediate field.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3;
the rational-algebraic generator theorem in the project's p-adic `Extension` module
(blueprint: lem-sfb-algcl-countable-closed-finite-cover).

Proof:
1. By lem-sfb-algebraic-elements-countable (`Algebraic.countable`), the set of elements
   of the closure algebraic over the countable field Q is countable. It contains zero,
   so enumerate it as b_n, repeating zero at unused indices of an injection into N.
2. Set K_j = Q_l(b_0,...,b_j). Every generator is algebraic over Q_l because the
   ambient field is an algebraic closure. Thus K_j is finite-dimensional by
   lem-weil-pbc-algebraic-generators-finite-extension. Inclusion of the generating
   sets gives K_j contained in K_(j+1).
3. Set F_j = E K_j, the compositum in the closure. The finite-compositum clause of
   def-weil-finite-subextension-directed-set gives finiteness over Q_l. The definition
   of compositum gives E contained in F_j, and monotonicity follows from that of K_j.
4. Each F_j is a finite-dimensional subspace of the Hausdorff normed Q_l-vector space
   given by the closure. The base field is complete and nontrivially normed
   (def-weil-l-adic-numbers), so lem-sfb-finite-dimensional-subspace-closed applies.
5. Given x in the closure, lem-sfb-padic-rational-algebraic-generator gives b algebraic
   over Q such that x belongs to Q_l(b). Write b = b_n using step 1. Then x belongs
   to Q_l(b_n), hence to K_n and F_n. This proves exhaustion; the reverse inclusion
   is automatic because the intermediate fields are subsets of the closure.
-/
theorem exists_monotone_closed_finiteIntermediateField_cover
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : IntermediateField (Padic l) Ω) [FiniteDimensional (Padic l) E] :
    ∃ F : ℕ → IntermediateField (Padic l) Ω,
      Monotone F ∧
      (∀ j : ℕ, E ≤ F j ∧ FiniteDimensional (Padic l) (F j) ∧
        IsClosed (F j : Set Ω)) ∧
      (⋃ j : ℕ, (F j : Set Ω)) = Set.univ := by
  classical
  let : Algebra ℚ Ω :=
    ((algebraMap (Padic l) Ω).comp (algebraMap ℚ (Padic l))).toAlgebra
  obtain ⟨b, hb⟩ := (Algebraic.countable ℚ Ω).exists_eq_range
    ⟨0, isAlgebraic_zero⟩
  let S (j : ℕ) : Finset Ω := (Finset.range (j + 1)).image b
  let K (j : ℕ) : IntermediateField (Padic l) Ω :=
    IntermediateField.adjoin (Padic l) (S j : Set Ω)
  have hK (j : ℕ) : FiniteDimensional (Padic l) (K j) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let F (j : ℕ) : IntermediateField (Padic l) Ω := E ⊔ K j
  have hF (j : ℕ) : FiniteDimensional (Padic l) (F j) := by
    have := hK j
    exact IntermediateField.finiteDimensional_sup E (K j)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i j hij
    apply sup_le_sup_left
    apply IntermediateField.adjoin.mono
    exact_mod_cast Finset.image_mono b
      (Finset.range_mono (Nat.add_le_add_right hij 1))
  · intro j
    have := hF j
    exact ⟨le_sup_left, inferInstance,
      Submodule.closed_of_finiteDimensional (F j).toSubalgebra.toSubmodule⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hx⟩ :=
      exists_isAlgebraic_rat_mem_adjoin_simple_of_isAlgClosure l Ω x
    have ha : a ∈ Set.range b := by
      rw [← hb]
      exact ha
    obtain ⟨n, rfl⟩ := ha
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    apply (show K n ≤ F n from le_sup_right)
    have hbn : b n ∈ K n := IntermediateField.subset_adjoin (Padic l) (S n : Set Ω)
      (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩)
    exact (IntermediateField.adjoin_simple_le_iff.mpr hbn) hx

end Padic
