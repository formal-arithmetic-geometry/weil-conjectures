/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Engel

/-!
# Engel's theorem for Lie algebras of nilpotent endomorphisms

This file records the classical matrix form of Engel's theorem: a Lie algebra of nilpotent
endomorphisms of a nonzero finite-dimensional vector space has a common null vector and is
nilpotent. It is a direct consequence of Mathlib's `LieModule.isNilpotent_iff_forall'`.

## Main declarations

* `LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent`: Engel's matrix lemma.

## Blueprint

`LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent` implements `lem-wf-engel-matrix`.
-/

@[expose] public section

open LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- **Engel's matrix lemma.** Let `A` be a Lie algebra of endomorphisms of a nonzero
finite-dimensional vector space `M`, all of whose elements are nilpotent. Then some nonzero vector
of `M` is killed by every element of `A`, and `A` is a nilpotent Lie algebra.
(blueprint: `lem-wf-engel-matrix`) -/
theorem exists_forall_apply_eq_zero_and_isNilpotent [Nontrivial M]
    (A : LieSubalgebra k (Module.End k M)) (hA : ∀ X ∈ A, IsNilpotent X) :
    (∃ v : M, v ≠ 0 ∧ ∀ X ∈ A, X v = 0) ∧ LieRing.IsNilpotent A := by
  have hM : LieModule.IsNilpotent A M :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr fun X ↦ hA X X.2
  refine ⟨?_, (LieAlgebra.isNilpotent_iff_forall (R := k)).mpr fun X ↦
    LieAlgebra.isNilpotent_ad_of_isNilpotent (hA X X.2)⟩
  have := nontrivial_max_triv_of_isNilpotent k A M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : maxTrivSubmodule k A M)
  refine ⟨v, fun h ↦ hv0 (Subtype.ext h), fun X hX ↦ ?_⟩
  exact (mem_maxTrivSubmodule k A M v).mp hv ⟨X, hX⟩

end LieSubalgebra
