/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# A degree-p final step in a finite purely inseparable extension

Source: Stacks Project, More on Algebra, Tag 07PR, proof, induction paragraph;
Fields, Tags 09HI and 09G9.
(blueprint: lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate)
-/

universe u v

namespace IsPurelyInseparable

/-- A nontrivial finite purely inseparable extension in positive characteristic has a
degree-`p` final step obtained by adjoining a `p`th root.
Source: Stacks Project, Tag 07PR, proof, induction paragraph, with Tags 09HI and 09G9.
(blueprint: lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate)

Proof: use the pth-root tower of Tag 09HI
(`lem-weil-pbc-purely-inseparable-pth-root-tower`). Its length is positive because a
length-zero tower has degree one. Take M to be its penultimate field and z its last
generator. The last step gives L = M(z), z^p in M, and [L:M] = p. The field M is a
finite-dimensional K-subspace of L. Every element of M has a p-power in K, since it is
an element of L; thus M/K is finite purely inseparable
(`def-weil-pbc-finite-purely-inseparable-extension`). Degree multiplicativity, Tag 09G9
(`lem-weil-pbc-field-degree-multiplicativity`), gives [L:K] = p[M:K]. Since p >= 2
and [M:K] >= 1, this is strictly greater than [M:K]. -/
theorem exists_degree_p_intermediate (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [IsPurelyInseparable K L]
    (p : ℕ) [CharP K p] (hp : 0 < p) (hdeg : 1 < Module.finrank K L) :
    ∃ (M : IntermediateField K L) (z : L),
      Module.Finite K M ∧ IsPurelyInseparable K M ∧
      Module.finrank K M < Module.finrank K L ∧
      IntermediateField.adjoin M ({z} : Set L) = ⊤ ∧
      (∃ f : M, z ^ p = (f : L)) ∧ Module.finrank M L = p := by
  sorry

end IsPurelyInseparable
