/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs

import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# A common extension of two fields

We show that two field extensions of `k` embed into a common extension
(`Field.exists_common_extension`), namely a quotient of `E ⊗[k] F` by a maximal ideal.

## References

* [Stacks Project, Tag 0H7K](https://stacks.math.columbia.edu/tag/0H7K)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Field

/-- Two extensions `E/k` and `F/k` admit `k`-embeddings into a common extension `M/k`. -/
theorem exists_common_extension (k : Type u) (E : Type v) (F : Type w)
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra k M)
      (i : E →ₐ[k] M) (j : F →ₐ[k] M), Function.Injective i ∧ Function.Injective j := by
  classical
  let : Nontrivial (TensorProduct k E F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k E F
      (algebraMap k E).injective (algebraMap k F).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (α := TensorProduct k E F)
  let : I.IsMaximal := hI
  let : Field (TensorProduct k E F ⧸ I) := Ideal.Quotient.field I
  let i : E →ₐ[k] (TensorProduct k E F ⧸ I) :=
    (Ideal.Quotient.mkₐ k I).comp Algebra.TensorProduct.includeLeft
  let j : F →ₐ[k] (TensorProduct k E F ⧸ I) :=
    (Ideal.Quotient.mkₐ k I).comp Algebra.TensorProduct.includeRight
  exact ⟨TensorProduct k E F ⧸ I, inferInstance, inferInstance, i, j,
    i.injective, j.injective⟩

end Field
