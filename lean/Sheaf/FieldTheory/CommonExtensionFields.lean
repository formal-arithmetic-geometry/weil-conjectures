/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs

/-!
# A common extension of two fields

Source: Stacks Project, Fields, Tag 0H7K, `fields-lemma-common-extension-field`
(blueprint: lem-weil-common-extension-fields).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Field

/-- Two extensions `E/k` and `F/k` admit embeddings into a common extension `M/k`.
Source: Stacks Project, Fields, Tag 0H7K (blueprint: lem-weil-common-extension-fields).

Proof: Form `T = E ⊗[k] F`. Its two canonical factor maps are injective by
[lem-weil-common-extension-fields-tensor-inclusions]. Since the factors are fields,
[lem-weil-common-extension-fields-tensor-nontrivial] shows that `T` is nontrivial.
Choose a maximal ideal `I` by [lem-weil-common-extension-fields-maximal-ideal].
The quotient `M = T/I` is a field by [lem-weil-common-extension-fields-quotient-field].
Compose the factor maps with the quotient map to obtain `k`-algebra homomorphisms
`E → M` and `F → M`. Their kernels are proper ideals of fields, since they preserve
one and `M` is nontrivial. Thus both kernels vanish and both maps are injective. -/
theorem exists_common_extension (k : Type u) (E : Type v) (F : Type w)
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra k M)
      (i : E →ₐ[k] M) (j : F →ₐ[k] M), Function.Injective i ∧ Function.Injective j := by
  sorry

end Field
