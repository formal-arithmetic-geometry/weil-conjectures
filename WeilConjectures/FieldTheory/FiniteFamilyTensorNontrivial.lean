/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Nontriviality of finite tensor products of field extensions

Source: literature/stacks-project/limits.tex, discussion preceding Tag 0CNI,
lines 145–157; the auxiliary nontriviality argument over a field is agent-supplied.
(blueprint: lem-trf-finite-family-tensor-nontrivial).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Field

/-- A finite tensor product of extensions of `k` is nontrivial. For an empty index
set, its canonical structure map from `k` is bijective, identifying the empty
coproduct with `k` as a `k`-algebra.

Source: literature/stacks-project/limits.tex, discussion preceding Tag 0CNI,
lines 145–157, for finite tensor stages. The argument over `k` is agent-supplied.
(blueprint: lem-trf-finite-family-tensor-nontrivial).

Proof: Induct on the cardinality of `S`. For the empty set the tensor product is
canonically `k`: its elements are scalar multiples of the empty pure tensor, and
sending that pure tensor to `1` gives the inverse to the structure map. This also
proves nontriviality since `k` is a field. In the induction step remove one index
`s`. The tensor product of the remaining factors is nontrivial by induction and
is a nonzero vector space over `k`, as is `L s`. Their binary tensor product is
nontrivial by [lem-pur-field-vector-space-tensor-nontrivial], using vector-space
freeness and `Module.FaithfullyFlat.lTensor_nontrivial`. The binary coproduct
universal property [lem-weil-pbc-algebra-tensor-pushout-universal-property]
identifies this binary tensor product with the tensor product of the full finite
family: maps out of either object correspond to the same family of algebra maps.
The two universal maps are inverse since they agree with the identity on every
factor. Transport nontriviality across this algebra isomorphism. This includes
the singleton case, when the remaining tensor product is `k`. -/
theorem finite_tensorProduct_nontrivial
    (k : Type u) [Field k] (S : Type w) [Finite S]
    (L : S → Type v) [∀ s : S, Field (L s)] [∀ s : S, Algebra k (L s)] :
    Nontrivial (⨂[k] s : S, L s) ∧
      (IsEmpty S → Function.Bijective (algebraMap k (⨂[k] s : S, L s))) := by
  sorry

end Field
