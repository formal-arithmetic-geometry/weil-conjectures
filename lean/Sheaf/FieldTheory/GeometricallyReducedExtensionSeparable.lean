/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Sheaf.FieldTheory.SeparableExtension

/-!
# Geometrically reduced field extensions are separable in positive characteristic

Source: Stacks Project, Algebra, Lemma Tag 030W, implication (4) => (1),
with Definition Tag 030S
(blueprint: lem-weil-pbc-geometrically-reduced-extension-separable).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- In prime characteristic, reducedness of the tensor product with every field extension
implies separability in the sense that every finitely generated intermediate field is
separably generated. Source: Stacks Project, Algebra, Lemma Tag 030W, (4) => (1),
with Definition Tag 030S
(blueprint: lem-weil-pbc-geometrically-reduced-extension-separable).

Proof:
1. In an algebraic closure of `k`, form the subfield of elements whose `p`-th powers lie
   in `k`. Frobenius is injective and a ring homomorphism, so this subfield contains `k`
   and has a unique `p`-th root of every element of `k`
   (`def-weil-algebraic-closure`, `def-weil-ring-frobenius`, `def-pc-field-extension`).
2. Apply the hypothesis to this extension `L = k^{1/p}`. The ring `K ⊗[k] L` is reduced
   and has characteristic `p` (`def-weil-vector-space-scalar-extension`).
3. For a finite relation with coefficients `cᵢ` in `k`, put `x = ∑ bᵢ ⊗ cᵢ^{1/p}`.
   Frobenius and tensor balancing give `x^p = (∑ cᵢ bᵢ^p) ⊗ 1`
   (`def-weil-ring-frobenius`, `def-weil-vector-space-scalar-extension`).
4. If the `bᵢ` are linearly independent and the latter sum vanishes, reducedness gives
   `x = 0`. Extend the `bᵢ` to a basis and extend scalars; their tensors remain independent.
   Thus every `cᵢ^{1/p}`, and hence every `cᵢ`, is zero
   (`lem-weil-pbc-vector-space-basis-through-vector`, `def-weil-vector-space-scalar-extension`).
5. This independence of `p`-th powers passes to every finitely generated intermediate
   field. Apply `lem-weil-pbc-p-power-independence-separably-generated` to obtain a
   separating transcendence basis there. This is exactly clause (2) of
   `def-weil-pbc-separable-field-extension`.
-/
theorem isSeparableExtension_of_forall_isReduced_tensorProduct
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hred : ∀ (L : Type (max u v)) [Field L] [Algebra k L],
      IsReduced (K ⊗[k] L)) :
    Algebra.IsSeparableExtension k K := by
  sorry

end Algebra
