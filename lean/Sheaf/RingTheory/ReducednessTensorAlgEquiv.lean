/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reducedness under an equivalence of scalar algebras

Source: Stacks Project, Algebra, Tags 00CX and 05G3, with the reduced-ring convention
of Tag 00B3 (blueprint: lem-trf-reducedness-tensor-alg-equiv).
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Algebra

/-- Reducedness of a tensor product is unchanged by a bijective algebra homomorphism
between the scalar fields. Source: Stacks Project, Algebra, Tags 00CX, 05G3 and 00B3
(blueprint: lem-trf-reducedness-tensor-alg-equiv).

Proof plan:
1. The inverse function `d` of `e` preserves addition, multiplication, zero, one and
   the structure map: apply the injective map `e` to each required equality. Thus `d`
   is a `k`-algebra homomorphism with `d ∘ e = id` and `e ∘ d = id`, using
   `def-weil-pbc-algebra-hom-quotient`.
2. The algebra tensor universal property
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`) constructs algebra maps
   `F : A ⊗[k] L →ₐ[k] A ⊗[k] M` and `G` in the reverse direction, sending
   `a ⊗ l` to `a ⊗ e l` and `a ⊗ m` to `a ⊗ d m`, respectively.
3. Their composites are the identity on pure tensors, hence on the entire tensor
   products, since pure tensors generate (`def-weil-pbc-module-tensor-product`).
4. If `A ⊗[k] L` is reduced and `y` in `A ⊗[k] M` is nilpotent, then `G y` is
   nilpotent, so `G y = 0` and `y = F (G y) = 0`.
5. Conversely, reducedness of `A ⊗[k] M` implies that a nilpotent `x` in
   `A ⊗[k] L` has `F x = 0`, whence `x = G (F x) = 0`. -/
theorem isReduced_tensorProduct_iff_of_bijective
    (k : Type u) (A : Type v) (L : Type w) (M : Type z)
    [Field k] [CommRing A] [Algebra k A] [Field L] [Algebra k L]
    [Field M] [Algebra k M] (e : L →ₐ[k] M) (he : Function.Bijective e) :
    IsReduced (A ⊗[k] L) ↔ IsReduced (A ⊗[k] M) := by
  sorry

end Algebra
