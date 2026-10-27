/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Reducedness after extension to two perfect scalar fields

Source: Stacks Project, Algebra, Tag 00I4 (`lemma-perfect-reduced`), and Fields,
Tag 0H7K (`lemma-common-extension-field`).
(blueprint: lem-trf-perfect-scalars-reducedness-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace Algebra

/-- Reducedness after scalar extension is independent of the chosen perfect extension field.
The algebra `A` may be nonreduced, infinitely generated, or the zero ring, and the base field
`k` need not be perfect. No embedding between `E` and `F` is required.

Source: Stacks Project, Algebra, Tag 00I4 (`lemma-perfect-reduced`), combined with Fields,
Tag 0H7K (`lemma-common-extension-field`).
(blueprint: lem-trf-perfect-scalars-reducedness-comparison)

Proof:
1. By `lem-weil-common-extension-fields` (`Field.exists_common_extension`), choose a common
   extension `M/k` with compatible embeddings `i_E : E → M` and `i_F : F → M`.
   For `D = E, F`, give `M` its `D`-algebra structure through `i_D`. Put
   `B_D = A ⊗[k] D` and `T = A ⊗[k] M`.
2. Apply `lem-weil-pbc-tensor-cancel-base-change` with `R = k`, `S = D`, its algebra `A = M`
   and its algebra `B = A`. Composing `Algebra.TensorProduct.cancelBaseChange` with tensor
   flips gives a ring isomorphism `B_D ⊗[D] M ≃+* T` sending `(a ⊗ d) ⊗ m` to
   `a ⊗ (i_D(d) * m)`, with inverse `a ⊗ m ↦ (a ⊗ 1) ⊗ m`.
   The flips come from `def-weil-pbc-module-tensor-product`; they preserve multiplication
   by `lem-weil-pbc-algebra-tensor-pushout-universal-property`, whose pure-tensor product
   formula is `Algebra.TensorProduct.tmul_mul_tmul`.
3. By `lem-sfb-field-extension-tensor-injective`, the map `B_D → B_D ⊗[D] M`,
   `b ↦ b ⊗ 1`, is injective (`Algebra.TensorProduct.includeLeft_injective`). Composing
   with the preceding ring isomorphism gives an injective ring map `j_D : B_D → T`
   sending `a ⊗ d` to `a ⊗ i_D(d)`. This includes the case `B_D = 0`.
4. If `B_E` is reduced, apply `lem-weil-pbc-perfect-reduced-tensor`
   (`isReduced_tensorProduct_of_perfectField`) over the perfect field `E` to `B_E` and
   the reduced field `M`. Thus `B_E ⊗[E] M` is reduced; its ring isomorphism with `T`
   makes `T` reduced as well.
5. For any nilpotent `x` in `B_F`, its image `j_F(x)` is nilpotent in `T`, hence zero;
   injectivity gives `x = 0`. Thus `B_F` is reduced. Conversely, if `B_F` is reduced,
   apply the same perfect-field tensor theorem over `F` and the ring isomorphism to make
   `T` reduced, then descend nilpotents through `j_E` to show that `B_E` is reduced.
-/
theorem isReduced_tensorProduct_iff_of_perfectField
    (k : Type u) (A : Type v) (E : Type w) (F : Type z)
    [Field k] [CommRing A] [Field E] [Field F]
    [Algebra k A] [Algebra k E] [Algebra k F] [PerfectField E] [PerfectField F] :
    IsReduced (A ⊗[k] E) ↔ IsReduced (A ⊗[k] F) := by
  sorry

end Algebra
