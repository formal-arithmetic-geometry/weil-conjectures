/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.FieldTheory.SeparableExtension

import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable

/-!
# Separability descends from a tensor field

Source: Stacks Project, Algebra, Tags 030U and 030W; descent corollary using
Fields, Tag 0H7K (blueprint: lem-sfb-separability-tensor-field-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- If the canonical tensor algebra `F ⊗[k] k'` is a field separable over `k'`, then
`F/k` is separable, including for extensions that are not algebraic or finitely generated.
The field structure is obtained from fieldness of the canonical tensor ring, and the
`k'`-algebra structure is the canonical map `b ↦ 1 ⊗ₜ b`.

Source: Stacks Project, Algebra, Tags 030U and 030W, with Fields, Tag 0H7K
(blueprint: lem-sfb-separability-tensor-field-descent).

Proof:
1. Set `T = F ⊗[k] k'`. In characteristic zero use
   `lem-weil-pbc-char-zero-field-extension-separable`. Otherwise the characteristic
   is a prime `p > 0`.
2. For an arbitrary field extension `L/k`, use `lem-weil-common-extension-fields` to
   embed `L` and `k'` compatibly over `k` into a field `M`. Regard `M` as a `k'`-algebra.
3. To prove `T ⊗[k'] M` reduced, write a nilpotent as a finite sum of pure tensors.
   Its finitely many coefficients in `T` belong to a finitely generated intermediate
   field `E/k'`. By `def-weil-pbc-separable-field-extension`, `E/k'` is separably
   generated. Thus `E ⊗[k'] M` is reduced by
   `lem-weil-pbc-separably-generated-tensor-reduced`. Its map to `T ⊗[k'] M` is
   injective by `lem-weil-pbc-module-over-field-flat` and
   `lem-trf-flat-tensor-preserves-injection`. The lifted finite sum is nilpotent,
   hence zero, so the original element is zero.
4. The tensor universal properties `def-weil-pbc-module-tensor-product` and
   `lem-weil-pbc-algebra-tensor-pushout-universal-property` give inverse ring maps
   `(F ⊗[k] k') ⊗[k'] M → F ⊗[k] M`, sending `(a ⊗ b) ⊗ m` to `a ⊗ j(b)m`,
   and `F ⊗[k] M → (F ⊗[k] k') ⊗[k'] M`, sending `a ⊗ m` to `(a ⊗ 1) ⊗ m`.
   Balancing verifies the inverse formulas on pure tensors, which generate.
   Transport reducedness along these maps to `F ⊗[k] M`.
5. The map `F ⊗[k] L → F ⊗[k] M` induced by `L → M` is injective by
   `lem-weil-pbc-module-over-field-flat` and `lem-trf-flat-tensor-preserves-injection`.
   A nilpotent maps to zero in its reduced target, hence is zero. This proves
   reducedness of `F ⊗[k] L` for every `L/k`.
6. Apply `lem-weil-pbc-geometrically-reduced-extension-separable` in characteristic
   `p` to conclude exactly that every finitely generated intermediate field of `F/k`
   is separably generated. No algebraicity or finite-generation assumption was used.
-/
theorem isSeparableExtension_of_isField_tensorProduct
    (k : Type u) (k' : Type v) (F : Type w)
    [Field k] [Field k'] [Field F] [Algebra k k'] [Algebra k F]
    (hfield : IsField (F ⊗[k] k'))
    (hsep : @IsSeparableExtension k' (F ⊗[k] k') _ hfield.toField
      (Algebra.TensorProduct.rightAlgebra (R := k) (A := F) (B := k'))) :
    IsSeparableExtension k F := by
  sorry

end Algebra
