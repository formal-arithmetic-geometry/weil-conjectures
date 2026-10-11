/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Descent of finite purely inseparable field extensions

Source: Stacks Project, Tag 07QG, the finite purely inseparable extension asserted in its proof;
Tag 09HE for purely inseparable extensions
(blueprint: lem-weil-pbc-finite-purely-inseparable-scalar-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- A finite purely inseparable field extension descends along extension of scalars.
Source: Stacks Project, Tag 07QG (implicit in its proof), and Tag 09HE
(blueprint: lem-weil-pbc-finite-purely-inseparable-scalar-descent).

Proof (agent's basis argument recorded in the DAG):
1. Set `A = L ⊗[K] B`, with its left-factor `L`-algebra structure. Since `A` is a field,
   `B` is nonzero (def-weil-module-base-change, def-pc-field-extension).
2. Choose a `K`-basis of `B` containing `1`
   (lem-weil-pbc-vector-space-basis-through-vector).
3. Scalar extension and swapping tensor factors give the `L`-basis `1 ⊗ bᵢ` of `A`.
   Its finite cardinality gives finiteness of `B` and the dimension equality
   (def-weil-vector-space-scalar-extension, def-weil-module-base-change,
   def-weil-vector-space-dimension, def-weil-finite-dimensional-subspace).
4. This basis shows that `b ↦ 1 ⊗ b` is injective. Thus `B` embeds in the field `A`
   and is a domain.
5. A finite-dimensional domain over a field is a field
   (lem-weil-pbc-finite-dimensional-domain-is-field, def-pc-field-extension,
   def-weil-pbc-finite-purely-inseparable-extension).
6. In characteristic `p > 0`, pure inseparability gives `1 ⊗ β^(p^n) = l ⊗ 1`.
   Comparing coordinates in the basis through `1` shows that `β^(p^n)` lies in `K`
   (def-weil-pbc-finite-purely-inseparable-extension).
7. In characteristic zero, pure inseparability says `A = L`. Its dimension is one,
   so the basis of `B` consists only of `1`, and `B = K`
   (def-weil-pbc-finite-purely-inseparable-extension). -/
theorem finite_purelyInseparable_of_tensorProduct
    (K : Type u) (L : Type v) (B : Type w)
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (hfield : IsField (L ⊗[K] B))
    [Module.Finite L (L ⊗[K] B)] [IsPurelyInseparable L (L ⊗[K] B)] :
    IsField B ∧ Module.Finite K B ∧ IsPurelyInseparable K B ∧
      Module.finrank K B = Module.finrank L (L ⊗[K] B) := by
  sorry

end Algebra.TensorProduct
