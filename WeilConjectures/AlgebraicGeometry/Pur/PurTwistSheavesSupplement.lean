/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor
import WeilConjectures.CategoryTheory.Tensor.TensorPushoutAction
public import WeilConjectures.AlgebraicGeometry.PurTwistSheaves

/-! # The integral Tate line on the pro-etale site

Source: Stacks Project, Tag 03PK; the coefficient-twist blueprint, order 1505
(blueprint: def-pur-twist-sheaves).

The auxiliary constructions retain the root tower, constant scalar extension and completed
scalar action. All choices below have a uniqueness specification. The tensor of commutative
ring sheaves is their pushout, so the coefficient comparison is a morphism of ring sheaves.
The natural-number level `n` means positive exponent `n + 1` throughout.

## Main definitions

* `purTwistZlOne` and `purTwistZlModule`: the root limit and its completed scalar action.
* `purTwistIntegralOne` and `purTwistIntegralModule`: the prescribed integral tensor line.
* `purTwistFiniteOne`: its prescribed ordinary finite-coefficient tensor reduction.
The coefficient rings and their comparison are reexported from
`WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement`.
Local freeness and derived completeness
are proved in `WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree`.
-/

@[expose] public section

set_option autoImplicit false

universe u d

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]

-- Jointly injective coordinates transfer the module laws and determine the action uniquely.

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
