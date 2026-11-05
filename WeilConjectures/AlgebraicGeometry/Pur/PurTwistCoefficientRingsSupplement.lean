/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
public import WeilConjectures.AlgebraicGeometry.PurTwistCoefficientRings

/-! # Coefficient rings of the integral Tate twist

Source: coefficient-twist blueprint, order 1505.
(blueprint: def-pur-twist-coefficient-rings)

The constant and completed coefficient rings, their quotient projections, and the
canonical comparison form the coefficient data used before constructing the Tate line.
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
variable (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
