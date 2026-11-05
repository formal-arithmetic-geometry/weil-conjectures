/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.FieldTheory.Minpoly.Basic

/-!
# Finite p-adic coefficient extensions under algebra isomorphisms

An isomorphism of finite extensions of `ℚ_[l]` preserves the spectral absolute value, hence
identifies the valuation rings and their uniformizer ideals. Every finite extension has an
isomorphic model in any universe.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

namespace Padic

variable (l : ℕ) [Fact l.Prime]
variable {E : Type v} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {E' : Type w} [Field E'] [Algebra ℚ_[l] E'] [FiniteDimensional ℚ_[l] E']

end Padic
