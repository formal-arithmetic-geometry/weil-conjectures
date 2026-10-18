/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weil numbers

Source: literature/blueprint/master/blueprint/sec-zeta-weil/sk-def-roots/def-weil-numbers.md,
node `def-weil-numbers`, order 2864 (blueprint: def-weil-numbers).

For the global finite-field datum `D` (blueprint: def-weil-finite-field-fiber), which fixes
the prime `p`, the exponent `a ≥ 1` and `q = p ^ a`, `IsWeilNumber D α w` is the condition
that `α` is a nonzero element of any fixed algebraic closure `Qbar` of `ℚ` and every
field embedding `τ : ℚ(α) → ℂ` satisfies `‖τ α‖ = q ^ (w / 2)`, the weight `w` being real.
A field homomorphism is a `RingHom`; its restriction to `ℚ` is the identity by `map_ratCast`.
The node's algebraic-integer clause is Mathlib's `IsIntegral ℤ α`
(blueprint: def-weil-algebraic-integer) and is not redeclared.
-/

@[expose] public section

universe u v

namespace WeilConjectures

/-- A nonzero element `α` of the fixed algebraic closure of `ℚ` is a `q`-Weil number of
real weight `w`, for the fixed prime power `q = D.q = p ^ a` of the global finite-field
datum `D`, when every field embedding `τ` of the simple field `ℚ(α)` into `ℂ` has
`|τ(α)| = q ^ (w / 2)`.

Source: literature/blueprint/master/blueprint/sec-zeta-weil/sk-def-roots/def-weil-numbers.md,
node `def-weil-numbers`, order 2864 (blueprint: def-weil-numbers). -/
def IsWeilNumber (D : FiniteFieldDatum.{u}) {Qbar : Type v} [Field Qbar]
    [Algebra ℚ Qbar] [IsAlgClosure ℚ Qbar] (α : Qbar) (w : ℝ) : Prop :=
  α ≠ 0 ∧
    ∀ τ : IntermediateField.adjoin ℚ ({α} : Set Qbar) →+* ℂ,
      ‖τ (IntermediateField.AdjoinSimple.gen ℚ α)‖ = (D.q : ℝ) ^ (w / 2)

end WeilConjectures
