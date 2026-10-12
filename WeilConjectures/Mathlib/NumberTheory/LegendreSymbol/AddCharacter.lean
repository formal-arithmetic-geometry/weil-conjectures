/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Nontrivial additive characters with values in an algebraically closed field

A finite field `F` has a nontrivial additive character with values in any algebraically closed
field `K` whose characteristic differs from that of `F`: the primitive character
`AddChar.FiniteField.primitiveChar`, with values in a cyclotomic extension of `K`, followed by a
`K`-embedding of that extension into `K`.
-/

@[expose] public section

namespace AddChar

/-- A finite field `F` has a nontrivial additive character with values in an algebraically
closed field `K` of characteristic different from that of `F`. -/
theorem exists_ne_one_of_isAlgClosed (F K : Type*) [Field F] [Finite F] [Field K]
    [IsAlgClosed K] (h : ringChar K ≠ ringChar F) : ∃ ψ : AddChar F K, ψ ≠ 1 := by
  let ψ := FiniteField.primitiveChar F K h
  have : Algebra.IsAlgebraic K (CyclotomicField ψ.n K) :=
    inferInstanceAs (Algebra.IsAlgebraic K (Polynomial.cyclotomic ψ.n K).SplittingField)
  let φ : CyclotomicField ψ.n K →ₐ[K] K := IsAlgClosed.lift
  refine ⟨(φ : CyclotomicField ψ.n K →* K).compAddChar ψ.char, fun h1 ↦ ?_⟩
  refine ψ.prim one_ne_zero ?_
  ext a
  apply φ.injective
  have := DFunLike.congr_fun h1 a
  simpa [mulShift_apply] using this

end AddChar
