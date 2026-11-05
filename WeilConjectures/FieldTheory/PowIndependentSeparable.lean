/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals
public import WeilConjectures.FieldTheory.AdjoinSimplePow
public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# `p`-independence is preserved by separable extensions of a rational function field

Let `k → Q` be fields of characteristic `p`, `x ∈ Q` transcendental over `k`, and `b` a
`p`-independent family of `k`. Then the monomials `∏ b i ^ E i` (`0 ≤ E i < p`) stay linearly
independent over the `p`-th powers of elements of `Q` separable over `k⟮x⟯`
(`Field.PowIndependent.eq_zero_of_isSeparable`). In particular, `b` stays `p`-independent in any
extension of `k` which is separable algebraic over `k⟮x⟯`
(`Field.PowIndependent.map_of_isSeparable`).

Proof: the monomials are linearly independent over `k⟮x⟯ ^ p = k ^ p ⟮x ^ p⟯` (expand in powers of
the transcendental `x ^ p`), and the extension `k⟮x⟯ / k⟮x⟯ ^ p` is purely inseparable while the
`p`-th powers of separable elements are separable over `k⟮x⟯ ^ p`; separable and purely
inseparable extensions are linearly disjoint
(`IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`).
-/

@[expose] public section

open IntermediateField Polynomial

namespace Field

variable {k Q : Type*} [Field k] [Field Q] [Algebra k Q] (p : ℕ) [Fact p.Prime] [CharP Q p]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Field
