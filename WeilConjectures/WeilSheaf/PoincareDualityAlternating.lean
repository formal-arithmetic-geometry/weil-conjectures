/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.PoincareDuality
public import WeilConjectures.ZetaLinearAlgebra.TraceCupAlternating

/-!
# The middle-degree Poincaré pairing in odd dimension is alternating

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`,
and `Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. The Poincaré pairing `⟨x, y⟩ = tr (x ⌣ y)` on `H^d` satisfies
`⟨y, x⟩ = (-1)^d ⟨x, y⟩` (`AlgebraicGeometry.WeilSheaf.exists_traceCup_poincarePairing`); since
`ℚ̄_ℓ` has characteristic zero, it is alternating when `d` is odd.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_traceCup_isAlt_pairing_of_odd`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-cup-product-pairing--3`: for `X` smooth, proper and geometrically
connected of odd pure dimension `d` over `k₀ = 𝔽_q`, the cohomology
`H^• = H^•(X ⊗ k̄, ℚ̄_ℓ)` carries a trace–cup structure whose trace `H^{2d} ⟶ ℚ̄_ℓ(-d)` is an
isomorphism, whose pairings `Hⁱ × H^{2d-i} ⟶ ℚ̄_ℓ(-d)` are perfect, and whose middle pairing
`⟨x, y⟩ = tr (x ⌣ y)` on `H^d` is alternating, `⟨x, x⟩ = 0`, as for a compact complex manifold
of odd dimension. The coefficient field `ℚ̄_ℓ` has characteristic zero, so this follows from
graded commutativity (`FrobeniusModule.TraceCup.isAlt_pairing`). -/
theorem exists_traceCup_isAlt_pairing_of_odd (hd : Odd d) :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} (adicConstant k₀ l X).cohomology (2 * d)
        ((Nat.card k₀ : PadicAlgCl l) ^ d),
      Function.Bijective T.trace ∧
      (∀ (i j : ℤ) (h : i + j = 2 * d), (T.pairing i j h).IsPerfPair) ∧
      (T.pairing d d (two_mul (d : ℤ)).symm).IsAlt := by
  obtain ⟨T, htr, -, hp⟩ := exists_traceCup_poincarePairing k₀ l X d
  exact ⟨T, htr, fun i j h ↦ (hp i j h).1,
    T.isAlt_pairing ((Int.odd_coe_nat d).2 hd) (two_mul (d : ℤ)).symm⟩

end WeilSheaf

end AlgebraicGeometry
