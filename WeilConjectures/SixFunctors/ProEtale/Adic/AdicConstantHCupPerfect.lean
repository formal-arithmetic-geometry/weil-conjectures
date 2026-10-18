/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.RationalPerfectPairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHCup

/-!
# Perfectness of the cup product pairing on `H^*(S_proét, ℚ̄_ℓ)` from the finite levels

Let `S` be a quasi-compact quasi-separated scheme with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`, and
`i + j = n`. Suppose that at every finite level `m` the cup product pairing
`Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hⁿ(S, ℤ/ℓᵐ)` is nondegenerate on both sides, and that
`Hⁿ(S, ℚ̄_ℓ)` is a line, `t : Hⁿ(S, ℚ̄_ℓ) ≅ ℚ̄_ℓ`. Then the pairing
`(v, w) ↦ t(v ⌣ w) : Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` is perfect
(`AlgebraicGeometry.ProEtale.isPerfPair_adicConstantHCup`).

The proof transports the finite-level nondegeneracy to the integral cohomology `Hᵏ(S, ℤ_ℓ)`: if
`a ⌣ b` is torsion for all `b`, then by the Bockstein sequences (`ℓᵉ` killing the torsion) the
reduction of `ℓ^{2e} a` modulo `ℓᵐ` pairs to zero with all of `Hʲ(S, ℤ/ℓᵐ)`, hence vanishes, so that
`ℓ^{2e} a ∈ ⋂ₘ ℓᵐ Hⁱ(S, ℤ_ℓ) = 0`. Since `Hⁿ(S, ℤ_ℓ)` has rank one, `t` restricts to an integral
pairing with torsion kernels, whose extension to `ℚ̄_ℓ` is perfect
(`LinearMap.isPerfPair_of_span_eq_top`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
  (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

/-- **Perfectness of the `ℚ̄_ℓ`-cup product pairing from the finite levels.** If at every level
`ℤ/ℓᵐ` the cup product pairing `Hⁱ × Hʲ ⟶ Hⁿ` is nondegenerate on both sides and `Hⁿ(S, ℚ̄_ℓ)` is
a line `t : Hⁿ(S, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, then `(v, w) ↦ t(v ⌣ w)` is a perfect pairing on
`Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ)`. -/
theorem isPerfPair_adicConstantHCup {i j n : ℕ} (h : i + j = n)
    (hl : ∀ m (x : FiniteAdicH S l m i), (∀ y, finiteAdicHCup l m S h x y = 0) → x = 0)
    (hr : ∀ m (y : FiniteAdicH S l m j), (∀ x, finiteAdicHCup l m S h x y = 0) → y = 0)
    (t : AdicConstantH l S n ≃ₗ[PadicAlgCl l] PadicAlgCl l) :
    ((adicConstantHCup l S hfin h).compr₂ t.toLinearMap).IsPerfPair :=
  sorry

end AlgebraicGeometry.ProEtale
