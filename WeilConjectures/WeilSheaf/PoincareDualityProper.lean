/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TraceEquivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UntwistedPerfectness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice

/-!
# Frobenius-equivariant Poincaré duality for a smooth proper geometrically connected scheme

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, and
`Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` with its geometric Frobenius `F`. For `i + j = 2d` there is a perfect
pairing `Hⁱ × Hʲ ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩`
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_isProper`).

At each finite level `Λ = ℤ/ℓᵐ` the untwisted degreewise Poincaré pairing
`H^i_c(X̄, Λ) × H^j(X̄, Λ) ⟶ Λ(-d)` of the geometric fibre is nondegenerate
(`AlgebraicGeometry.Etale.TateOrientation.nondegenerate_untwistedDegreewisePoincarePairing`) and a
`q^d`-similitude for the Frobenius operators
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_unit_frobeniusOperator`),
given the Weil equivariance of the smooth trace
(`AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace`). Read through
`H^i_c = H^i` (`a` proper), the adjunction `La^* ⊣ Ra_*` (which intertwines the Frobenius operators,
`AlgebraicGeometry.Etale.frobeniusOperator_unitShiftAddEquivLowerStar`) and a trivialisation of
`Λ(-d)` over `k̄`, these are the finite-level dualities of
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_unitPairing`, which
transports them to `ℚ̄_ℓ`.

This is clause (1) of blueprint `thm-pod-qbar-coefficient-pairing` for the constant sheaf on a
proper `X₀` (`H_c = H`), with the similitude of `cor-pod-untwisted-similitude`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-pod-qbar-coefficient-pairing` (clause (1), for the constant sheaf on a proper
`X₀`, with the similitude of `cor-pod-untwisted-similitude`): for `X₀` smooth, proper and
geometrically connected of pure dimension `d` over `k₀` and `i + j = 2d`, there is a perfect pairing
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ) × Hʲ(X₀ ⊗ k̄, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for the geometric
Frobenius `F`. -/
theorem exists_isPerfPair_cohomology_adicConstant_of_isProper (i j : ℕ) (h : i + j = 2 * d) :
    ∃ P : ((adicConstant k₀ l X).cohomology i).carrier →ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P (((adicConstant k₀ l X).cohomology i).frobenius x)
        (((adicConstant k₀ l X).cohomology j).frobenius y) =
          (Nat.card k₀ : PadicAlgCl l) ^ d * P x y :=
  sorry

end AlgebraicGeometry.WeilSheaf
