/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.TateTwistPowerDatum
public import WeilConjectures.WeilSheaf.ConstantTwistCondensed
public import WeilConjectures.WeilSheaf.FrobeniusTwist

/-!
# The condensed Tate twist and the native constant twist `ℚ̄_ℓ ⊗ 𝓑_{χ^d}`

In the condensed model of Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`, Weil
structures for `(Fr_X⁻¹)_*`), the native Tate sheaf `ℚ̄_ℓ(d) = ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)^d}` becomes the regular
module with structure `χ_ℓ(σ)^d` times the structure of `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.toCondensedObjConstantTwistAdicConstantIso`). The condensed Tate
twist `ℚ̄_ℓ,X̄(d)` (`AlgebraicGeometry.ProEtale.tateTwistNat`) with its pullback datum along the
Frobenius `Fr_X^*` (`AlgebraicGeometry.ProEtale.upperStarTateTwistNatIso`), transported to the
`(Fr_X⁻¹)_*` model along `upperStarIsoLowerStarInv`, is the pair
`AlgebraicGeometry.WeilSheaf.tateTwistLowerPair`. Given
- a trivialization of `ℚ̄_ℓ,X̄(1)` carrying the pullback datum to `χ_ℓ(σ)` times the unit constraint
  (the `d = 1` input `e₁`), and
- the compatibility of the unit structures: the native structure of `ℚ̄_ℓ` in the condensed model is
  the unit constraint of `Fr_X^*` transported to `(Fr_X⁻¹)_*` (`hunit`),
the two pairs are isomorphic for every `d`
(`AlgebraicGeometry.WeilSheaf.nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] neZero_natCast_algebraicClosure

/-- Powers of the scalar `b` on the regular module are the scalar `b ^ d`. -/
lemma scalarPow_regularSmulIso_hom (b : (PadicAlgCl l)ˣ) :
    ∀ d : ℕ, (IsoAlgebra.scalarPow (regularSmulIso k₀ l X b) d).hom =
      (regularSmulIso k₀ l X (b ^ d)).hom
  | 0 => by
    simp only [IsoAlgebra.scalarPow, Iso.refl_hom, regularSmulIso_hom, pow_zero, Units.val_one,
      map_one]
    rfl
  | d + 1 => by
    rw [IsoAlgebra.scalarPow, Iso.trans_hom, scalarPow_regularSmulIso_hom b d, regularSmulIso_hom,
      regularSmulIso_hom, regularSmulIso_hom, ← End.mul_def]
    erw [← map_mul, ← map_mul]
    rw [← Units.val_mul, ← pow_succ']
    rfl

end AlgebraicGeometry.WeilSheaf
