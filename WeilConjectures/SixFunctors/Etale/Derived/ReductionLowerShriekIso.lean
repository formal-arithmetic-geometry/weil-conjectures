/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUpperShriek

/-!
# The reduction of coefficients commutes with compactly supported direct images

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars. For a morphism `f : X ⟶ Y` of schemes locally
of finite type over a field, the comparison `β_f : Ψ_Y ∘ Rf_! ⟶ Rf_! ∘ Ψ_X`
(`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType`).

The proof is not yet formalised. Closed immersions are done
(`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsLowerShriekMap_of_isClosedImmersion`), and the
proper case is reduced to identifications `θ_X : (- ⊗ᴸ R_X) ≅ Res ∘ Ψ` compatible with the derived
pullbacks (`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsLowerStarComparison`, through the
projection formula). Still missing: these identifications, the case of open immersions, and the
assembly along a compactification.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) [Finite Λ]

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients commutes with `Rf_!`**: for a morphism `f : X ⟶ Y` admitting a
compactification, `Y` quasi-compact and locally of finite type over a field, the comparison
`Ψ_Y ∘ Rf_! ⟶ Rf_! ∘ Ψ_X` is an isomorphism. Through a compactification `f = p ∘ j` this is the
projection formula `Rp_* M ⊗ᴸ Λ'_Y ≅ Rp_*(M ⊗ᴸ Λ'_X)` for the proper `p`, of finite
cohomological dimension, and the commutation of the extension by zero `j_!` with `- ⊗ᴸ Λ'`
(SGA 4, Exposé XVII, 5.2.9). -/
theorem isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] :
    IsIso (derivedExtendScalarsLowerShriekMap hρ ha f) :=
  sorry

end AlgebraicGeometry.Etale
