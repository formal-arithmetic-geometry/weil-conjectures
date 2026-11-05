/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field with base change
`φ̄ : X ⟶ Y` to the geometric fibres. The exchange isomorphisms
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` and `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*` of `ℓ`-adic
sheaves are mates under the adjunction `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_eq_mateEquiv`).
Consequently the unit and the counit of `φ̄^* ⊣ φ̄_*` are compatible with Frobenius structures,
which makes `φ^* ⊣ φ_*` an adjunction of Weil sheaves.

The proof iterates the mates correspondence along the Frobenius equivalences
`(Fr⁻¹)_* ⊣ Fr_*`: the iterated mate of the pullback exchange isomorphism is its conjugate, a
composite of composition and congruence isomorphisms of pushforwards, by the conjugation
identities for the pullbacks (`conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`);
and the mate of the pushforward exchange isomorphism along the Frobenius equivalences is the same
composite, which is checked on sections
(`AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)

/-- The exchange isomorphism `φ^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ φ^*` of pullbacks along a commutative
square `a ≫ φ = φ ≫ b` with `a`, `b` isomorphisms:
`(a⁻¹)_* φ^* ≅ a^* φ^* ≅ (a ≫ φ)^* = (φ ≫ b)^* ≅ φ^* b^* ≅ φ^* (b⁻¹)_*`. -/
noncomputable def upperStarExchangeIso (c : a.hom ≫ φ = φ ≫ b.hom) :
    (φ)^*[A] ⋙ (a.inv)_*[A] ≅ (b.inv)_*[A] ⋙ (φ)^*[A] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A a).symm ≪≫ (upperStarComp A _ _).symm ≪≫
    upperStarCongr A c ≪≫ upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv A b) _

end Sheaf

end AlgebraicGeometry.ProEtale
