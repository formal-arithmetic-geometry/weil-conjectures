/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelRingedProEtaleBaseChange

/-!
# Transport of finite coefficient exchange

This is the coefficient transport step for the finite-level proper base-change theorem.
Source: Stacks Tags 09C8 and 09C9.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- After restriction from the continuous-function coefficient presentation to the constant
coefficient presentation, the ambient finite exchange is invertible. The coefficient
identifications are arbitrary, and invertibility is only asserted after applying
`finiteOriginToConstant`.
Source: Stacks Tags 09C8 and 09C9. -/
theorem finiteOriginToConstant_map_ambientExchange_isIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ) c_f c_g')
      (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ) c_g c_f'))
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((finiteOriginToConstant Y' Λ).map
      ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
        (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X' Λ)
        (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app K)) := by
  sorry

end AlgebraicGeometry.Scheme
