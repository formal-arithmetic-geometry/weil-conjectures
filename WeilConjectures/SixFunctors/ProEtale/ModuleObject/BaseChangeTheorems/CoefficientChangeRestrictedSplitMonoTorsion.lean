/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.RetractionLift

/-!
# Split restricted base change maps from unique torsion retractions

For a commutative square `sq : g' ≫ p' = p ≫ g` of quasi-compact quasi-separated schemes,
`i : Z ⟶ Y'` and a derived complete `𝒪_E`-complex `K₀`, the restricted base change map
`Li^* BC_sq(K₀)` with `𝒪_E`-coefficients is a split monomorphism if its reductions modulo `ℓⁿ⁺¹`
have unique retractions with a property preserved by reduction
(`ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicIntegers_of_unique_retractions`),
by `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`: the source
`Li^* Lg^* Rp_* K₀` is derived complete.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Lifting unique torsion retractions of the restricted base change map to `𝒪_E`**: for
quasi-compact quasi-separated schemes and a derived complete `K₀`, the restricted base change map
`Li^* BC_sq(K₀)` with `𝒪_E`-coefficients is a split monomorphism if its reductions modulo `ℓⁿ⁺¹`
have unique retractions with a property `Pₙ` preserved by reduction. The hypotheses are stated on
a morphism `f₀` equal, as an arrow, to `Li^* BC_sq(K₀)`. -/
theorem isSplitMono_map_baseChangeMap_app_padicIntegers_of_unique_retractions [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z]
    [QuasiSeparatedSpace Z] (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK₀ : derivedCompleteIntegers ℓ E X K₀)
    {A B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))} (f₀ : A ⟶ B)
    (hf₀ : Arrow.mk f₀ = Arrow.mk ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀)))
    (P : ∀ n, (L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).obj A) → Prop)
    (hex : ∀ n, ∃ r, P n r ∧
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map f₀ ≫ r = 𝟙 _)
    (huniq : ∀ n r r', P n r → P n r' →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map f₀ ≫ r = 𝟙 _ →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map f₀ ≫ r' = 𝟙 _ →
      r = r')
    (hred : ∀ n r, P (n + 1) r →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1 + 1))).map f₀ ≫ r = 𝟙 _ →
      P n (Mod.derivedExtendScalarsReduction (integersModPowReduction Z ℓ E.1 (n + 1 + 1))
        (modPowTransition Z ℓ E.1 (n + 1)) (integersModPowReduction Z ℓ E.1 (n + 1))
        (integersModPowReduction_comp_modPowTransition Z ℓ E.1 (n + 1)) r)) :
    IsSplitMono ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀)) := by
  have hA : derivedCompleteIntegers ℓ E Z A := by
    have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj i
      (derivedCompleteIntegers_leftDerivedUpperStar_obj g
        (derivedCompleteIntegers_rightDerivedLowerStar_obj p hK₀))
    have e := congrArg Comma.left hf₀
    dsimp only [Arrow.mk_left] at e
    rw [e]
    exact hsrc
  have := isSplitMono_of_derivedCompleteIntegers_of_unique_retractions f₀ hA P hex huniq hred
  exact Arrow.isSplitMono_of_iso (eqToIso hf₀.symm)

end AlgebraicGeometry.ProEtale.CondensedRing
