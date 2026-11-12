/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgClData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!
# The composition isomorphisms of `Rf_!` as instances of the general construction

The composition isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on bounded constructible `E`-sheaves
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp`) and `ℚ̄_ℓ`-sheaves
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`) are the general
construction `ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekComp` for the
pushforward data of `E̲` and `ℚ̲̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_eq_lowerShriekComp`,
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_eq_lowerShriekComp`).

For `E` the proof unfolds the definitions `boundedConstructibleLowerShriekComp` and
`boundedConstructibleLowerShriekOfCompactificationIso`, whose bodies are not exposed: this file
imports their defining modules with `import all`. It is kept separate so that these bodies stay
invisible to the kernel in the files using the identifications.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (f : X ⟶ Y) (g : Y ⟶ S)

section Bridge

variable (k) in
/-- The exchange morphisms `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of the pushforward datum of `ℚ̲̄_ℓ` are
isomorphisms for proper `p'`. -/
lemma isIsoExchange_padicAlgClPushforwardData :
    (padicAlgClPushforwardData ℓ k).IsIsoExchange := by
  intro X Z X' Z' _ _ _ _ _ _ _ _ _ _ _ _ p i' j p' _ _ _ sq
  have h : (padicAlgClPushforwardData ℓ k).lowerStarOpenImmersionLowerShriekExchange sq =
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq := by
    unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
      BoundedConstructiblePushforwardData.lowerStarOpenImmersionLowerShriekExchange
      Adjunction.exchangeRight
    rfl
  rw [h]
  exact isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ sq

variable (k) in
/-- The exchange morphisms `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of the pushforward datum of `E̲` are
isomorphisms for proper `p'`. -/
lemma isIsoExchange_continuousMapPushforwardData :
    (continuousMapPushforwardData ℓ k E).IsIsoExchange := by
  intro X Z X' Z' _ _ _ _ _ _ _ _ _ _ _ _ p i' j p' _ _ _ sq
  have h : (continuousMapPushforwardData ℓ k E).lowerStarOpenImmersionLowerShriekExchange sq =
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E
        sq := by
    unfold ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
      BoundedConstructiblePushforwardData.lowerStarOpenImmersionLowerShriekExchange
      Adjunction.exchangeRight
    rfl
  rw [h]
  exact isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on bounded constructible
`ℚ̄_ℓ`-sheaves is the one of the pushforward datum of `ℚ̲̄_ℓ`. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_eq_lowerShriekComp :
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g =
      BoundedConstructiblePushforwardData.lowerShriekComp
        (isIsoRefinementPushforward_padicAlgClPushforwardData ℓ k)
        (isIsoExchange_padicAlgClPushforwardData ℓ k) f g := by
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_def]
  simp only [boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq_refinementIso]
  rfl

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on bounded constructible `E`-sheaves is
the one of the pushforward datum of `E̲`: both are the same construction. The proof is the
unfolding of `boundedConstructibleLowerShriekComp` and
`boundedConstructibleLowerShriekOfCompactificationIso`, whose bodies are not exposed outside
their defining modules. -/
lemma boundedConstructibleLowerShriekComp_eq_lowerShriekComp :
    boundedConstructibleLowerShriekComp ℓ E f g =
      BoundedConstructiblePushforwardData.lowerShriekComp
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E)
        (isIsoExchange_continuousMapPushforwardData ℓ E k) f g := by
  unfold boundedConstructibleLowerShriekComp
  simp only [boundedConstructibleLowerShriekOfCompactificationIso]
  rfl

end Bridge

end AlgebraicGeometry.ProEtale.CondensedRing
