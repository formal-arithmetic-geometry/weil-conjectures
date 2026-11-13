/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Base change morphism for etale extension by zero

Source: Stacks Project, Etale Cohomology, Tags 03S6 (proof) and 03S3(3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The base change morphism `j'_! f'⁻¹ ⟶ f⁻¹ j_!` on sheaves of constant-ring modules,
where `V' = pullback f j`, `j' = pullback.fst f j` and `f' = pullback.snd f j`.
(Stacks, Tags 03S6 and 03S3) -/
noncomputable def etaleLowerShriekBaseChangeMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y V X : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X) [Etale j] :
    upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f j) ⋙
        etaleLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst f j) inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance ⋙
        upperStar (ModuleCat.{u + 1} Λ) f :=
  (conjugateEquiv
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (pullback.snd f j)).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
        (pullback.fst f j) inferInstance))).symm
    (baseChangeMap (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback f j).toCommSq)

end AlgebraicGeometry.Etale
