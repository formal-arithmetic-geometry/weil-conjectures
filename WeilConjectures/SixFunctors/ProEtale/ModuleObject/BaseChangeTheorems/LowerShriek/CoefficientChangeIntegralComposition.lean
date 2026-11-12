/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral

/-!
# The building blocks of the lower shriek and the extension of scalars `𝒪_E ⟶ E`

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
let `C = ProEtale.CondensedRing.extendScalarsCoefficientChange ℓ E k` be the extension of scalars
`𝒪_E ⟶ E` as a coefficient change of the bounded constructible six functors. This file shows
that the following isomorphisms are compatible with the coefficient comparisons of `C`:

* the independence isomorphisms `Rf_!^{c₁} ≅ Rf_!^{c₂}` of the lower shriek from the
  compactification
  (`ProEtale.CondensedRing.squareCompatible_lowerShriekOfCompactificationIso_extendScalars`);
* the identity isomorphism `(𝟙 X)_! ≅ 𝟭` of the trivial compactification of a proper morphism
  (`ProEtale.CondensedRing.squareCompatible_openImmersionLowerShriekOfIsProperIso_extendScalars`);
* the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*` of a cartesian square
  (`squareCompatible_lowerStarOpenImmersionLowerShriekExchange_extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section PushforwardData

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

lemma padicIntegersPushforwardData_lowerStar (p : X ⟶ Y) :
    (padicIntegersPushforwardData ℓ k E.1).lowerStar p =
      PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p :=
  rfl

lemma continuousMapPushforwardData_lowerStar (p : X ⟶ Y) :
    (continuousMapPushforwardData ℓ k E).lowerStar p =
      ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p :=
  rfl

lemma padicIntegersPushforwardData_lowerStarComp (p : X ⟶ Y) (q : Y ⟶ Z) :
    (padicIntegersPushforwardData ℓ k E.1).lowerStarComp p q =
      PadicIntegersRingObj.boundedConstructibleLowerStarComp ℓ E.1 p q :=
  rfl

lemma continuousMapPushforwardData_lowerStarComp (p : X ⟶ Y) (q : Y ⟶ Z) :
    (continuousMapPushforwardData ℓ k E).lowerStarComp p q =
      ContinuousMapRingObj.boundedConstructibleLowerStarComp ℓ E p q :=
  rfl

end PushforwardData

section Independence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The independence isomorphism of `E̲` is the one of its pushforward datum. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_eq_pushforwardData
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso ℓ E c₁ c₂ =
      BoundedConstructiblePushforwardData.lowerShriekOfCompactificationIso
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) c₁ c₂ := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso
  rfl

/-- The independence isomorphism of `𝒪̲_E` is the one of its pushforward datum. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers_eq_pushforwardData
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E.1 c₁ c₂ =
      BoundedConstructiblePushforwardData.lowerShriekOfCompactificationIso
        (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E.1) c₁ c₂ := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers
  rfl

/-- The independence isomorphisms `Rf_!^{c₁} ≅ Rf_!^{c₂}` of `𝒪̲_E` and `E̲` are compatible with
the extension of scalars. -/
lemma squareCompatible_lowerShriekOfCompactificationIso_extendScalars
    (c₁ c₂ : Compactification f.left) :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification c₁)
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification c₂)
      (boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E.1 c₁ c₂).hom
      (boundedConstructibleLowerShriekOfCompactificationIso ℓ E c₁ c₂).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationIso_eq_pushforwardData,
    boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers_eq_pushforwardData]
  exact (extendScalarsCoefficientChange ℓ E k).squareCompatible_lowerShriekOfCompactificationIso
    _ _ c₁ c₂

end Independence

section IsProper

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The identity isomorphisms `(𝟙 X)_! ≅ 𝟭` of the trivial compactification
`X ⟶[𝟙] X ⟶[f] Y` of a proper `f` are compatible with the extension of scalars. -/
lemma squareCompatible_openImmersionLowerShriekOfIsProperIso_extendScalars (f : X ⟶ Y)
    [IsProper f.left] :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriek (Compactification.ofIsProper f.left).overI)
      (Functor.idSquareIso (boundedConstructibleExtendScalars X.left ℓ E))
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
        (Profinite.padicIntegersRingObj ℓ E.1) ℓ f).hom
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
        (Profinite.continuousMapRingObj E.1) ℓ f).hom := by
  have hm := (extendScalarsCoefficientChange ℓ E k).isMateSquare_shriek_pull
    (Compactification.ofIsProper f.left).overI
  have hu := (extendScalarsCoefficientChange ℓ E k).squareCompatible_upperStarId X
  have h₁ :=
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
      (Profinite.padicIntegersRingObj ℓ E.1) ℓ f
  have h₂ :=
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
      (Profinite.continuousMapRingObj E.1) ℓ f
  exact NatTrans.SquareCompatible.of_adjunction hm _ _ _ _ h₁ h₂ hu

end IsProper

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` (`E`-coefficient) is the exchange
morphism `CategoryTheory.Adjunction.exchangeRight` of the extension-by-zero base-change
isomorphism under the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchangeRight
    (sq : IsPullback p i' j p') :
    ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq =
      Adjunction.exchangeRight
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
          (Profinite.continuousMapRingObj E) ℓ sq) := by
  unfold ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
    ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
    Adjunction.exchangeRight
  rfl

/-- The exchange morphisms `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of `𝒪̲_E` and `E̲` of a cartesian square
with `p` and `p'` proper are compatible with the extension of scalars. -/
lemma squareCompatible_lowerStarOpenImmersionLowerShriekExchange_extendScalars
    [IsProper p.left] [IsProper p'.left] (sq : IsPullback p i' j p') :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso ((extendScalarsCoefficientChange ℓ E k).push p)
        ((extendScalarsCoefficientChange ℓ E k).shriek j))
      (Functor.pasteSquareIso ((extendScalarsCoefficientChange ℓ E k).shriek i')
        ((extendScalarsCoefficientChange ℓ E k).push p'))
      (PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E.1 sq)
      (ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ E sq) := by
  have h := NatTrans.SquareCompatible.exchangeRight
    ((extendScalarsCoefficientChange ℓ E k).isMateSquare_pull_push p)
    ((extendScalarsCoefficientChange ℓ E k).isMateSquare_pull_push p')
    ((extendScalarsCoefficientChange ℓ E k).squareCompatible_openImmersionLowerShriekBaseChangeIso
      sq)
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers_eq,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchangeRight]
  exact h

end Exchange

end AlgebraicGeometry.ProEtale.CondensedRing
