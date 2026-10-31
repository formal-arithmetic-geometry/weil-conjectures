/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIntegralRealization
import WeilConjectures.CategoryTheory.StageSystem.StageComparisonNaturality

/-! # Descent of normalized finite-field components to the common-stage category

Source: Bhatt--Scholze, Remark 6.8.15 and the common-stage universal construction.
(blueprint: lem-sf-native-pullback-common-stage-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (O : Operations l p R S) (I : ∀ E, IntegralComparison l p R S O E)

/-- The finite-stage scalar square required for common-stage descent, expressed on
integral representatives. Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-common-stage-descent). -/
def NativePullbackStageScalarCoherent : Prop :=
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y),
    let P := (inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K)
    let t := (stageSystem l (PadicAlgCl l) Y).isoToStage P h
    (commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R).map t.hom ≫
        (nativePullbackRationalComparison l p R S O L (I L)).hom.app (P.toStage h) =
      (nativePullbackIntegralRealization l p R S O E (I E)).comparison.hom.app K ≫
        (ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient).map t.hom

/-- Compatible normalized stage components descend to an isomorphism on the actual
common-stage category, with every finite integral normalization retained.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-common-stage-descent).

Proof: extend each integral comparison uniquely through raw scalar localization.
For an object P, take the component at its recorded stage P.stage. The supplied
scalar square identifies this component after passage to a larger finite field.
Every common-stage arrow has a representative over such a field. The stage-system
naturality theorem therefore proves naturality. Inverses are the same componentwise
inverses, giving a natural isomorphism. On each finite integral object its component
is the prescribed integral composite, so its previously proved component calculation
gives IntegralAgreement, including both literal equality transports. -/
theorem nativePullbackCommonStageDescent
    (hscalar : NativePullbackStageScalarCoherent l p R S O I) :
    ∃ a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
        ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient,
      ∀ E, IntegralAgreement l p R S O E (I E) a := by
  let F := commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R
  let H := ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient
  let e := fun E ↦ nativePullbackRationalComparison l p R S O E (I E)
  have he (P : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) Y)
      (L : Index l (PadicAlgCl l)) (h : P.stage ≤ L) :
      F.map ((stageSystem l (PadicAlgCl l) Y).isoToStage P h).hom ≫
          (e L).hom.app (P.toStage h) =
        (e P.stage).hom.app P.obj ≫
          H.map ((stageSystem l (PadicAlgCl l) Y).isoToStage P h).hom := by
    obtain ⟨E, ⟨K⟩⟩ := P
    rw [show (e E).hom.app ⟨K⟩ =
      (nativePullbackIntegralRealization l p R S O E (I E)).comparison.hom.app K from
        (nativePullbackRationalRealization l p R S O E (I E)).exists.choose_spec K]
    exact hscalar E L h K
  let a : F ≅ H := NatIso.ofComponents (fun P ↦ (e P.stage).app P.obj)
    (fun f ↦ StageSystem.stageComparison_naturality
      (stageSystem l (PadicAlgCl l) Y) F H e he f)
  refine ⟨a, ?_⟩
  intro E
  apply (nativePullbackIntegralRealization l p R S O E (I E)).agreement a
  intro K
  change HEq ((e E).hom.app _) _
  exact heq_of_eq ((nativePullbackRationalRealization l p R S O E
    (I E)).exists.choose_spec K)

end WeilConjectures.AdicQbarRealization.Proper
