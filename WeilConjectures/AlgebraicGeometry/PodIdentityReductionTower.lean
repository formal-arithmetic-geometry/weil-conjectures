/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCompletionUnitScalarIntertwining
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerFunctorSpec
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

/-! # The strict identity compact-support tower

Source: blueprint sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, first sentence; Bhatt--Scholze 6.7.6.
(blueprint: lem-pod-identity-reduction-tower).
The finite identity comparisons are the existing canonical constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures.PodRawReconstruction
open PodCompletionScalar
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identity extension by zero in the intrinsic constant-ring presentation, obtained
from the specified realization equivalence and the open-sheaf identity adjunction.
Source: blueprint opening sentence, identity compactification
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteOpenIdentity (n : ℕ) :
    Scheme.sfIntrinsicExtensionByZero (𝟙 (point D))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerLeft
      (Scheme.sfIntrinsicModuleEquivalence (point D)
        (Padic.coefficientExtensionRing l E (n + 1))).inverse
      (isoWhiskerRight
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriekIdIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))) (point D))
        (Scheme.sfIntrinsicModuleEquivalence (point D)
          (Padic.coefficientExtensionRing l E (n + 1))).functor ≪≫
        Functor.leftUnitor _) ≪≫
    (Scheme.sfIntrinsicModuleEquivalence (point D)
      (Padic.coefficientExtensionRing l E (n + 1))).counitIso

/-- The fixed finite-level compact-support identity: exact identity open extension,
then the K-injective-normalized identity direct image. Source: blueprint opening
sentence (blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteIdentity (n : ℕ) :
    Scheme.sfIntrinsicCompactSupport (Compactification.ofIsProper (𝟙 (point D)))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (finiteOpenIdentity D l E n) ≪≫
        Functor.mapDerivedCategoryIdIso _)
      (Scheme.proEtaleConstantDerivedDirectImage (𝟙 (point D))
        (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    Functor.leftUnitor _ ≪≫
    Scheme.proEtaleGlobalEvaluationDirectImageId
      (Padic.coefficientExtensionRing l E (n + 1)) (point D)

/-- The identity finite operation applied to actual reduction and restriction.
Source: blueprint opening sentence, strict tower
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteRestrictedIdentity (n : ℕ) :
    compactSupportRestrictedLevel l E (Compactification.ofIsProper (𝟙 (point D))) n ≅
      scalarReductionDerivedExtension l E (point D) n ⋙
        scalarReductionDerivedRestriction l E (point D) n :=
  isoWhiskerLeft (scalarReductionDerivedExtension l E (point D) n)
      (isoWhiskerRight (finiteIdentity D l E n)
        (scalarReductionDerivedRestriction l E (point D) n) ≪≫ Functor.leftUnitor _)

/-- The chosen identity compact-support tower is the actual reduction tower.
Source: blueprint lem-pod-point-dualizing-complex.proof.md, first sentence,
expanded raw-rational reconstruction step 3; Bhatt--Scholze Definition 6.7.6.
(blueprint: lem-pod-identity-reduction-tower).

Proof: unfold the construction of exists_compactSupportReductionTower: it is
reduction, identity open extension on strict coefficient systems, identity proper
image on those systems, then exact restriction to completed coefficients. The
identity-open adjunction identifies extension with identity by its sectionwise
unit; the normalized K-injective comparison identifies identity proper image with
identity on the derived system category. Compare the reduction used in that
construction with A.reduction by uniqueness of left adjoints to the same total
limit. The scalar-adjunction unit-projection normalization fixes its evaluated
components to A.reductionEvaluation, rather than an arbitrary automorphism.
Whisker these three comparisons with exact strict-system restriction. Their
composition is theta. Evaluating the ordinary identity section maps and then
localizing gives the displayed finiteRestrictedIdentity equation. The chosen
tower's original evaluation comparisons satisfy every quotient-transition equation
by exists_compactSupportReductionTower. This argument takes place on whole systems;
it does not attempt to lift maps from the category of levelwise derived objects. -/
theorem identityReductionTower (hk : IsUnit (l : D.k))
    (A : CoefficientDerivedSystemCalculus l E (point D)) :
    ∃ (T : DerivedCategory (scalarReductionSource l E (point D)) ⥤
        coefficientSequenceRestrictedDerived l E (point D))
      (e : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l E (point D) n ≅
        compactSupportRestrictedLevel l E (Compactification.ofIsProper (𝟙 (point D))) n)
      (θ : A.reduction ⋙ coefficientSequenceDerivedRestriction l E (point D) ≅ T),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E D.k (point D) (point D)
          (𝟙 (point D)) hk
          (Compactification.ofIsProper (𝟙 (point D)))))).2.2 ∧
      HEq e (Classical.choose (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (exists_compactSupportReductionTower l E D.k (point D) (point D)
            (𝟙 (point D)) hk
            (Compactification.ofIsProper (𝟙 (point D)))))).2.2).2).2) ∧
      (∀ (C : DerivedCategory (scalarReductionSource l E (point D))) (n : ℕ),
        (coefficientConstantTowerEvaluation l E (point D) n).map (θ.hom.app C) ≫
            (e n).hom.app C ≫ (finiteRestrictedIdentity D l E n).hom.app C =
          (coefficientRestrictedEvaluationIso l E (point D) n).hom.app
              (A.reduction.obj C) ≫
            (scalarReductionDerivedRestriction l E (point D) n).map
              ((A.reductionEvaluation n).hom.app C)) ∧
      ∀ (m n : ℕ) (h : n ≤ m)
        (C : DerivedCategory (scalarReductionSource l E (point D))),
        (pbcTowerTransition (point D)
            (completedIntegralCommRingSheafUnrestricted l E (point D)) m n h).app
              (T.obj C) ≫ (e n).hom.app C =
          (e m).hom.app C ≫ compactSupportRestrictedTransition l E
            (Compactification.ofIsProper (𝟙 (point D))) m n h C := by
  sorry

end WeilConjectures.PodRawReconstruction
