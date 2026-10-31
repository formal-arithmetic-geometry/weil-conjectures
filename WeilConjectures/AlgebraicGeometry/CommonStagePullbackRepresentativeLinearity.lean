/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Scalar multiplication of common-stage pullback representatives

Source: the Weil-structures paragraph of the all-stage open/closed triangle proof.
The finite-stage scalar identity is transported through the actual representative map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback
  GeneralAlgebraicallyClosedCoefficients.ofHom StageSystem.PairCategory.mkHom

attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] sfIntegralConstructibleLinear

/-- Cache the canonical scalar-localization linear structure at the named finite stage.
Source: the canonical rational stages of the common-stage coefficient category
(blueprint: lem-sf-common-stage-pullback-representative-linearity). -/
instance commonStageRepresentativeLinearity_stageLinear
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    Linear (Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)))
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  @ScalarLocalization.linear (Padic.coefficientExtensionIntegers l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)) inferInstance
    (sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) T)
    inferInstance inferInstance
    (sfIntegralConstructibleLinear l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) T)
    (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
attribute [local instance 5000] commonStageRepresentativeLinearity_stageLinear
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive

/-- The common-stage pullback formula respects a scalar represented in its coefficient field.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-common-stage-pullback-representative-linearity).
Proof: apply the specified representative formula to the scalar multiple of the arrow.
Linearity of rational pullback takes the scalar through its map. Bilinearity of
composition takes it through the source comparison and inverse target comparison.
Apply congruence for the actual common-stage representative constructor to this
finite-stage equality and substitute it into the specified map formula. Only this
one coefficient field is used, so no choice of a common enlargement is required. -/
theorem commonStageDerivedPullback_map_smul_of_linear
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y)
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (hlin : (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).Linear
        (Localization.Away (Padic.coefficientExtensionUniformizer l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))))
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)))
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    HEq ((commonStageDerivedPullback l Ω f).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ (a • r)))
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)
        L hP hQ
        (a • ((commonStagePullbackComparison l Ω f P L hP).hom ≫
          (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            f).map r ≫ (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).Linear
        (Localization.Away (Padic.coefficientExtensionUniformizer l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))) := hlin
    unfold commonStageDerivedPullback
    have hm := (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
      P Q L hP hQ (a • r)
    have hs := (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map_smul a r
    have hr :
        (commonStagePullbackComparison l Ω f P L hP).hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map (a • r) ≫
            (commonStagePullbackComparison l Ω f Q L hQ).inv =
          a • ((commonStagePullbackComparison l Ω f P L hP).hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map r ≫
            (commonStagePullbackComparison l Ω f Q L hQ).inv) := by
      rw [hs, Linear.smul_comp, Linear.comp_smul]
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      have ht := congrArg
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)
          L hP hQ) hr
      exact hm.trans (heq_of_eq ht)

end WeilConjectures
