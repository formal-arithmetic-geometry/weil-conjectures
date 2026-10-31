/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOrientationCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.NormalizedSmoothOrientationUnits
public import WeilConjectures.AlgebraicGeometry.SpecifiedIntegralUnitOrientation
public import WeilConjectures.AlgebraicGeometry.SmoothOrientationTransportSquare
public import WeilConjectures.AlgebraicGeometry.PurAdicReconstruction

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-smooth-orientation-purity-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans
attribute [local irreducible]
  RationalSmoothPurityCanonical.integralIso
  RationalSmoothPurityCanonical.integralSource
  RationalSmoothPurityCanonical.representative
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.orientation
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.commonSource
  RationalSmoothPurityCanonical.commonSourceComparison

section SpecifiedIntegralFamily
variable (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k)) [aX.IsOver (Spec (.of P.field.k))]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (d : ℕ) [SmoothOfRelativeDimension d aX]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := aX))
    (I : AdicPurityScalarNaturality.Data P.field P.coefficients aX d T)

/-- Forward and inverse reduction squares for the stipulated integral unit family.
The finite arrow is written as the actual `smoothPurityMap`, at every positive
quotient, so the formula pins the integral family to the specified finite gamma.
Source: normalized adic reconstruction, reduction equation
(blueprint: def-pod-smooth-orientation-purity-squares). -/
@[irreducible] def specifiedUnitPurityReductionSquare
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients) (n : ℕ) : Prop :=
  let U := smoothOrientationIntegralUnit P E
  let γ := (finiteTorConstructibleIntegral P.coefficients.l E.val X).ι.mapIso
      ((I.gamma E).app U) ≪≫ (I.targetRealization E).app U
  let Q := scalarReductionDerivedExtension P.coefficients.l E.val X n
  let hQ := purAdicSourceReduction P.field P.coefficients E.val aX d U.obj U.property n
  let zQ := purAdicTargetReduction P.field P.coefficients E.val aX d U.obj U.property n
  let γ' := canonicalSmoothPurityIso
    (purAdicFiniteSetting P.field P.coefficients E.val n) aX d
    ((scalarReductionDerivedExtension P.coefficients.l E.val
      (Spec (.of P.field.k)) n).obj U.obj)
    (purAdicReductionFiniteTor P.field P.coefficients E.val
      (Spec (.of P.field.k)) U.obj U.property n)
  Q.map γ.hom ≫ zQ = hQ ≫ γ'.hom ∧
    Q.map γ.inv ≫ hQ = zQ ≫ γ'.inv

/-- The coefficient square for this same unit family, after the displayed realization
functor. The functor is instantiated below by identity, rationalization, and the
actual common-stage realization; h and z are the recorded source comparison and
counit mate, and eta is the inverse of the very same gamma.
Source: integral extension and rational/common-stage passage
(blueprint: def-pod-smooth-orientation-purity-squares). -/
@[irreducible] def specifiedUnitPurityScalarSquare
    (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F)
    {W : Type (u + 2)} [Category.{u + 2} W]
    (R : AdicPurityScalarNaturality.Cat P.field P.coefficients F X ⥤ W) : Prop :=
  let U := smoothOrientationIntegralUnit P E
  let Q := AdicPurityScalarNaturality.scalar P.field P.coefficients I.scalarClosed E F h true
  let U' := (AdicPurityScalarNaturality.scalar P.field P.coefficients
    I.scalarClosed E F h false).obj U
  R.map (Q.map ((I.gamma E).hom.app U)) ≫ R.map ((I.b E F h).hom.app U) =
    R.map ((I.a E F h).hom.app U) ≫ R.map ((I.gamma F).hom.app U') ∧
  R.map (Q.map ((I.gamma E).inv.app U)) ≫ R.map ((I.a E F h).hom.app U) =
    R.map ((I.b E F h).hom.app U) ≫ R.map ((I.gamma F).inv.app U')

/-- Rationalization of the actual trace-normalized integral purity map, including
its source shift comparison and the counit-preserving exceptional comparison.
Source: rational purity transport, coefficient-unit specialization
(blueprint: def-pod-smooth-orientation-purity-squares). -/
@[irreducible] def specifiedUnitPurityRationalizationSquare
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (c : Compactification aX) : Prop :=
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ x : Spec (.of P.field.k),
      Invertible (P.coefficients.l : (Spec (.of P.field.k)).residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients (Spec (.of P.field.k)) x).invertible
  let PE := RationalSmoothPurityCanonical.stageSetting P E
  let U := smoothOrientationIntegralUnit P E
  let QX := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage PE) X
  let QY := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage PE) (Spec (.of P.field.k))
  let V := QY.obj U
  let U₀ := RationalSmoothPurityCanonical.representative PE V
  let γ := RationalSmoothPurityCanonical.integralIso PE aX c T d U₀
  let γ' := RationalSmoothPurityCanonical.rationalIso PE aX c T d V
  let hQ := (RationalSmoothPurityCanonical.rationalSourceComparison PE aX d V).symm
  let zQ := (T.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage PE)).b.app U₀
    ≪≫ (T.ring.operation c (.rational (AdicSmoothDualizing.fieldStage PE))).G.mapIso
      (eqToIso (RationalSmoothPurityCanonical.representative_eq PE V))
  smoothOrientationPuritySquare QX γ γ' hQ zQ

/-- The rational coefficient-field square for the specified canonical purity maps.
The common-stage clause below uses exactly its finite-field representative through
the recorded small-model scalar extension and common-stage inclusion.
Source: rational and common-stage purity, scalar comparison equation
(blueprint: def-pod-smooth-orientation-purity-squares). -/
@[irreducible] def specifiedRationalUnitPurityScalarSquare
    (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F)
    (c : Compactification aX)
    {W : Type (u + 2)} [Category.{u + 2} W]
    (R : sfRationalConstructibleCategory P.coefficients.l F.val X ⥤ W) : Prop :=
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ x : Spec (.of P.field.k),
      Invertible (P.coefficients.l : (Spec (.of P.field.k)).residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients (Spec (.of P.field.k)) x).invertible
  let PE := RationalSmoothPurityCanonical.stageSetting P E
  let PF := RationalSmoothPurityCanonical.stageSetting P F
  let U := AdicSmoothDualizing.rationalTwist PE (Spec (.of P.field.k)) (𝟙 _) 0
  let QX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage PE)
    (AdicSmoothDualizing.fieldStage PF) (IntermediateField.inclusion h) X
  let QY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage PE)
    (AdicSmoothDualizing.fieldStage PF) (IntermediateField.inclusion h) (Spec (.of P.field.k))
  let γ := RationalSmoothPurityCanonical.rationalIso PE aX c T d U
  let γ' := RationalSmoothPurityCanonical.rationalIso PF aX c T d (QY.obj U)
  let hQ := RationalSmoothPurityCanonical.sourceScalar P.coefficients.l E.val F.val
    (IntermediateField.inclusion h) aX d U
  let zQ := (ConstructibleExceptionalCoefficients.FieldComparison.b P.coefficients.l
    P.coefficients.Qbar (T.fields.rationalComparison c (AdicSmoothDualizing.fieldStage PE)
      (AdicSmoothDualizing.fieldStage PF) (IntermediateField.inclusion h))).app U
  smoothOrientationPuritySquare (QX ⋙ R) γ (R.mapIso γ')
    (R.mapIso hQ) (R.mapIso zQ)

/-- The common-stage extension square, with the literal finite-stage purity
representative, the canonical source comparison, and the exceptional common-stage
mate. Both directions use `commonIso`, not an existentially chosen common-stage map.
Source: rational and common-stage purity, common-stage identification
(blueprint: def-pod-smooth-orientation-purity-squares). -/
@[irreducible] def specifiedCommonUnitPuritySquare (c : Compactification aX) : Prop := by
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ x : Spec (.of P.field.k),
      Invertible (P.coefficients.l : (Spec (.of P.field.k)).residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients (Spec (.of P.field.k)) x).invertible
  let K := AdicSmoothDualizing.closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0
  let γ₀ := RationalSmoothPurityCanonical.smallModelIso
    (RationalSmoothPurityCanonical.stageSetting P K.stage) aX c T d K.obj
  dsimp only [RationalSmoothPurityCanonical.stageSetting,
    AdicSmoothDualizing.fieldIndex] at γ₀
  let Q := ConstructibleExceptionalCoefficients.commonInclusion
    P.coefficients.l P.coefficients.Qbar X K.stage
  let hQ := (RationalSmoothPurityCanonical.commonSourceComparison P.coefficients.l
    P.coefficients.Qbar aX d K).symm
  let zQ := (T.common.commonComparison c K.stage).b.app K.obj
  let γ' := RationalSmoothPurityCanonical.commonIso P aX c T d K
  exact smoothOrientationPuritySquare Q γ₀ γ' hQ zQ

end SpecifiedIntegralFamily

end WeilConjectures
