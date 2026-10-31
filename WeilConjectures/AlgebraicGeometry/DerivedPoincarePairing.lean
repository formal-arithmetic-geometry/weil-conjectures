/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.SixFunctorMixedSupportCupProduct
public import WeilConjectures.AlgebraicGeometry.SixFunctorDualNotation
public import WeilConjectures.AlgebraicGeometry.SixFunctorOrientationFamily
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.CommonStageCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.PairingData
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # The derived Poincare pairing

Source: current blueprint, sec-six-functors/sk-thm-sf-identification/def-sf-pairing.md
(blueprint: def-sf-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- Evaluation in the order K tensor its coefficient dual, twisted by a coefficient line.
The braiding changes the right-tensor adjunction convention into the displayed
left-tensor adjunction convention. The remainder is inverse associator, evaluation
whiskered by the line, and the coefficient left unitor.
Source: def-sf-pairing, ev_K(d) display (blueprint: def-sf-pairing). -/
def sfPairingTwistedEvaluation {B : Type v} [Category.{w} B]
    {H : Bᵒᵖ × B ⥤ B} (M : CoefficientClosedStructure H)
    (s : @SymmetricCategory B _ M.monoidal) (K T : B) :
    M.tensor.obj (K, M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), T)) ⟶ T :=
  (M.monoidal.associator _ _ _).inv ≫
    M.tensor.map (Prod.mkHom
      ((s.braiding K _).hom ≫ M.evaluation K M.monoidal.tensorUnit) (𝟙 T)) ≫
    (M.monoidal.leftUnitor T).hom

/-- The canonical comparison from the normalized tensor to a closed presentation.
It is the inverse normalized transpose of the closed adjunction unit, so it
introduces neither an arbitrary tensor map nor a choice of isomorphism.
Source: the tensor/evaluation coordinates in def-sf-pairing
(blueprint: def-sf-pairing). -/
def sfPairingTensorComparison {B : Type v} [Category.{w} B] [Preadditive B]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} {T : B × B ⥤ B}
    (M : SixFunctorClosedDomain P Q H) (A : PodPartialClosed T Q H)
    (K L : P.FullSubcategory) :
    T.obj (K.obj, L.obj) ⟶ (M.closed.tensor.obj (K, L)).obj :=
  (A.transpose K.obj
    ⟨(op L.obj, (M.closed.tensor.obj (K, L)).obj),
      M.homPermitted L (M.closed.tensor.obj (K, L))⟩).symm
    ((M.closed.transpose K L (M.closed.tensor.obj (K, L)) (𝟙 _)).hom)

/-- The geometric alternative required for global Verdier duality: properness,
or a smooth separated geometrically connected finite-type model over k₀.
The isomorphism is over k, and the second alternative does not require properness.
Source: the geometric hypotheses of def-sf-pairing (blueprint: def-sf-pairing). -/
def SfPairingGlobalGeometry {D : FiniteFieldDatum.{u}} (X : SixFunctorSpace D) : Prop :=
  IsProper X.obj.hom ∨ ∃ X₀ : Over (Spec (.of D.k₀)),
    Smooth X₀.hom ∧ IsSeparated X₀.hom ∧ LocallyOfFiniteType X₀.hom ∧
    QuasiCompact X₀.hom ∧ GeometricallyConnected X₀.hom ∧
    Nonempty (X.obj ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀)

namespace SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

/-- The orientation line Λ_X(d)[2d] in the existing integral finite-Tor domain.
Source: shifted coefficient-line convention (blueprint: def-sf-pairing). -/
def sfPairingIntegralLine (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D) (d : ℕ) :
    (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory :=
  ⟨sfOrientationIntegralLineOn D C E X d,
    @sfOrientationIntegralComplex_mem C.l _ E _ _ _ X.obj.left
      (dlAdicGeometricResidueInvertible D C X.obj.left) d⟩

/-- K^∨(d)[2d] formed by the actual completed tensor. Its closed-presentation
comparison is the inverse-transpose construction sfPairingTensorComparison; the line's
single-functor shift identification is sfOrientationIntegralShiftIso.
Source: the second input of beta_K (blueprint: def-sf-pairing). -/
def sfPairingIntegralDualTwist (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (⟨(constructibleIntegralTensor C.l E X.obj.left).obj
      (((S.integralCoefficientDual X).obj (op K)).obj, (S.sfPairingIntegralLine X d).obj),
    Eq.mp (congrArg (fun P ↦ P ((constructibleIntegralTensor C.l E X.obj.left).obj
      (((S.integralCoefficientDual X).obj (op K)).obj,
        (S.sfPairingIntegralLine X d).obj)).obj)
      (integral_residue_tor D C.l C.different E X.obj.left).2)
      ((constructibleIntegralTensor C.l E X.obj.left).obj
        (((S.integralCoefficientDual X).obj (op K)).obj,
          (S.sfPairingIntegralLine X d).obj)).property⟩ :
      (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory)

/-- Completed twisted evaluation on the actual stage tensor. The canonical
comparison is followed by inverse associator, the adjunction evaluation tensored
with the shifted line, and left unitor. In particular evaluation is not an input.
Source: the middle arrow of beta_K (blueprint: def-sf-pairing). -/
def sfPairingIntegralEvaluation (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  eqToHom (congrArg (fun H ↦ (H.obj K.obj).obj
      (S.sfPairingIntegralDualTwist X d K).obj)
    (S.higher.integralTensorNormalization X)) ≫
  sfPairingTensorComparison (S.integralClosed X) (podIntegralClosed C.l E X.obj.left)
    K (S.sfPairingIntegralDualTwist X d K) ≫
  ((S.integralClosed X).closed.tensor.map (Prod.mkHom (𝟙 K)
    (ObjectProperty.homMk
      (sfPairingTensorComparison (S.integralClosed X) (podIntegralClosed C.l E X.obj.left)
        ((S.integralCoefficientDual X).obj (op K)) (S.sfPairingIntegralLine X d))))).hom ≫
  (sfPairingTwistedEvaluation (S.integralClosed X).closed
    (S.integralClosed X).symmetric K (S.sfPairingIntegralLine X d)).hom

/-- The integral derived Poincare pairing of point complexes. We use the canonical
shift-inside-the-line representative of RΓ(K^∨(d))[2d]. The displayed cup is the
inverse point tensorator followed by projection and the pull/direct counit.
Its target is sent by compact support of twisted evaluation to the shifted
coefficient line; the final arrow is the orientation-normalized exceptional counit.
Source: all three arrows of def-sf-pairing (blueprint: def-sf-pairing). -/
def integralPoincarePairing (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] (d : ℕ)
    [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (_hconnected : GeometricallyConnected X.obj.hom)
    (_hpure : X.obj.left.IsPureDimension d) (_hglobal : SfPairingGlobalGeometry X)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory)
    (_hperfect : IsIntegralCoefficientSitePerfect C.l E X.obj.left
      ((S.integralCoefficientDual X).obj (op K)).obj.obj) :=
  S.integralPairingCup X c ⟨K.obj.obj, K.property⟩
      ⟨(S.sfPairingIntegralDualTwist X d K).obj.obj,
        (S.sfPairingIntegralDualTwist X d K).property⟩ ≫
    (pointFibreIntegralAmbient D C.l E).map
      ((S.higher.integral.support (sixFunctorStructure X) c).map
        (S.sfPairingIntegralEvaluation X d K)).hom ≫
    S.integralNormalizedSmoothTrace O X d c

/-- The same finite-Tor object with a single full-subcategory layer.
Source: finite input convention (blueprint: def-sf-pairing). -/
def sfPairingFiniteTorInput (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    (K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory) :
    finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left := ⟨K.obj.obj, K.property⟩

/-- Reduction of the actual completed orientation line, with A5 finite-Tor membership.
Source: finite shifted line (blueprint: def-sf-pairing). -/
def sfPairingFiniteLine (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D) (d : ℕ) :
    (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory :=
  ⟨sfOrientationReducedLine D C E m X d,
    (S.reductionClosedComparison m X).domain (S.sfPairingIntegralLine X d)⟩

/-- Finite K^∨(d)[2d] formed with the recorded finite-Tor tensor.
Source: finite second input (blueprint: def-sf-pairing). -/
def sfPairingFiniteDualTwist (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory) :=
  (⟨pairingFiniteInput X (((S.finiteTensorDomainStage X).obj
    (S.sfPairingFiniteTorInput X ((S.finiteCoefficientDual X).obj (op K)))).obj
      (S.sfPairingFiniteTorInput X (S.sfPairingFiniteLine X d))),
    (((S.finiteTensorDomainStage X).obj
      (S.sfPairingFiniteTorInput X ((S.finiteCoefficientDual X).obj (op K)))).obj
        (S.sfPairingFiniteTorInput X (S.sfPairingFiniteLine X d))).property⟩ :
    (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)

/-- The finite tensor comparison is inverse intrinsic transposition of the
closed adjunction unit, with full-subcategory inclusions made explicit.
Source: finite evaluation coordinates (blueprint: def-sf-pairing). -/
def sfPairingFiniteTensorComparison (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    (K L : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory) :=
  ((finiteIntrinsicClosed C.l E X.obj.left m).transpose K.obj.obj L.obj.obj
    ((S.finiteClosed X).closed.tensor.obj (K, L)).obj.obj).symm
    (((S.finiteClosed X).closed.transpose K L
      ((S.finiteClosed X).closed.tensor.obj (K, L)) (𝟙 _)).hom.hom)

/-- Finite twisted evaluation, using the normalized finite tensor and the
coefficient-dual adjunction, inverse associator and left unitor.
Source: finite middle arrow (blueprint: def-sf-pairing). -/
def sfPairingFiniteEvaluation (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory) :
    pairingFiniteInput X (((S.finiteTensorDomainStage X).obj (S.sfPairingFiniteTorInput X K)).obj
      (S.sfPairingFiniteTorInput X (S.sfPairingFiniteDualTwist X d K))) ⟶
        (S.sfPairingFiniteLine X d).obj :=
  ObjectProperty.homMk (eqToHom (S.finiteTensorNormalization X (S.sfPairingFiniteTorInput X K)
      (S.sfPairingFiniteTorInput X (S.sfPairingFiniteDualTwist X d K))) ≫
    S.sfPairingFiniteTensorComparison X K (S.sfPairingFiniteDualTwist X d K) ≫
    ((S.finiteClosed X).closed.tensor.map (Prod.mkHom (𝟙 K)
      (ObjectProperty.homMk (ObjectProperty.homMk
        (eqToHom (S.finiteTensorNormalization X
          (S.sfPairingFiniteTorInput X ((S.finiteCoefficientDual X).obj (op K)))
          (S.sfPairingFiniteTorInput X (S.sfPairingFiniteLine X d))) ≫
        S.sfPairingFiniteTensorComparison X ((S.finiteCoefficientDual X).obj (op K))
          (S.sfPairingFiniteLine X d)))))).hom.hom ≫
    (sfPairingTwistedEvaluation (S.finiteClosed X).closed (S.finiteClosed X).symmetric
      K (S.sfPairingFiniteLine X d)).hom.hom)

/-- Finite derived Poincare pairing, with the shift inside the orientation line.
The three factors are the coefficient-valued cup, compact-support image of
canonical twisted evaluation, and normalized smooth trace.
Source: the finite instance of beta_K (blueprint: def-sf-pairing). -/
def finitePoincarePairing (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] (d : ℕ)
    [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (_hconnected : GeometricallyConnected X.obj.hom)
    (_hpure : X.obj.left.IsPureDimension d) (_hglobal : SfPairingGlobalGeometry X)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)
    (_hperfect : IsFiniteCoefficientSitePerfect.{u, u} C.l E X.obj.left m
      ((S.finiteCoefficientDual X).obj (op K)).obj.obj) :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (m + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Functor.mapDerivedCategory.{u + 2, u + 1, u + 1, u + 1, u + 2, u + 2}
    (pointFiniteSections D.k (Padic.coefficientExtensionRing C.l E (m + 1)))
  SixFunctorDatum.finitePairingCup.{u} S X c (S.sfPairingFiniteTorInput X K)
      (S.sfPairingFiniteTorInput X (S.sfPairingFiniteDualTwist X d K)) ≫
    F.map ((@SixFunctorPushStage.support.{u, u + 2, u + 2} D
    (fun Y ↦ sixFunctorFiniteCategory D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) Y)
    (fun Y ↦ inferInstanceAs (Category.{u + 2} (sixFunctorFiniteCategory D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) Y)))
    S.finite X (sixFunctorPoint D) (sixFunctorStructure X) c).map
      (S.sfPairingFiniteEvaluation X d K)).hom ≫
    SixFunctorDatum.finiteNormalizedSmoothTrace.{u} O X d c

/-- The rational shifted orientation line is the localization of the integral line.
Source: rational shifted line (blueprint: def-sf-pairing). -/
def sfPairingRationalLine (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D) (d : ℕ) :
    (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory :=
  ⟨(sfRationalConstructibleLocalization C.l E X.obj.left).obj
    (S.sfPairingIntegralLine X d).obj, trivial⟩

/-- Rational K^∨(d)[2d] formed with the actual rationalized tensor.
Source: rational second input (blueprint: def-sf-pairing). -/
def sfPairingRationalDualTwist (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (⟨(rationalDerivedTensor C.l E X.obj.left).obj
    (((S.rationalCoefficientDual X).obj (op K)).obj,
      (S.sfPairingRationalLine X d).obj), trivial⟩ :
    (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory)

/-- Rational twisted evaluation, using the uniquely localized normalized transpose.
Source: rational middle arrow (blueprint: def-sf-pairing). -/
def sfPairingRationalEvaluation (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  eqToHom (congrArg (fun H ↦ (H.obj K.obj).obj
      (S.sfPairingRationalDualTwist X d K).obj)
    (S.higher.rationalTensorNormalization X)) ≫
  sfPairingTensorComparison (S.rationalClosed X) (podRationalClosed C.l E X.obj.left)
    K (S.sfPairingRationalDualTwist X d K) ≫
  ((S.rationalClosed X).closed.tensor.map (Prod.mkHom (𝟙 K)
    (ObjectProperty.homMk
      (sfPairingTensorComparison (S.rationalClosed X) (podRationalClosed C.l E X.obj.left)
        ((S.rationalCoefficientDual X).obj (op K)) (S.sfPairingRationalLine X d))))).hom ≫
  (sfPairingTwistedEvaluation (S.rationalClosed X).closed (S.rationalClosed X).symmetric
    K (S.sfPairingRationalLine X d)).hom

/-- Rational Poincare pairing: actual rational cup, support of twisted evaluation,
and the rational orientation/counit trace. The line carries the even shift.
Source: the rational instance of beta_K (blueprint: def-sf-pairing). -/
def rationalPoincarePairing (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] (d : ℕ)
    [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (_hconnected : GeometricallyConnected X.obj.hom)
    (_hpure : X.obj.left.IsPureDimension d) (_hglobal : SfPairingGlobalGeometry X)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory)
    (_hperfect : IsSfRationalCoefficientSitePerfect C.l E X.obj.left
      ((S.rationalCoefficientDual X).obj (op K)).obj) :=
  S.rationalPairingCup X c K.obj (S.sfPairingRationalDualTwist X d K).obj ≫
    (pointRationalFibre D C.l C.different E ⋙ (DerivedCategory.pointFiniteDimensional E).ι).map
      ((S.higher.rational.support (sixFunctorStructure X) c).map
        (S.sfPairingRationalEvaluation X d K)) ≫ S.rationalNormalizedSmoothTrace O X d c

/-- The common-stage shifted line, represented at the canonical least coefficient field.
Source: common-stage shifted line (blueprint: def-sf-pairing). -/
def sfPairingCommonLine (_S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D) (d : ℕ) :
    (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory :=
  ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := C.l) (Ω := C.Qbar) (Y := X.obj.left)
    (Padic.finiteCoefficientBase C.l C.Qbar)).obj
      ((sfRationalConstructibleLocalization C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
          (Padic.finiteCoefficientBase C.l C.Qbar)) X.obj.left).obj
            (sfOrientationIntegralLineOn D C
              (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
                (Padic.finiteCoefficientBase C.l C.Qbar)) X d)), trivial⟩

/-- Common-stage K^∨(d)[2d], with the datum's existing coefficient dual.
Source: common-stage second input (blueprint: def-sf-pairing). -/
def sfPairingCommonDualTwist (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (⟨(commonStageDerivedTensor C.l C.Qbar X.obj.left).obj
    (((S.commonStageCoefficientDual X).obj (op K)).obj,
      (S.sfPairingCommonLine X d).obj), trivial⟩ :
    (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory)

/-- Common-stage twisted evaluation is formed with the common-finite-stage
normalized transpose, followed by the closed associator/evaluation/unitor composite.
Source: common-stage middle arrow (blueprint: def-sf-pairing). -/
def sfPairingCommonEvaluation (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (d : ℕ)
    (K : (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  eqToHom (congrArg (fun H ↦ (H.obj K.obj).obj
      (S.sfPairingCommonDualTwist X d K).obj)
    (S.closure.commonStageTensorNormalization X)) ≫
  sfPairingTensorComparison (S.commonClosed X) (podCommonClosed C.l C.Qbar X.obj.left)
    K (S.sfPairingCommonDualTwist X d K) ≫
  ((S.commonClosed X).closed.tensor.map (Prod.mkHom (𝟙 K)
    (ObjectProperty.homMk
      (sfPairingTensorComparison (S.commonClosed X) (podCommonClosed C.l C.Qbar X.obj.left)
        ((S.commonStageCoefficientDual X).obj (op K)) (S.sfPairingCommonLine X d))))).hom ≫
  (sfPairingTwistedEvaluation (S.commonClosed X).closed (S.commonClosed X).symmetric
    K (S.sfPairingCommonLine X d)).hom

/-- Algebraically closed coefficient Poincare pairing, formed with the actual
common-stage cup and realized in coefficient complexes before the normalized trace.
All inputs and arrows retain their existing common-finite-field transitions.
Source: the common-stage instance of beta_K (blueprint: def-sf-pairing). -/
def commonStagePoincarePairing (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] (d : ℕ)
    [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (_hconnected : GeometricallyConnected X.obj.hom)
    (_hpure : X.obj.left.IsPureDimension d) (_hglobal : SfPairingGlobalGeometry X)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory)
    (_hperfect : IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left
      ((S.commonStageCoefficientDual X).obj (op K)).obj) :=
  S.commonPairingCup X c K.obj (S.sfPairingCommonDualTwist X d K).obj ≫
    (pointQbarFibre D C.l C.different C.Qbar ⋙
      DerivedCategory.pointFdQbarRealization C.l C.Qbar).map
      ((S.closure.commonStage.support (sixFunctorStructure X) c).map
        (S.sfPairingCommonEvaluation X d K)) ≫ S.commonNormalizedSmoothTrace O X d c

end SixFunctorDatum

/-- A pairing of point complexes is perfect precisely when its tensor-Hom
adjoint D → RHom(C, Λ) is invertible. No separate perfectness assumption on
C or D is imposed. The braiding implements the argument order of the right
closed adjunction.
Source: the final sentence of def-sf-pairing (blueprint: def-sf-pairing). -/
def IsSfPerfectPairing {B : Type v} [Category.{w} B]
    {H : Bᵒᵖ × B ⥤ B} (M : CoefficientClosedStructure H)
    (s : @SymmetricCategory B _ M.monoidal) (C D : B)
    (b : M.tensor.obj (C, D) ⟶ M.monoidal.tensorUnit) : Prop :=
  letI := M.monoidal
  letI := s
  letI : MonoidalClosed B :=
    ⟨fun X ↦ ⟨Prod.sectR (op X) B ⋙ H,
      (M.adjunction X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X).symm⟩⟩
  CategoryTheory.MonoidalClosed.IsPerfectPairing b

end WeilConjectures
