/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CompositionTensorMate
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityAgreement

/-! # Affine zero-section orientations and descent

Source: main-20261015, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence.proof.md, Steps 1--2.
(blueprint: def-pur-composition-model-orientation-coordinates).

All tensor, pullback, exceptional and orientation maps below are the recorded canonical
maps. The auxiliary definitions only express their coefficient-unit and site coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Concatenate the ordered positive shifted Tate powers, without swapping their blocks.
Source: composition proof Step 2 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientationPowerMul (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (d e : ℕ) :=
  (compatibleComparisonTensor P.Coefficient B
    (P.diagonalTwistEtale B d) (P.diagonalTwistEtale B e)).symm ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates B d e).symm

/-- The canonical restriction of the shifted Tate power, through the exact site comparison.
Source: composition proof Step 2 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientationTwistPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ Spec (.of P.field.k)) (e : ℕ) :=
  Dnc.pullComparison P f (P.diagonalTwistEtale Y e) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates
          (Etale.projectiveLineTraceTransport P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level)
            P.Coefficient P.diagonalExponent_annihilates)
          f (P.diagonalExponent_isUnit aY) e)

/-- Mu is tensor-power concatenation after canonical Tate pullback. The positive powers
already carry their even shifts, so the same composite includes shift addition.
Source: composition proof Step 2 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientationMu (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (aY : Y ⟶ Spec (.of P.field.k)) :=
  P.compatibleTensorIso (Iso.refl (P.diagonalTwist X d))
    (P.modelOrientationTwistPullback f aY e) ≪≫ P.modelOrientationPowerMul X d e

/-- The coefficient-unit change from the tensor-mate omega to the diagonal omega.
It applies the standing exceptional functor to the specified comparison-unit isomorphism.
Source: composition proof Step 1 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientationUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    ProEtale.CompositionTensorMate.omega P.Coefficient f ≅ P.diagonalDualizing f :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient f
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  (ProEtale.rightDerivedUpperShriek P.Coefficient f).mapIso
    ((ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient Y).symm ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso
          (smoothPurityUnitIso P.Coefficient Y).symm) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} P.Coefficient)
            (HasCompactification.compactification f))).rightAdjointUniq
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).app _).symm

/-- The specified diagonal orientation in the tensor-mate coefficient-unit coordinates.
Source: composition proof Step 1 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientation (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P f aY
  P.modelOrientationUnit f ≪≫ P.diagonalDualizingObject d f aY

/-- The type of Gamma on the affine models, before asserting its ordered normalization.
Source: composition proof Step 4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelAffineGamma (P : PurityFiniteSetting.{u}) :=
  ∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ),
    letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
    P.diagonalTwist (DiagonalPasting.A r B) r ≅ P.diagonalDualizing (DiagonalPasting.pr r B)

/-- Gamma inverse for the total projection, in the tensor-mate omega coordinates.
The equality q P_e=P_(d+e) is only a transport of the exceptional target.
Source: composition proof Step 4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelAffineTotalOrientation (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
  letI := Dnc.compactifiable P (DiagonalPasting.q d e B) (DiagonalPasting.pr e B ≫ aB)
  letI := Dnc.compactifiable P (DiagonalPasting.pr (d + e) B) aB
  P.modelOrientationUnit (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) ≪≫
    eqToIso (by
      simp only [(DiagonalPasting.affineGeometry d e B).2.2.2.1]) ≪≫
    (G B aB (d + e)).symm

/-- Remove the common even shift of T_X, retaining its specified Tate-power object.
Source: composition proof Step 8 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def modelOrientationUnshifted (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℕ) :=
  (P.diagonalTwist X r)⟦-(2 * (r : ℤ))⟧

/-- Concentration, rank one, and detection on any given Zariski covering. The last
clause is precisely injectivity on automorphisms, including the empty covering.
Source: composition proof Steps 8--9
(blueprint: def-pur-composition-model-orientation-coordinates).
-/
def ModelOrientationDetection (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℕ) : Prop :=
  letI : TopologicalSpace P.Coefficient := ⊥
  letI : DiscreteTopology P.Coefficient := ⟨rfl⟩
  _root_.DerivedCategory.homologyConcentratedIn 0 0 (P.modelOrientationUnshifted X r) ∧
  ((ProEtale.finiteCoefficientRealization X P.Coefficient).obj
    ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      (P.modelOrientationUnshifted X r))).IsFiniteLocallyFreeOfRank 1 ∧
  ∀ (I : Type w) (U : I → X.Opens), iSup U = ⊤ →
    Function.Injective (fun a : Aut (P.diagonalTwist X r) ↦
      fun i : I ↦ (ProEtale.upperStar
        (ModuleCat.{u + 1} P.Coefficient) (U i).ι).mapDerivedCategory.mapIso a)

end WeilConjectures.PurityFiniteSetting
