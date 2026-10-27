/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.Paper.PurityCompositionCompatibleDncCharts
public import Sheaf.Paper.CompositionTensorMate
public import Sheaf.Paper.PurityCompositionComparisons
public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.ProjectionPurityAgreement
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

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
    (f : X ⟶ Y) [HasCompactification f] :=
  (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    ((ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient Y).symm ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso
          (smoothPurityUnitIso P.Coefficient Y).symm)

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

/-- The equality (**) in the actual pro-etale category. All compactifications and
compactness instances follow from the finite-type domain. Sigma is exactly the recorded
symmetry/theta/c-inverse map, rather than a newly supplied comparison.
Source: composition proof Step 1 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def ModelOrientationEquation (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := P.noetherian aZ
  letI := P.noetherian (g ≫ aZ)
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  letI := Dnc.compactifiable P (f ≫ g) aZ
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
      (P.modelOrientation (d + e) (f ≫ g) aZ).hom =
    (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.modelOrientation e g aZ))).hom ≫ (P.modelOrientationMu d e f (g ≫ aZ)).hom ∧
  (P.modelOrientationMu d e f (g ≫ aZ)).inv ≫
    (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.modelOrientation e g aZ))).inv ≫
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
      (P.modelOrientation (d + e) (f ≫ g) aZ).hom = 𝟙 (P.diagonalTwist X (d + e))

/-- The recorded ordered Gamma at the coefficient unit, enumerating every positive level.
Only the successor presentation of the existing finite datum changes.
Source: composition proof Steps 2--4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelOrderedGamma (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) [IsAffine B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ) :
    letI := (ProEtale.AffineSpacePurity.projection_geometry B r).2
    P.diagonalTwist (iteratedAffineLine B r) r ⟶
      P.diagonalDualizing (iteratedAffineLineProj B r) := by
  rcases P with ⟨F, C, E, n, hn⟩
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n => exact chartGamma F C E n B aB r

/-- The ordered coordinate morphism from the finite-coordinate affine model.
The outermost iterated-line coordinate is the last affine coordinate.
Source: composition proof Step 4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelOrderedCoordinates (B : Scheme.{u}) (r : ℕ) :
    DiagonalPasting.A r B ⟶ iteratedAffineLine B r :=
  (DiagonalPasting.pr r B).toIteratedAffineLine
    (fun i ↦ AffineSpace.coord B (ULift.up i.rev))

/-- The type of Gamma on the affine models, before asserting its ordered normalization.
Source: composition proof Step 4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelAffineGamma (P : PurityFiniteSetting.{u}) :=
  ∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ),
    letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
    P.diagonalTwist (DiagonalPasting.A r B) r ≅ P.diagonalDualizing (DiagonalPasting.pr r B)

/-- The actual exceptional-adjunction coordinate comparison, along an isomorphism
preserving the projection. No purity orientation occurs in this map.
Source: composition proof Steps 3--4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelCoordinateDualizing (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) [IsAffine B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (c : DiagonalPasting.A r B ≅ iteratedAffineLine B r)
    (hc : c.hom ≫ iteratedAffineLineProj B r = DiagonalPasting.pr r B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aB
  letI := ProEtale.AffineSpacePurity.tower_noetherian P B aB r
  letI := (ProEtale.AffineSpacePurity.projection_geometry B r).2
  letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
  letI : HasCompactification (c.hom ≫ iteratedAffineLineProj B r) :=
    HasCompactification.of_eq hc.symm
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) c.hom).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison (iteratedAffineLineProj B r)) ≪≫
    Dnc.pullComparison P c.hom (P.diagonalOrdinaryDualizing (iteratedAffineLineProj B r)) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A r B)).mapDerivedCategory.mapIso
        (P.diagonalEtaleLocality N c.hom (iteratedAffineLineProj B r) ≪≫
          eqToIso (by simp only [hc])) ≪≫
    (P.diagonalDualizingComparison (DiagonalPasting.pr r B)).symm

/-- Gamma is fixed by the recorded ordered comparison under the actual coordinate map.
The existential coordinate isomorphism has prescribed hom, so supplies no choice of frame.
Source: composition proof Steps 2--4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelGammaNormalization (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma) : Prop :=
  ∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ),
    ∃ (c : DiagonalPasting.A r B ≅ iteratedAffineLine B r)
      (hc : c.hom ≫ iteratedAffineLineProj B r = DiagonalPasting.pr r B),
      c.hom = modelOrderedCoordinates B r ∧
      ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) c.hom).leftDerivedFunctor.map
            (P.modelOrderedGamma B aB r) ≫ (P.modelCoordinateDualizing B aB r c hc N).hom =
          (P.modelOrientationTwistPullback c.hom (iteratedAffineLineProj B r ≫ aB) r).hom ≫
            (G B aB r).hom

/-- Gamma_0 is the identity after the actual exceptional and pullback identity
constraints. This states the unit convention on the ordered Gamma itself.
Source: composition proof Steps 4--5
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelGammaZeroNormalization (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB],
    P.modelOrderedGamma B aB 0 ≫ (P.diagonalDualizingComparison (𝟙 B)).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
        (((Etale.rightDerivedUpperShriekIsoOfIso
          (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
            (Etale.ordinaryFiniteUnit P.Coefficient B)).hom ≫
          ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
            (Etale.ordinaryFiniteUnit P.Coefficient B)).hom) = 𝟙 _

/-- The specified b_r is Lz* of Gamma inverse, followed by canonical Tate restriction.
Its source is the recorded standard zero-section invariant, with the actual unit and
site comparisons inserted; the diagonal orientation is not used to define b_r.
Source: composition proof Step 5
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelOrientationZero (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    (B : Scheme.{u}) [IsAffine B] (r : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ((Etale.ordinaryFinitePullback P.Coefficient (DiagonalPasting.zero r B)).mapIso
        (P.chartDualizingUnit (DiagonalPasting.pr r B))) ≪≫
    (Dnc.pullComparison P (DiagonalPasting.zero r B)
      (P.diagonalOrdinaryDualizing (DiagonalPasting.pr r B))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.zero r B)).leftDerivedFunctor.mapIso
        ((P.diagonalDualizingComparison (DiagonalPasting.pr r B)).symm ≪≫ (G B aB r).symm) ≪≫
    P.modelOrientationTwistPullback (DiagonalPasting.zero r B)
      (DiagonalPasting.pr r B ≫ aB) r

/-- The orientation of q is the base change of the rank-d Gamma inverse. The
base-change arrow is the inverse smooth exceptional mate in ordinary coordinates,
transported to the pro-etale category, followed by canonical Tate pullback.
Source: composition proof Steps 3--5
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def modelAffineQOrientation (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := DiagonalPasting.affineDimension d B
  letI := Dnc.compactifiable P (DiagonalPasting.pr d B) aB
  letI := Dnc.compactifiable P (DiagonalPasting.q d e B) (DiagonalPasting.pr e B ≫ aB)
  P.modelOrientationUnit (DiagonalPasting.q d e B) ≪≫
    P.diagonalDualizingComparison (DiagonalPasting.q d e B) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B)).mapDerivedCategory.mapIso
        (P.chartOrdinaryBaseChange d (DiagonalPasting.pr d B) aB
          (DiagonalPasting.pr e B) (DiagonalPasting.q d e B) (DiagonalPasting.first d e B)
          (DiagonalPasting.affineGeometry d e B).1).symm ≪≫
    (Dnc.pullComparison P (DiagonalPasting.first d e B)
      (P.diagonalOrdinaryDualizing (DiagonalPasting.pr d B))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.first d e B)).leftDerivedFunctor.mapIso
        ((P.diagonalDualizingComparison (DiagonalPasting.pr d B)).symm ≪≫ (G B aB d).symm) ≪≫
    P.modelOrientationTwistPullback (DiagonalPasting.first d e B)
      (DiagonalPasting.pr d B ≫ aB) d

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
      simp only [(DiagonalPasting.affineGeometry d e B).2.2.2.1]
      rfl) ≪≫
    (G B aB (d + e)).symm

/-- The first affine identity uses Gamma and the base-changed rank-d orientation,
not the final diagonal-orientation equality specialized to q.
Source: composition proof Step 4
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelAffineOrientationEquation (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] : Prop :=
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
  letI := Dnc.compactifiable P (DiagonalPasting.q d e B) (DiagonalPasting.pr e B ≫ aB)
  letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  ProEtale.CompositionTensorMate.sigma P.Coefficient
      (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) ≫
      (P.modelAffineTotalOrientation G B d e aB).hom =
    (P.compatibleTensorIso (P.modelAffineQOrientation G B d e aB)
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
          (P.modelOrientationUnit (DiagonalPasting.pr e B) ≪≫ (G B aB e).symm))).hom ≫
      (P.modelOrientationMu d e (DiagonalPasting.q d e B) (DiagonalPasting.pr e B ≫ aB)).hom

/-- The zero-section multiplication equation in the specified pro-etale coordinates.
Source: composition proof Step 5 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def ModelZeroOrientationEquation (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] : Prop :=
  P.compatibleNu d e B aB ≪≫ P.modelOrientationZero G B (d + e) aB =
    P.compatibleTensorIso (P.modelOrientationZero G B d aB)
      (P.modelOrientationZero G B e aB) ≪≫ P.modelOrientationPowerMul B d e

/-- The local beta-delta equation, before cancelling the alpha coordinate comparisons.
The maps beta are the actual normal-bundle orientations, without a choice of frames.
Source: composition proof Steps 6--7
(blueprint: def-pur-composition-model-orientation-coordinates).
-/
def ModelChartOrientationEquation (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT] : Prop :=
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  ∀ t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates,
    P.compatibleKappa d e f g aT ≪≫ P.chartDiagonalDelta (d + e) (f ≫ g) aT ≪≫
        P.chartDiagonalBeta (d + e) (f ≫ g) aT t =
      P.compatibleTensorIso
        (P.chartDiagonalDelta d f (g ≫ aT) ≪≫ P.chartDiagonalBeta d f (g ≫ aT) t)
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (P.chartDiagonalDelta e g aT ≪≫ P.chartDiagonalBeta e g aT t)) ≪≫
        P.modelOrientationMu d e f (g ≫ aT)

/-- In the actual conormal frames the three beta maps are the same b_r defined
from Gamma inverse. The middle equality includes pullback and the specified
standard-section base-change comparison, so all three maps live on U.
Source: composition proof Steps 5--6
(blueprint: def-pur-composition-model-orientation-coordinates). -/
def ModelChartBetaIdentification (P : PurityFiniteSetting.{u}) (G : P.ModelAffineGamma)
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT] : Prop :=
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  ∀ (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
    letI := (composition_compatible_tangent_normal P d e f g aT x y hx hy).2.1
    P.chartDiagonalBeta d f (g ≫ aT) t =
      P.chartNormalCoordinateComparison d f (g ≫ aT) x hx N ≪≫
        P.modelOrientationZero G U d (f ≫ g ≫ aT) ∧
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.chartDiagonalBeta e g aT t) ≪≫ P.modelOrientationTwistPullback f (g ≫ aT) e =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.chartNormalCoordinateComparison e g aT y hy N) ≪≫
        P.compatibleStandardPullback e f (g ≫ aT) ≪≫
          P.modelOrientationZero G U e (f ≫ g ≫ aT) ∧
    P.chartDiagonalBeta (d + e) (f ≫ g) aT t =
      P.chartNormalCoordinateComparison (d + e) (f ≫ g) aT
        (compatibleCompositeChart d e f g x y)
        (composition_compatible_tangent_normal P d e f g aT x y hx hy).2.2 N ≪≫
          P.modelOrientationZero G U (d + e) (f ≫ g ≫ aT)

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

/-- Source naturality with the eight canonical factors of the recorded source
identification; the same formula applies on the finite-Tor constructible subcategory.
Source: composition proof Step 2 (blueprint: def-pur-composition-model-orientation-coordinates).
-/
def ModelOrientationSourceNaturality (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  (∀ K : Scheme.proEtaleDerivedCategory Z P.Ring,
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K →
    P.CompositionSourceNormalized f g d e K (P.compositionSourceFixed f g d e K)) ∧
  ∀ (K L : Scheme.proEtaleDerivedCategory Z P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K →
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z L →
    ∀ a : K ⟶ L,
    ((P.compositionShiftedPullback (f ≫ g) (d + e)).map a) ≫
        (P.compositionSourceIdentification f g d e L).hom =
      (P.compositionSourceIdentification f g d e K).hom ≫
        ((P.compositionShiftedPullback g e) ⋙ (P.compositionShiftedPullback f d)).map a

/-- All model identities, chart identities, canonical source naturality and the global
descent assertion. Gamma is normalized by the recorded ordered affine comparison;
its inverse defines both the affine and the zero-section orientation equations.
Source: composition proof Steps 1--2
(blueprint: def-pur-composition-model-orientation-coordinates).
-/
def CompositionModelOrientationConclusion (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI : Y.Over (Spec (.of P.field.k)) := ⟨g ≫ aZ⟩
  ∃ G : P.ModelAffineGamma,
  P.ModelGammaNormalization G ∧
  P.ModelGammaZeroNormalization ∧
  ModelOrientationSourceNaturality P d e f g ∧
  (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1 ∧
  (∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB],
    ModelAffineOrientationEquation P G B d e aB ∧
      ModelZeroOrientationEquation P G B d e aB) ∧
  (∀ (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
    (f' : U ⟶ V) (g' : V ⟶ T)
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
      ModelChartOrientationEquation P d e f' g' aT ∧
        ModelChartBetaIdentification P G d e f' g' aT) ∧
  ModelOrientationDetection.{u, w} P X (d + e) ∧
  ModelOrientationEquation P d e f g aZ

end WeilConjectures.PurityFiniteSetting
