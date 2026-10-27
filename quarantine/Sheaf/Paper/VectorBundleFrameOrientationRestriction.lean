module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.ProjectionPurityAgreement
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.DiagonalOrientationRefinement
public import Sheaf.Paper.SectionReesBaseChangeEtale
public import Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.AffineTargetDiagonalDnc
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import Sheaf.Paper.TraceTransposeBaseChange
import Sheaf.Paper.BoundedSiteExchangeTransposes
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison

/-! # Restriction of vector-bundle orientation to linear frames

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-vector-bundle.proof.md, Step 3.
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction).

All maps below use the fixed finite coefficient realization. The affine coordinate
model is the published ordered tower, with its coordinate-preserving isomorphism to
AffineSpace (ULift (Fin d)). No purity comparison is used to define a transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
namespace FrameOrientation

/-- Smoothness supplied by the recorded bundle-frame geometry, without an assumption
on the absolute separatedness of the base. Source: vector-bundle proof, Step 1
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
instance bundleSmooth (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    letI := P.noetherian aS
    SmoothOfRelativeDimension d (VectorBundleZeroSection.π S d F) :=
  letI := P.noetherian aS
  (VectorBundleZeroSection.finite_type_frames P.field.k S aS d F).choose_spec.2.2.2.2.2.1

/-- The ordinary integration adjunct with its canonical Tate source identification.
Source: vector-bundle proof, Step 3, actual integration transpose
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def adjunctEtale (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := P.noetherian aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π S d F) aS
  (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
    (VectorBundleZeroSection.π S d F) (P.diagonalExponent_isUnit aS) d).inv ≫
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (VectorBundleZeroSection.π S d F)).homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)

/-- P_pi is the comparison image of the actual ordinary integration adjunct, followed
by the fixed comparison-unit identification of the exceptional target.
Source: vector-bundle proof, Step 3; vector-integration-site-comparison
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def adjunct (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := P.noetherian aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π S d F) aS
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    (VectorBundleZeroSection.scheme S d F)).mapDerivedCategory.map
      (adjunctEtale P S aS d F) ≫
    (P.diagonalDualizingComparison (VectorBundleZeroSection.π S d F)).inv

/-- Exceptional exchange for a smooth Cartesian square, in the actual finite
exceptional target coordinates. The only maps are comparison units and the mate
of inverse compact-support exchange. Source: vector-bundle proof, Steps 2--4
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def rho (P : PurityFiniteSetting.{u}) {X Y X' Y' : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f' : X' ⟶ Y') [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (aY' : Y' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b) :=
  letI := Dnc.compactifiable P f aY
  letI := Dnc.compactifiable P f' aY'
  (OrientationRefinement.pull P a).mapIso (P.diagonalDualizingComparison f) ≪≫
    Dnc.pullComparison P a (P.diagonalOrdinaryDualizing f) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.mapIso
        (P.chartOrdinaryBaseChange d f aY b f' a sq) ≪≫
    (P.diagonalDualizingComparison f').symm

/-- The actual affine integration adjunct P_p, using the normalized ordered counit.
Source: vector-bundle proof, Steps 3 and 6
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def affineAdjunct (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) :=
  letI := P.noetherian aB
  letI := affineTraceNoetherian B d
  letI := Dnc.compactifiable P (affineTraceProjection B d) aB
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    (affineTraceTower B d)).mapDerivedCategory.map
      (P.diagonalAffineMate
        (Etale.projectiveLineTraceTransport P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates)
        (Etale.projectiveLineTraceDatum P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates)
        B (P.diagonalExponent_isUnit aB) d) ≫
    (P.diagonalDualizingComparison (affineTraceProjection B d)).inv

/-- The zero-section integration adjunct is invertible, including the empty base
and rank zero. Source: vector-bundle proof, Step 2; cor-pur-vector-bundle-purity
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction).

Proof: ordinary vector purity makes the actual integration adjunct invertible
at the coefficient unit. Its canonical Tate comparisons are isomorphisms.
Pullback along the zero section preserves isomorphisms. Thus the composite
vectorBetaInverse, consisting of this pullback and Tate restriction, is invertible. -/
theorem zeroAdjunct_isIso (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    IsIso (OrientationRefinement.vectorBetaInverse P B aB d F) := by
  sorry

/-- Beta is the inverse of the ACTUAL integration adjunct pulled to zero, transported
from the canonical conormal bundle model by section exchange. No diagonal orientation
occurs in this definition. Source: vector-bundle proof, Steps 2 and 6
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def normalBeta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (h : X ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian (h ≫ aY)
  letI := (chartDiagonalNormalBundle d h).1
  let g := pullback.fst h h
  let z := pullback.diagonal h
  let F := ConormalGradedAlgebra.piece z 1
  let he := (chartNormal_model_exists d h).exists.choose_spec
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g z) :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d g z (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d g (h ≫ aY) z (pullback.diagonal_fst h)
  letI := Dnc.invertibleExponent P (Scheme.Hom.normalConeProj g z ≫ (h ≫ aY))
  letI := (Etale.vectorIntegration_geometry X d F).1
  letI := (Etale.vectorIntegration_geometry X d F).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π X d F) (h ≫ aY)
  letI := zeroAdjunct_isIso P X (h ≫ aY) d F
  Dnc.normalComparison P d g (h ≫ aY) z (pullback.diagonal_fst h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X).symm.app _ ≪≫
        Dnc.sectionBaseChange P.Coefficient d (Scheme.Hom.normalConeProj g z)
          (IsPullback.of_horiz_isIso
            ⟨he.2.1.trans (Category.comp_id _).symm⟩)
          z.normalConeZeroSection (VectorBundleZeroSection.zero X d F)
          (he.2.2.trans (Category.id_comp _).symm) ≪≫
        (asIso (OrientationRefinement.vectorBetaInverse P X (h ≫ aY) d F)).symm)

/-- The specified global diagonal orientation on the bundle, with its geometric
properties derived rather than assumed. Source: vector-bundle proof, Step 1
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def orientation (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := P.noetherian aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := bundleSmooth P S aS d F
  P.diagonalDualizingObject d (VectorBundleZeroSection.π S d F) aS

/-- Rho includes the inverse linear frame; it is the actual exceptional exchange
for vectorIntegrationChart. Source: vector-bundle proof, Steps 2--3
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def frameRho (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :=
  letI := P.noetherian aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := bundleSmooth P S aS d F
  fun e : VectorBundleZeroSection.Trivialization S d F U.1 ↦
    rho P d (VectorBundleZeroSection.π S d F) aS
      (affineTraceProjection U.1.toScheme d) (U.1.ι ≫ aS)
      (Etale.vectorIntegrationChart S d F U.1 e) U.1.ι
      (Etale.vectorIntegrationChart_isPullback S d F U.1 e)

/-- Tate restriction with exactly the same inverse frame as rho.
Source: vector-bundle proof, Steps 2--3
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def frameTate (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :=
  letI := P.noetherian aS
  fun e : VectorBundleZeroSection.Trivialization S d F U.1 ↦
    OrientationRefinement.tate P (Etale.vectorIntegrationChart S d F U.1 e)
      (VectorBundleZeroSection.π S d F ≫ aS) d

/-- Tau followed after the pulled orientation and inverse rho, in diagram order.
Source: vector-bundle proof, first displayed restriction formula
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def frameOrientation (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :=
  letI := P.noetherian aS
  fun e : VectorBundleZeroSection.Trivialization S d F U.1 ↦
    (frameRho P S aS d F U e).inv ≫
      (OrientationRefinement.pull P (Etale.vectorIntegrationChart S d F U.1 e)).map
        (orientation P S aS d F).hom ≫ (frameTate P S aS d F U e).hom

/-- Rho followed after the pulled integration adjunct and inverse tau.
Source: vector-bundle proof, second displayed restriction formula
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def frameAdjunct (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :=
  letI := P.noetherian aS
  fun e : VectorBundleZeroSection.Trivialization S d F U.1 ↦
    (frameTate P S aS d F U e).inv ≫
      (OrientationRefinement.pull P (Etale.vectorIntegrationChart S d F U.1 e)).map
        (adjunct P S aS d F) ≫ (frameRho P S aS d F U e).hom

/-- The diagonal assembly in the published affine coordinate tower, retaining beta
as actual integration rather than substituting diagonal purity for it.
Source: vector-bundle proof, Step 2
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def affineAssembly (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) :=
  letI := chartTraceProjection_smooth B d
  (P.chartDiagonalAlpha d (affineTraceProjection B d) aB).inv ≫
    (P.chartDiagonalDelta d (affineTraceProjection B d) aB).hom ≫
    (normalBeta P d (affineTraceProjection B d) aB).hom

/-- The two requested equalities for every chosen linear frame on U.
Source: vector-bundle proof, Steps 2--3
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def Equations (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) : Prop :=
  letI := P.noetherian aS
  ∀ e : VectorBundleZeroSection.Trivialization S d F U.1,
    frameOrientation P S aS d F U e = affineAssembly P U.1.toScheme (U.1.ι ≫ aS) d ∧
    frameAdjunct P S aS d F U e = affineAdjunct P U.1.toScheme (U.1.ι ≫ aS) d

/-- The actual coordinate map from a smaller framed bundle chart into a larger
one. For equal opens it is exactly change of linear frame. Source: vector-bundle
proof, Steps 4--7 (blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def frameMap (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] {U U' : S.affineOpens} (h : U'.1 ≤ U.1)
    (e : VectorBundleZeroSection.Trivialization S d F U.1)
    (e' : VectorBundleZeroSection.Trivialization S d F U'.1) :=
  letI := (VectorBundleZeroSection.trivializationMap_spec S d F U'.1 e').1
  (affineTraceAffineSpaceIso U'.1.toScheme d).hom ≫
    inv (VectorBundleZeroSection.trivializationMap S d F U'.1 e') ≫
    OrientationRefinement.inclusion (VectorBundleZeroSection.π S d F) h ≫
    VectorBundleZeroSection.trivializationMap S d F U.1 e ≫
    (affineTraceAffineSpaceIso U.1.toScheme d).inv

/-- Geometry of a change of diagonal pairs. The product is fixed by both projections;
the normal map is fixed by the coefficientwise Rees map on its closed fibre. Thus
no independent normal automorphism is permitted. Source: vector-bundle proof,
Steps 4--6 (blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
structure PairGeometry {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] (f' : X' ⟶ Y') [IsSeparated f'] (a : X' ⟶ X) where
  product : pullback f' f' ⟶ pullback f f
  fst_eq : product ≫ pullback.fst f f = pullback.fst f' f' ≫ a
  snd_eq : product ≫ pullback.snd f f = pullback.snd f' f' ≫ a
  diagonal_eq : pullback.diagonal f' ≫ product = a ≫ pullback.diagonal f
  cartesian : IsPullback product (pullback.fst f' f') (pullback.fst f f) a
  normal : (pullback.diagonal f').ker.normalCone ⟶ (pullback.diagonal f).ker.normalCone
  normal_eq : normal ≫ (pullback.diagonal f).ker.normalConeToDeformationSpace =
    (pullback.diagonal f').ker.normalConeToDeformationSpace ≫
      SectionReesBaseChange.pairMap (pullback.diagonal f) (pullback.diagonal f')
        product a diagonal_eq
  normal_cartesian : IsPullback normal
    (Scheme.Hom.normalConeProj (pullback.fst f' f') (pullback.diagonal f'))
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)) a
  zero_eq : (pullback.diagonal f').normalConeZeroSection ≫ normal =
    a ≫ (pullback.diagonal f).normalConeZeroSection

/-- Canonical source-section comparison for a frame restriction, including the
pullback compositor and the actual diagonal square. Source: vector-bundle proof,
Steps 4--5 (blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def sourceExchange (P : PurityFiniteSetting.{u}) {X Y X' Y' : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f' : X' ⟶ Y') [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (aY' : Y' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (a : X' ⟶ X) (G : PairGeometry f f' a) :=
  (OrientationRefinement.pull P a).mapIso
      (Dnc.sourceComparison P d (pullback.fst f f) (f ≫ aY) (pullback.diagonal f)) ≪≫
    OrientationRefinement.sectionExchange P d (pullback.fst f f) (pullback.fst f' f')
      (f ≫ aY) (f' ≫ aY') G.cartesian (pullback.diagonal f) (pullback.diagonal f')
      G.diagonal_eq ≪≫
    (Dnc.sourceComparison P d (pullback.fst f' f') (f' ≫ aY') (pullback.diagonal f')).symm

/-- Canonical normal-section comparison for the same coefficientwise Rees map.
Source: vector-bundle proof, Steps 4--6
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def normalExchange (P : PurityFiniteSetting.{u}) {X Y X' Y' : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f' : X' ⟶ Y') [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (aY' : Y' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (a : X' ⟶ X) (G : PairGeometry f f' a) :=
  letI := Dnc.normalCompactifiable P d (pullback.fst f f) (f ≫ aY)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  letI := Dnc.normalCompactifiable P d (pullback.fst f' f') (f' ≫ aY')
    (pullback.diagonal f') (pullback.diagonal_fst f')
  letI := Dnc.normalQuasiCompact d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  letI := Dnc.normalQuasiCompact d (pullback.fst f' f')
    (pullback.diagonal f') (pullback.diagonal_fst f')
  letI : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)) :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst f)).smoothOfRelativeDimension_proj
  (OrientationRefinement.pull P a).mapIso
      (Dnc.normalComparison P d (pullback.fst f f) (f ≫ aY)
        (pullback.diagonal f) (pullback.diagonal_fst f)) ≪≫
    OrientationRefinement.sectionExchange P d
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (Scheme.Hom.normalConeProj (pullback.fst f' f') (pullback.diagonal f'))
      (f ≫ aY) (f' ≫ aY') G.normal_cartesian
      (pullback.diagonal f).normalConeZeroSection (pullback.diagonal f').normalConeZeroSection
      G.zero_eq ≪≫
    (Dnc.normalComparison P d (pullback.fst f' f') (f' ≫ aY')
      (pullback.diagonal f') (pullback.diagonal_fst f')).symm

/-- All three factors commute individually with the canonical changes of section
objects. Alpha uses the canonical p2 Delta = id compositor in chartDiagonalAlpha.
Source: vector-bundle proof, Steps 4--6
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def Factors (P : PurityFiniteSetting.{u}) {B B' : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [IsSeparated aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    [IsSeparated aB'] (d : ℕ)
    (a : affineTraceTower B' d ⟶ affineTraceTower B d) (b : B' ⟶ B)
    (sq : IsPullback a (affineTraceProjection B' d) (affineTraceProjection B d) b) : Prop :=
  letI := chartTraceProjection_smooth B d
  letI := chartTraceProjection_smooth B' d
  ∃ G : PairGeometry (affineTraceProjection B d) (affineTraceProjection B' d) a,
    (OrientationRefinement.pull P a).map
        (P.chartDiagonalAlpha d (affineTraceProjection B d) aB).hom ≫
      (rho P d (affineTraceProjection B d) aB (affineTraceProjection B' d) aB' a b sq).hom =
      (sourceExchange P d (affineTraceProjection B d) aB
        (affineTraceProjection B' d) aB' a G).hom ≫
      (P.chartDiagonalAlpha d (affineTraceProjection B' d) aB').hom ∧
    (OrientationRefinement.pull P a).map
        (P.chartDiagonalDelta d (affineTraceProjection B d) aB).hom ≫
      (normalExchange P d (affineTraceProjection B d) aB
        (affineTraceProjection B' d) aB' a G).hom =
      (sourceExchange P d (affineTraceProjection B d) aB
        (affineTraceProjection B' d) aB' a G).hom ≫
      (P.chartDiagonalDelta d (affineTraceProjection B' d) aB').hom ∧
    (OrientationRefinement.pull P a).map (normalBeta P d (affineTraceProjection B d) aB).hom ≫
      (OrientationRefinement.tate P a (affineTraceProjection B d ≫ aB) d).hom =
      (normalExchange P d (affineTraceProjection B d) aB
        (affineTraceProjection B' d) aB' a G).hom ≫
      (normalBeta P d (affineTraceProjection B' d) aB').hom

/-- Both frame formulas commute with further restriction AND change of linear frame.
The frames on the two opens may be different; equal opens give arbitrary frame changes.
The last two equations are for the actual transported maps on both sides, not merely
a repetition of the formulas on each open. Source: vector-bundle proof, Steps 4--7
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def Compatible (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U U' : S.affineOpens) (h : U'.1 ≤ U.1) : Prop :=
  letI := P.noetherian aS
  letI := chartTraceProjection_smooth U.1.toScheme d
  letI := chartTraceProjection_smooth U'.1.toScheme d
  ∀ (e : VectorBundleZeroSection.Trivialization S d F U.1)
    (e' : VectorBundleZeroSection.Trivialization S d F U'.1),
    ∃ sq : IsPullback (frameMap S d F h e e') (affineTraceProjection U'.1.toScheme d)
        (affineTraceProjection U.1.toScheme d) (S.homOfLE h),
      frameMap S d F h e e' ≫ Etale.vectorIntegrationChart S d F U.1 e =
        Etale.vectorIntegrationChart S d F U'.1 e' ∧
      Factors P (U.1.ι ≫ aS) (U'.1.ι ≫ aS) d (frameMap S d F h e e') (S.homOfLE h) sq ∧
      (OrientationRefinement.pull P (frameMap S d F h e e')).map
          (frameOrientation P S aS d F U e) ≫
        (OrientationRefinement.tate P (frameMap S d F h e e')
          (affineTraceProjection U.1.toScheme d ≫ U.1.ι ≫ aS) d).hom =
        (rho P d (affineTraceProjection U.1.toScheme d) (U.1.ι ≫ aS)
          (affineTraceProjection U'.1.toScheme d) (U'.1.ι ≫ aS)
          (frameMap S d F h e e') (S.homOfLE h) sq).hom ≫
        frameOrientation P S aS d F U' e' ∧
      (OrientationRefinement.pull P (frameMap S d F h e e')).map
          (frameAdjunct P S aS d F U e) ≫
        (rho P d (affineTraceProjection U.1.toScheme d) (U.1.ι ≫ aS)
          (affineTraceProjection U'.1.toScheme d) (U'.1.ι ≫ aS)
          (frameMap S d F h e e') (S.homOfLE h) sq).hom =
        (OrientationRefinement.tate P (frameMap S d F h e e')
          (affineTraceProjection U.1.toScheme d ≫ U.1.ι ≫ aS) d).hom ≫
        frameAdjunct P S aS d F U' e'

/-- The full restriction assertion, including affine refinements of all overlaps.
The fixed coefficient extension is the bottom subfield, i.e. E = Q_l. No open,
rank, or field characteristic allowed by the source is excluded.
Source: blueprint latest, vector-bundle orientation, Step 3
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction). -/
def Conclusion (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  (∀ U : S.affineOpens, Equations P S aS d F U) ∧
  (∀ (U U' : S.affineOpens) (h : U'.1 ≤ U.1), Compatible P S aS d F U U' h) ∧
  ∀ U₁ U₂ : S.affineOpens,
    (⨆ W : {W : S.affineOpens // W.1 ≤ U₁.1 ⊓ U₂.1}, W.val.1) = U₁.1 ⊓ U₂.1 ∧
    ∀ (W : S.affineOpens) (h₁ : W.1 ≤ U₁.1) (h₂ : W.1 ≤ U₂.1),
      Compatible P S aS d F U₁ W h₁ ∧ Compatible P S aS d F U₂ W h₂

end FrameOrientation

/-- Restricting the specified diagonal factors and the independent integration
adjunct to any affine bundle frame gives exactly the two displayed maps, compatibly
with further frames and affine refinements. Source: blueprint latest,
sk-prop-sp-orientation-vector-bundle.proof.md, Step 3
(blueprint: lem-pur-vector-bundle-frame-orientation-restriction).

Proof:
1. lem-pur-vector-bundle-finite-type-frames supplies Noetherianity and the
   separated finite-type smooth bundle map. Restriction to an affine target
   is separated finite type over k (lem-pur-affine-target-diagonal-dnc).
2. Apply the diagonal assembly clause of lem-pur-diagonal-dnc-chart-normalization
   and identify its three factors through the frame. Its zero-section factor
   is the inverse actual integration adjunct by the site comparison; this is
   normalBeta. No equality of the global orientation and inverse integration
   is used.
3. Apply cor-pur-vector-bundle-purity at the unit and its base-change equation.
   lem-pur-vector-integration-site-comparison identifies its actual adjunct
   on both sites. lem-pur-bounded-site-exchange-transposes identifies the
   exchange separately, also for nonseparated S. Compose with inverse tau.
4. lem-pur-diagonal-orientation-refinement supplies each individual factor
   restriction. Paste exceptional mates (lem-weil-pbc-mate-pasting) and use
   the canonical derived pullback compositor and Cartesian Tate comparisons.
   In alpha this includes the canonical p2 Delta = id comparison.
5. Under a frame change G the coordinate differences y-x change to G(y-x).
   The associated-graded normal map is thus that same G. Normalized DNC
   uniqueness makes delta equivariant, while mate pasting gives alpha.
6. lem-amb-linear-trace-invariance preserves the actual affine trace for p
   and for its normal bundle. The site comparison and
   lem-pur-trace-transpose-base-change transport its transpose; pull inverse
   normal purity along zero to obtain beta. This proves all three equations
   in Factors and both equations in Compatible, without assuming purity agreement.
7. Affine subopens cover every overlap even when that overlap is not affine.
   Restrict both frames there and apply Steps 4--6. For the empty open all
   arrows are unique; in rank zero all trace and DNC diagrams are identities. -/
theorem vectorBundle_frame_orientation_restriction (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    FrameOrientation.Conclusion P S aS d F := by
  sorry

end WeilConjectures.PurityFiniteSetting
