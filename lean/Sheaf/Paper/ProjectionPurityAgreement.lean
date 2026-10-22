module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.AffineLinePurityComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.AffineDiagonalTateCoordinates
public import Sheaf.Paper.AffineDiagonalTensorCoordinates
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

import Sheaf.Paper.VectorIntegrationSiteComparison
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import Sheaf.Paper.AffineTranslationTrace
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.Paper.TraceTransposeBaseChange
import Sheaf.Paper.PurityDncComparisons
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.TensorTraceTranspose
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.SixFunctors.CompositionProjectionMate
import Sheaf.Paper.FiniteProjectionActionLaws
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.Paper.CompositeIntegrationCounit

/-! # Agreement of the two affine-space purity maps

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement (blueprint: lem-pur-projection-purity-agreement).
The comparison maps below change only coefficient, tensor and identity coordinates.

## Main declarations

* `projectionSourceIso` and `projectionTargetMap`: explicit normalized coordinates.
* `projectionAffineIntrinsic`: the existing ordered affine map on the original K.
* `projectionSmoothIntrinsic`: the recorded smooth map at the coordinate projection.
* `projection_purity_agreement`: equality of those two specified morphisms.
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
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

/-- The standard projection is smooth of the indicated pure relative dimension.
Source: polynomial charts; sbc-lem-affine-space-smooth
(blueprint: lem-pur-projection-purity-agreement).
Proof: the zero projection is the identity. Each successor adjoins one polynomial
variable and is smooth of pure dimension one. Relative dimensions add under
composition, giving dimension d, including the empty base. -/
theorem projection_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (iteratedAffineLineProj Y d) := by
  sorry

/-- The source of the smooth comparison in fixed-scalar coordinates.
Source: the displayed Lp* K(d)[2d]
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothSource (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C P.Coefficient Y)
    (d : ℕ) :=
  (((smoothPurityTensor P.Coefficient (iteratedAffineLine Y d)).obj
    ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)).obj
      ((P.diagonalTwist (iteratedAffineLine Y d) d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧

attribute [local irreducible] projectionTensorActionIso projectionTensorActionGeneric
  projectionTensorStep projectionLineIso projectionUnitRaw

/-- The literal canonical source-coordinate map, retaining its computed endpoints.
Source: tensor, shift, and identity normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSourceRaw
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) :
    (d : ℕ) → Σ M N : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient (iteratedAffineLine Y d), M ≅ N
  | 0 => ⟨_, _,
    (projectionSetting F C E n).smoothPurityReassociation Y 0
      (((projectionSetting F C E n).smoothPurityPullback (𝟙 Y)).obj K) ≪≫
    projectionTensorActionIso F C E n Y aY _ 0 ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarId
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _).app K⟩
  | d + 1 => ⟨_, _,
    (projectionSetting F C E n).smoothPurityReassociation (iteratedAffineLine Y (d + 1))
      (d + 1) (((projectionSetting F C E n).smoothPurityPullback
        (iteratedAffineLineProj Y (d + 1))).obj K) ≪≫
    projectionTensorActionIso F C E n (iteratedAffineLine Y (d + 1))
      (towerBase aY (d + 1)) _ (d + 1) ≪≫
    (action ((tensor (projectionSetting F C E n).Coefficient
      (iteratedAffineLine Y (d + 1))).flip.obj
        (shiftedLine (projectionSetting F C E n) (iteratedAffineLine Y (d + 1))))
      (d + 1)).mapIso
      (((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient)
          (iteratedAffineLineProj Y (d + 1))).app K).symm)⟩

/-- The common source-coordinate isomorphism type.
Source: purity source presentations (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionSourceIsoType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :=
  projectionSmoothSource (projectionSetting F C E n) Y K d ≅
    (orderedSource (projectionSetting F C E n) Y d).obj K

/-- The raw composite has exactly the recorded smooth and ordered affine endpoints.
The heterogeneous equality fixes its hom, so it cannot be chosen using a purity map.
Source: source presentations (blueprint: lem-pur-projection-purity-agreement).
Proof: unfold the two endpoints, the positive-level coefficient index, and orderedSource.
At zero, exact identity pullback, the tensor unit and zero shift give K. At a successor,
the exact/derived comparison followed by the ordered action gives orderedSource.
Transport the raw isomorphism along these endpoint equalities. Its hom is the specified
raw hom. Any two such isomorphisms have equal homs by transitivity of HEq, hence are equal. -/
theorem projectionSourceIso_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ∃! e : ProjectionSourceIsoType F C E n Y K d,
      HEq e (projectionSourceRaw F C E n Y aY K d).2.2 := by
  sorry

/-- The uniquely transported canonical source isomorphism, independent of either
purity arrow. Source: source-coordinate normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSourceIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ProjectionSourceIsoType F C E n Y K d :=
  projectionChooseUnique (projectionSourceIso_existsUnique F C E n Y aY K d)

/-- The recorded exceptional target of the smooth map.
Source: finite exceptional conventions (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothTarget (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C P.Coefficient Y)
    (d : ℕ) :=
  letI := (projection_geometry Y d).1
  (P.smoothPurityExceptionalOver (iteratedAffineLineProj Y d) aY).obj K

/-- The literal exceptional-coordinate map. At a positive rank it is identity;
at zero it is the ordinary exceptional identity comparison followed by the
comparison-adjunction counit, restricted later to the etale-origin class.
Source: exceptional identity normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionTargetRaw
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) :
    (d : ℕ) → Σ M N : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient (iteratedAffineLine Y d), M ⟶ N
  | 0 =>
    ⟨_, _,
      (ProEtale.VectorIntegrationSite.comparison (projectionSetting F C E n).Coefficient
        Y).map
          (((Etale.rightDerivedUpperShriekIsoOfIso
            (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) (Iso.refl Y)) ≪≫
              Etale.leftDerivedUpperStarId
                (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).hom.app
                  ((ProEtale.comparisonLowerStar
                    (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient)
                      Y).rightDerivedFunctor.obj K)) ≫
        (ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).counit.app K⟩
  | d + 1 =>
    letI := (projection_geometry Y (d + 1)).1
    letI := (projection_geometry Y (d + 1)).2
    ⟨_, _, 𝟙 (projectionSmoothTarget (projectionSetting F C E n) Y aY K (d + 1))⟩

/-- The common exceptional-coordinate map type.
Source: finite exceptional conventions (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionTargetMapType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :=
  projectionSmoothTarget (projectionSetting F C E n) Y aY K d ⟶
    (AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional
      (projectionSetting F C E n) Y d).obj K

/-- The raw exceptional normalization has the required source and target.
Source: the fixed finite exceptional functor and p_0=id
(blueprint: lem-pur-projection-purity-agreement).
Proof: at positive rank both definitions are nu* f^times Rnu_* at the same standing
compactification. The left-adjoint instances are propositions. At zero unfold the
identity exceptional functor; the raw comparison ends at K, the normalized target. -/
theorem projectionTargetMap_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ∃! t : ProjectionTargetMapType F C E n Y aY K d,
      HEq t (projectionTargetRaw F C E n Y aY K d).2.2 := by
  sorry

/-- The canonical exceptional-coordinate map, fixed independently of purity.
Source: identity and positive-rank normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionTargetMap
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ProjectionTargetMapType F C E n Y aY K d :=
  projectionChooseUnique (projectionTargetMap_existsUnique F C E n Y aY K d)



/-- On the stated etale-origin class the target normalization is invertible.
Source: bounded site comparison and exceptional identity
(blueprint: lem-pur-projection-purity-agreement).
Proof: at positive rank the raw map is identity. At zero the ordinary exceptional
identity comparison is invertible. For bounded-below Ke the comparison unit is
invertible; the adjunction triangle therefore makes the counit invertible at nu*Ke.
Transport across eK gives invertibility at K, including zero and empty-scheme objects. -/
theorem projectionTarget_isIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    IsIso (projectionTargetMap F C E n Y aY K.obj d) := by
  sorry

/-- The existing ordered affine-line composite, in the smooth source and target
coordinates. The source and target comparisons use no orientation map.
Source: Gamma_(p_d,K) (blueprint: lem-pur-projection-purity-agreement). -/
def projectionAffineInPresentation
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    projectionSmoothSource (projectionSetting F C E n) Y K.obj d ⟶
      projectionSmoothTarget (projectionSetting F C E n) Y aY K.obj d :=
  letI : IsIso (projectionTargetMap F C E n Y aY K.obj d) :=
    projectionTarget_isIso F C E n Y aY K Ke hKe eK d
  (projectionSourceIso F C E n Y aY K.obj d).hom ≫
    affineSpacePurityComparison (projectionSetting F C E n) Y aY K Ke hKe eK d ≫
      inv (projectionTargetMap F C E n Y aY K.obj d)

/-- The Hom type on the original intrinsic pro-etale object, with the specified
smooth source and the transported exceptional target.
Source: displayed Hom in the item (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionIntrinsicHom (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) (d : ℕ) :=
  (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor.obj
    (projectionSmoothSource P Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) d) ⟶
  (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor.obj
    (projectionSmoothTarget P Y aY
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) d)

/-- The affine-line composite has a unique presentation-independent realization on
K itself. Quantification over every etale presentation specifies its map completely;
existence of presentations follows from hK and is not an extra hypothesis.
Source: the affine-line construction and its ordered composite
(blueprint: lem-pur-projection-purity-agreement).
Proof: finite type over k makes Y Noetherian. The constructible-origin theorem and
finite-Tor comparison supply an etale finite-Tor representative of K and a lower bound.
The affine-line map is the specified exceptional transpose of the projection/integration
composite, so naturality of the Hom bijection identifies its maps under every change
of representative. The ordered recursion preserves this identity, using the canonical
pullback, Tate and exceptional compositors. The source root-power and tensor comparisons
and target identity comparison are natural in the same presentations. Hence their
conjugated composite has one value on every representative. Apply the intrinsic
realization functor. This constructs g and proves its defining equations. Any two
candidates agree using one of the available presentations, proving uniqueness. -/
theorem projectionAffineIntrinsic_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    ∃! g : ProjectionIntrinsicHom (projectionSetting F C E n) Y aY K d,
      ∀ (hb : boundedBelow (projectionSetting F C E n).Coefficient Y
        ((Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj
          K))
        (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
        (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
        (eK : (ProEtale.VectorIntegrationSite.comparison
          (projectionSetting F C E n).Coefficient Y).obj Ke ≅
            (Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj
              K),
        g = (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d)
          (projectionSetting F C E n).Ring).functor.map
            (projectionAffineInPresentation F C E n Y aY
              ⟨(Scheme.sfIntrinsicDerivedEquivalence Y
                (projectionSetting F C E n).Ring).inverse.obj K, hb⟩ Ke hKe eK d) := by
  sorry

/-- The ordered affine-line comparison on the original K. The existence-and-uniqueness
statement fixes the arrow by its value in every presentation, rather than choosing an
object or an orientation from mere existence.
Source: Gamma_(p_d,K) (blueprint: lem-pur-projection-purity-agreement). -/
def projectionAffineIntrinsic
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    ProjectionIntrinsicHom (projectionSetting F C E n) Y aY K d :=
  projectionChooseUnique (projectionAffineIntrinsic_existsUnique F C E n Y aY K hK d)

/-- The recorded smooth purity map at the affine projection. The required source
structure over k is its projection followed by aY, and the geometric instances
follow from polynomial charts; none is an additional hypothesis.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothIntrinsicRaw (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) :
    Σ M N : Scheme.proEtaleDerivedCategory (iteratedAffineLine Y d) P.Ring, M ⟶ N :=
  letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  letI : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) := ⟨towerBase aY d⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aY)
  letI : LocallyOfFiniteType (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).1
  letI : QuasiCompact (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).2.1
  letI : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI := (projection_geometry Y d).1
  letI := projection_smooth Y d
  ⟨_, _, P.smoothPurityMap (iteratedAffineLineProj Y d) d K hK⟩

/-- The recorded smooth map has the displayed intrinsic source and exceptional target.
This fixes its hom by literal heterogeneous equality, without changing its orientation.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement).
Proof: the installed Over structures have maps aY and p_d followed by aY. Their
finite-type instances are the original base instances and tower_geometry. Unfold
smoothPurityMap and its tensor source. Its source and target are precisely the two
objects in ProjectionIntrinsicHom. Transport the raw map along those endpoint equalities;
HEq fixes the hom uniquely. No purity equality is used in this endpoint check. -/
theorem projectionSmoothIntrinsic_existsUnique
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) :
    ∃! g : ProjectionIntrinsicHom P Y aY K d,
      HEq g (projectionSmoothIntrinsicRaw P Y aY K hK d).2.2 := by
  sorry

/-- The actual recorded smooth map in the common intrinsic Hom coordinates.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothIntrinsic (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) : ProjectionIntrinsicHom P Y aY K d :=
  projectionChooseUnique (projectionSmoothIntrinsic_existsUnique P Y aY K hK d)

/-- Smooth purity for the affine-space projection agrees with the ordered composite
of the affine-line integration transposes, at every positive coefficient level.
The orientation in smoothPurityMap is the recorded normalized diagonal/DNC orientation.
The affine composite uses the actual open-counit restriction of projective-line trace.
Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement (blueprint: lem-pur-projection-purity-agreement).

Proof (the DAG route, with its prerequisite nodes):
1. Choose $r\geq1$ with $\ell^r A=0$. Apply [lem-pur-vector-integration-site-comparison] to the
   trivial bundle over each base used here. Its statement gives the coherent specified Tate
   realization, the equality of the projective-line decompositions and traces, the open-counit
   restriction to $I_S$, and independence of $r$. Thus the displayed definition of each affine-line
   $\Gamma$ and its ordered composites is independent of $r$. This cites the coefficient and Kummer
   comparison as an existing lemma, rather than re-proving it using an empty divisor.
2. For $K$, choose the bounded constructible etale representative $K^e$ of [lem-sf-proetale-
   constructible-origin](ii). By [lem-sf-comparison-tor-amplitude](ii) it has the finite Tor
   interval of $K$, so [lem-pur-vector-integration-site-comparison] compares the actual
   projection/integration transposes on these inputs. Every scheme in the coordinate and projective
   compactification towers is finite type over $k$, hence Noetherian by [lem-weil-pbc-finite-type-
   over-noetherian] and of finite dimension by [lem-kun-dimension-finite-type]. Their projective
   compactifications therefore have integer dimension bounds. The source inputs are bounded etale-
   origin objects, so the Hom bijections of [thm-sf-ambient-adjoint-class] apply. Empty schemes have
   the unique maps between zero objects.
3. Put $p=p_d$, $X=\mathbf A^d_Y$ and $W=X\times_YX$. The projection $p$ is smooth of pure relative
   dimension $d$ by [sbc-lem-affine-space-smooth]. The diagonal base-change isomorphism is
   $\alpha:C(p_1,\Delta)\to\omega_p$ of [lem-pur-diagonal-base-change]; the section invariant is
   [def-pur-section-invariant]. The diagonal is regular of codimension $d$, with normal bundle
   $T_{X/Y}$ by [lem-pur-diagonal-regular-immersion]. In coordinates $(x,y)$, the isomorphism
   $h(x,y)=(x,u=y-x)$ has inverse $(x,u)\mapsto(x,x+u)$, takes $\Delta$ to zero, and sends its
   conormal basis $y_i-x_i$ to $u_i$. Thus its normal-coordinate basis is unchanged. The schemes and
   morphisms here are separated finite type by their polynomial charts; for $d=0$ the coordinate
   lists are empty.
4. The extracted lemma [lem-pur-affine-translation-trace], applied over $X$ to the section
   $(x_1,\ldots,x_d)$, says exactly that $h$ preserves the normalized integration. The actual site
   and transpose comparisons are [lem-pur-vector-integration-site-comparison] and the Hom bijections
   of [thm-sf-ambient-adjoint-class]. Applying those functors and bijections to the trace equality
   shows that the integration-transposed comparison is unchanged by $h$. This is the translation
   argument of the unit model paragraph, including the universal parameter and base-change
   normalization.
5. For any rank-$d$ trivial bundle $q$, write $P_{q,K}:Lq^*K(d)[2d]\to Rq^!K$ for the integration
   transpose, which is invertible by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-
   site-comparison]. The integration is [def-amb-vector-integration]. Put $L=A_X(d)[2d]$,
   $P=P_{p,A_Y}$, $L'=A_W(d)[2d]$, and $J=P_{p_1,A_X}$. Let $B:Lp_2^*\omega_p\to\omega_{p_1}$ be the
   specified dualizing base-change map. The trace base-change equation is [lem-amb-affine-space-top-
   trace], transported by the site comparison just cited. Therefore [lem-pur-trace-transpose-base-
   change] applied to this square gives $J=B\circ Lp_2^*P$. In [lem-pur-diagonal-base-change],
   $\alpha=(L\Delta^*B)^{-1}$ under $p_2\Delta=1_X$, and hence
$$\alpha\circ L\Delta^*J=P.$$
The
   ordinary Tate restriction $L\Delta^*L'=L$ is the coherent restriction already fixed above.
6. Apply [thm-pur-dnc-invariance] to $(p_1,\Delta)$, obtaining
   $\delta:C(p_1,\Delta)\xrightarrow{\sim}C(\pi_N,0_N)$. In the global coordinates $u_i=y_i-x_i$
   this is a standard affine pair. Its deformation is given by $u_i=t v_i$ and has constant family
   object by the standard-pair clause of [lem-pur-dnc-section-geometry]. The normalization clause of
   the DNC theorem makes $\delta$ the identity between these two standard section invariants. Write
   $\beta=L0_N^*(P_{\pi_N,A_X}^{-1})$, followed by Step 3's ordinary Tate restriction, so
   $\beta:C(\pi_N,0_N)\to A_X(d)[2d]$. The induced normal coordinates $v_i$ use the same ordered
   basis as $u_i$, by Step 3. With Step 4's translation invariance, the standard-pair identity says
   precisely $\beta\delta=(L\Delta^*J)^{-1}$. The explicitly specified diagonal/DNC normalization in
   the statement and in the middle arrow of [def-pur-smooth-purity-map] is
   $\theta_p=\beta\delta\alpha^{-1}$. By Step 5,
   $$\theta_p=(L\Delta^*J)^{-1}\alpha^{-1}=P_{p,A_Y}^{-1}.$$
This checks the actual normalized
   arrows; it does not deduce equality merely from existence of isomorphisms to a twist. In rank
   zero the displayed coordinate lists are empty, the deformation is the constant rank-zero pair,
   and the same equations are identities.
7. The two projection maps at $(L,K)$ and $(\omega_p,K)$ used below are invertible by [lem-weil-
   finite-compact-projection-formula]. Its source coefficients have bounded constructible etale
   witnesses: $L$ is the realized shifted Tate line, and the previous DNC computation gives
   $P:L\xrightarrow{\sim}\omega_p$. Its base coefficient is the witness $K^e$ above, with finite Tor
   interval by [lem-sf-comparison-tor-amplitude](ii). The separated finite-type projection $p$
   therefore satisfies every hypothesis; no Tor condition on an arbitrary source coefficient or six-
   functor datum is assumed.
8. By [def-pur-smooth-purity-map] and the DNC computation, smooth purity is $\theta_{p,K}(1\otimes
   P)$ after the fixed Tate reassociation. Apply [lem-pur-tensor-trace-transpose] with $t=t_p$ and
   $L=A_X(d)[2d]$. It identifies this map with the transpose of $(1_K\otimes t_p)\Pi_{L,K}$. This is
   exactly $P_{p,K}$, by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-site-
   comparison]. Thus the smooth map equals the integration transpose for every $K$. The
   tensor/counit identification is now a separate lemma; it is not inferred from naturality in $K$
   alone.
9. For the coordinate tower we need projection compatibility as an identity of maps. For
   $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, compactify $g$ by $(\mathbf P^1_Y)^d$ and
   take the compatible compactification triangle for $f$ supplied by [lem-weil-pbc-compatible-
   compactification-triangle]. All these schemes are finite type over $k$, hence Noetherian by [lem-
   weil-pbc-finite-type-over-noetherian] and quasi-separated by [lem-weil-pbc-locally-noetherian-
   quasi-separated], so the qcqs hypothesis holds and their opens are quasi-compact. The normalized
   compositor of this triangle is that of [lem-amb-unbounded-compact-support-comparisons]; at the
   finite pro-etale level its proper/open interchange is the evaluation in [lem-cbc-strict-tower-
   proper-open-calculus], and with [lem-sf-class-compact-support-comparison] these are the
   comparisons defining the compositor $\alpha$ of [thm-sf-comp-composition] on the witnessed
   inputs.
10. For the triangle of the preceding step, [lem-sf-composition-projection-mate] states, for
   arbitrary ambient finite-coefficient inputs and the counit-defined projection maps of [def-
   exchange-projection], the identity
$$\operatorname{PF}_{gf;M,N}(\alpha_M\otimes1)
   =\alpha_{M\otimes P_fP_gN}\,Rg_!(\operatorname{PF}_{f;M,P_gN})\,\operatorname{PF}_{g;Rf_!M,N},$$
   with $P_u=Lu^*$ and the canonical pullback, tensor and direct-image associators inserted. By the
   preceding step its $\alpha$ is the actual compositor of [thm-sf-comp-composition] on the
   witnessed inputs used here. No coherence of a six-functor datum is invoked. Clause 3 of [lem-pur-
   finite-projection-action-laws] gives the tensor-action identity for each compactification
   projection map.
11. All inverses in the tower calculation are on the domain of [lem-weil-finite-compact-projection-
   formula]. The source coefficients are shifted Tate lines or their products, and the affine-line
   direct image of such a line is $A$ by [lem-amb-affine-space-top-trace] and [lem-pur-vector-
   integration-site-comparison]. Base factors are $K$, its pullbacks, and their tensors with locally
   free Tate lines. By [lem-sf-pullback-tor-amplitude] these pullbacks are bounded constructible
   with the same finite Tor interval; tensor with a locally free line preserves it, and a shift
   translates it. Etale witnesses exist by [lem-sf-proetale-constructible-origin], and their Tor
   intervals are reflected by [lem-sf-comparison-tor-amplitude](ii). Thus every application of the
   preceding tensor-interchange and projection identities has the required witnessed bounded-below
   and finite-Tor inputs.
12. Work first on the ordinary etale site. For a line projection $q$, [lem-asd-ordinary-
   finite-p1-adjunction] identifies the actual projective-line counit at every coefficient $K$ with
   coefficient tensor the normalized trace after inverse projection. The explicit affine-line
   adjunction of [lem-amb-affine-space-top-trace] composes it with extension by zero. Its counit is
   that projective-line counit composed with $Rq_*$ of the open counit. Naturality of the proper
   projection map in its first variable, applied to the open counit at $A(1)[2]$, and the
   compatibility of the open tensor isomorphism with the open counit (clause 2 of [lem-pur-finite-
   projection-action-laws]) identify its coefficient formula with $(1_K\otimes I_S)\Pi$, where $\Pi$
   is built from the compactification projection map of [def-exchange-projection] for $c=(j,q)$. The
   comparison [lem-pur-vector-integration-site-comparison] carries precisely this formula and its
   transpose to the specified pro-etale line map $\Gamma_{q,K}$. On the originally named domain this
   is [def-pur-affine-line-purity-comparison]. The formulas apply at all $n\geq1$ by the exponent
   independence established above.
13. On the pro-etale site use the explicit affine adjunctions, transported by [lem-pur-vector-
   integration-site-comparison], from the affine adjunctions $F_d\dashv G_d$ of [lem-amb-affine-
   space-top-trace], where $G_dK=p_d^*K(d)[2d]$. Inductively their counits have the coefficient
   formula just established in rank one. Apply [lem-pur-composite-integration-counit] to
   $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, taking $L_f=A(1)[2]$ and $L_g=A(d)[2d]$.
   The projection hypotheses are the compositor identity and the compactification tensor-action
   identity of the preceding steps, on the verified domains. This lemma makes the composite counit
   $(1_K\otimes t_{p_{d+1}})\Pi$: at the tensor unit it is precisely the trace defining [lem-amb-
   affine-space-top-trace], and [def-amb-vector-integration] uses that trace on a trivial bundle.
   The induction starts from the identity adjunction at $d=0$. Thus the integration transpose
   $P_{p_d,K}$ is the adjunction-preserving comparison with the ordered composite of the explicit
   line adjunctions.
14. The composition convention on exceptional functors is the conjugate of $\alpha$ specified in
   [def-pur-affine-space-comparison], using [thm-sf-comp-composition]. Its ordered recursion uses
   $Rq_d^!Rp_d^!K$ instead of $G_1G_dK$. Naturality of the affine-line transpose gives
   $$\Gamma_{q_d,Rp_d^!K}\,Lq_d^*(P_{p_d,K})(1)[2]
=Rq_d^!(P_{p_d,K})\,\Gamma_{q_d,G_dK}.$$
It
   follows from naturality of the defining projection/integration composite in [def-pur-affine-line-
   purity-comparison], so substitution identifies the recursion with the composite counit just
   computed. Here $G_dK$ has the verified finite-Tor domain, and $Rp_d^!K\cong G_dK$ by the earlier
   integration comparison. The fixed Tate pullback and twist-additivity identifications are those in
   [def-pur-affine-space-comparison]; all shift factors have even degree. Finally [lem-pur-vector-
   integration-site-comparison] carries this counit equality and its transposes to the pro-etale
   site. Hence $P_{p_d,K}=\Gamma_{p_d,K}$; combined with the earlier DNC calculation this is the
   desired agreement. In rank zero all maps are $1_K$, and the calculation also covers $K=0$. -/
theorem projection_purity_agreement
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    projectionSmoothIntrinsic (projectionSetting F C E n) Y aY K hK d =
      projectionAffineIntrinsic F C E n Y aY K hK d := by
  sorry

end WeilConjectures.PurityFiniteSetting
