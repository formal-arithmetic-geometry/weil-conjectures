/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.LocalFrobeniusTrace
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Exact point hearts and finite-stage Weil representatives

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 7, dimension-zero Jordan filtration
(blueprint: lem-zl-point-heart-finite-stage).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The specified H^0 point functor, restricted to the actual rational heart.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointHeartOmega : sfRationalHeart l E (Spec (.of D.k)) ⥤ ModuleCat.{u} E :=
  (sfRationalHeartProperty l E (Spec (.of D.k))).ι ⋙ pointRationalFibre D l hl E ⋙
    DerivedCategory.coefficientFdCohomology E 0

/-- The specified H^0 point functor on the raw common-stage heart.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointCommonHeartOmega : sfCommonStageHeart l (Spec (.of D.k)) Ω ⥤ ModuleCat.{u} Ω :=
  (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω).ι ⋙ pointQbarFibre D l hl Ω ⋙
    DerivedCategory.coefficientQbarCohomology l Ω 0

/-- Exact equivalence onto finite-dimensional modules, expressed without choosing an
abelian structure on the source. Finite limits and colimits include kernels, cokernels
and the zero object; their reflection and the short-exact equivalence are explicit.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def ZlPointHeartExact {C : Type v} [Category.{w} C] [Preadditive C]
    (F : Type u) [Field F] (ω : C ⥤ ModuleCat.{u} F) : Prop :=
  ω.Full ∧ ω.Faithful ∧ ω.Additive ∧
    (∀ X, FiniteDimensional F (ω.obj X)) ∧
    (∀ V : ModuleCat.{u} F, FiniteDimensional F V → ∃ X, Nonempty (ω.obj X ≅ V)) ∧
    PreservesFiniteLimits ω ∧ PreservesFiniteColimits ω ∧
    ReflectsFiniteLimits ω ∧ ReflectsFiniteColimits ω ∧
    (∀ X, IsZero (ω.obj X) ↔ IsZero X) ∧
    (∀ [ω.PreservesZeroMorphisms] (S : ShortComplex C),
      (S.map ω).ShortExact ↔ S.ShortExact)

/-- The ambient rational realization used for the canonical truncation comparisons.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointAmbient : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
    DerivedCategory (ModuleCat.{u} E) :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι

/-- The ambient common-stage realization, using the recorded fully faithful realization.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointCommonAmbient : generalAlgebraicallyClosedConstructibleCategory l Ω
    (Spec (.of D.k)) ⥤ DerivedCategory (ModuleCat.{u} Ω) :=
  pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω

/-- Canonical truncation comparisons, characterized by the truncation counit and unit.
These equations exclude an arbitrary identification or a choice of splitting.
Source: BBD 1.3.3 and paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
structure ZlPointTruncationComparison
    {C : Type v} [Category.{w} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : Type u) [Field F] (t : Triangulated.TStructure C)
    (R : C ⥤ DerivedCategory (ModuleCat.{u} F)) where
  le : ∀ n : ℤ, t.truncLE n ⋙ R ≅ R ⋙ DerivedCategory.TStructure.t.truncLE n
  ge : ∀ n : ℤ, t.truncGE n ⋙ R ≅ R ⋙ DerivedCategory.TStructure.t.truncGE n
  le_counit : ∀ (n : ℤ) (K : C),
    (le n).hom.app K ≫ (DerivedCategory.TStructure.t.truncLEι n).app (R.obj K) =
      R.map ((t.truncLEι n).app K)
  ge_unit : ∀ (n : ℤ) (K : C),
    R.map ((t.truncGEπ n).app K) ≫ (ge n).hom.app K =
      (DerivedCategory.TStructure.t.truncGEπ n).app (R.obj K)

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The prescribed scalar comparison on H^0: sections comparison followed by the
canonical cohomology/tensor comparison sending tensor cycle classes to cycle classes.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointHeartScalar
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (DerivedCategory.coefficientFdCohomology L 0).obj
        ((pointRationalFibre D l hl L).obj
          ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)) ≅
      (ModuleCat.extendScalars ι.toRingHom).obj
        ((DerivedCategory.coefficientFdCohomology E 0).obj
          ((pointRationalFibre D l hl E).obj K)) :=
  (DerivedCategory.coefficientFdCohomology L 0).mapIso
      ((pointRationalFibreScalarIso D l hl E L ι).app K) ≪≫
    (DerivedCategory.fieldDerivedHomologyIso ι.toRingHom 0).app
      ((pointRationalFibre D l hl E).obj K).obj

/-- Source standard t-structure at the point, with its identity structure morphism.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
abbrev zlPointT := sfRationalStandardTStructure l E (Spec (.of D.k)) D hl

/-- The actual finite coefficient extension at the point.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
abbrev zlPointScalar := sfRationalScalarExtension l E (Spec (.of D.k)) 0
  (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

/-- The sections scalar comparison before applying H^0.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointScalarAmbient :
    zlPointScalar D l E L ι ⋙ zlPointAmbient D l hl L ≅
      zlPointAmbient D l hl E ⋙ DerivedCategory.fieldDerivedScalarExtension ι.toRingHom :=
  Functor.isoWhiskerRight (pointRationalFibreScalarIso D l hl E L ι)
    (DerivedCategory.pointFiniteDimensional L).ι

/-- Scalar/truncation commutativity for the specified sections comparison.
The equations are the upper counit and lower unit characterizations for the composite
scalar-then-fibre functor, so uniqueness makes the two truncation routes coincide.
Source: paragraph 7 and BBD 1.3.3 (blueprint: lem-zl-point-heart-finite-stage). -/
def ZlPointScalarTruncationSquare
    (cE : ZlPointTruncationComparison E (zlPointT D l hl E) (zlPointAmbient D l hl E))
    (cL : ZlPointTruncationComparison L (zlPointT D l hl L) (zlPointAmbient D l hl L)) :
    Prop :=
  ∃ (aLE : ∀ n : ℤ, (zlPointT D l hl E).truncLE n ⋙ zlPointScalar D l E L ι ≅
        zlPointScalar D l E L ι ⋙ (zlPointT D l hl L).truncLE n)
    (aGE : ∀ n : ℤ, (zlPointT D l hl E).truncGE n ⋙ zlPointScalar D l E L ι ≅
        zlPointScalar D l E L ι ⋙ (zlPointT D l hl L).truncGE n)
    (bLE : ∀ n : ℤ, DerivedCategory.TStructure.t.truncLE n ⋙
        DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ≅
      DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ⋙
        DerivedCategory.TStructure.t.truncLE n)
    (bGE : ∀ n : ℤ, DerivedCategory.TStructure.t.truncGE n ⋙
        DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ≅
      DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ⋙
        DerivedCategory.TStructure.t.truncGE n),
    (∀ (n : ℤ) (K : sfRationalConstructibleCategory l E (Spec (.of D.k))),
      (aLE n).hom.app K ≫ ((zlPointT D l hl L).truncLEι n).app
        ((zlPointScalar D l E L ι).obj K) =
          (zlPointScalar D l E L ι).map (((zlPointT D l hl E).truncLEι n).app K)) ∧
    (∀ (n : ℤ) (K : sfRationalConstructibleCategory l E (Spec (.of D.k))),
      (zlPointScalar D l E L ι).map (((zlPointT D l hl E).truncGEπ n).app K) ≫
        (aGE n).hom.app K =
          ((zlPointT D l hl L).truncGEπ n).app ((zlPointScalar D l E L ι).obj K)) ∧
    (∀ (n : ℤ) (V : DerivedCategory (ModuleCat.{u} E)),
      (bLE n).hom.app V ≫ (DerivedCategory.TStructure.t.truncLEι n).app
          ((DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).obj V) =
        (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).map
          ((DerivedCategory.TStructure.t.truncLEι n).app V)) ∧
    (∀ (n : ℤ) (V : DerivedCategory (ModuleCat.{u} E)),
      (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).map
          ((DerivedCategory.TStructure.t.truncGEπ n).app V) ≫ (bGE n).hom.app V =
        (DerivedCategory.TStructure.t.truncGEπ n).app
          ((DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).obj V)) ∧
    (∀ (n : ℤ) (K : sfRationalConstructibleCategory l E (Spec (.of D.k))),
      (zlPointAmbient D l hl L).map ((aLE n).hom.app K) ≫
          (cL.le n).hom.app ((zlPointScalar D l E L ι).obj K) ≫
          (DerivedCategory.TStructure.t.truncLE n).map
            ((zlPointScalarAmbient D l hl E L ι).hom.app K) =
        (zlPointScalarAmbient D l hl E L ι).hom.app
            (((zlPointT D l hl E).truncLE n).obj K) ≫
          (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).map
            ((cE.le n).hom.app K) ≫ (bLE n).hom.app ((zlPointAmbient D l hl E).obj K)) ∧
    (∀ (n : ℤ) (K : sfRationalConstructibleCategory l E (Spec (.of D.k))),
      (zlPointAmbient D l hl L).map ((aGE n).hom.app K) ≫
          (cL.ge n).hom.app ((zlPointScalar D l E L ι).obj K) ≫
          (DerivedCategory.TStructure.t.truncGE n).map
            ((zlPointScalarAmbient D l hl E L ι).hom.app K) =
        (zlPointScalarAmbient D l hl E L ι).hom.app
            (((zlPointT D l hl E).truncGE n).obj K) ≫
          (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).map
            ((cE.ge n).hom.app K) ≫ (bGE n).hom.app ((zlPointAmbient D l hl E).obj K))

/-- The point over the finite field, with its identity structure map.
Source: paragraph 7, dimension zero (blueprint: lem-zl-point-heart-finite-stage). -/
abbrev zlPointHeartBase : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

/-- Finite type of the identity map, without a new geometric assumption.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
instance zlPointHeartBaseLocallyOfFiniteType :
    LocallyOfFiniteType (zlPointHeartBase D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- Quasi-compactness of the identity map.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
instance zlPointHeartBaseQuasiCompact : QuasiCompact (zlPointHeartBase D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- The prescribed degree-zero geometric fibre of a recorded Weil complex.
The point is a map into the geometric fibre, not an identification of its scheme.
Source: paragraph 7 and the local point convention
(blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointWeilFibreAt
    (x : Spec (.of D.k) ⟶ (D.geometricFiber (zlPointHeartBase D)).left) :
    sfCommonStageWeilComplex D l hl (zlPointHeartBase D) Ω ⥤ ModuleCat.{u} Ω :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl (zlPointHeartBase D)
  sfCommonStageWeilForget D l hl (zlPointHeartBase D) Ω ⋙
    commonStageDerivedPullback l Ω x ⋙ pointQbarFibre D l hl Ω ⋙
      DerivedCategory.coefficientQbarCohomology l Ω 0

/-- Canonical scalar/cohomology followed by the ordinary tensor tower.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointCohomologyTower (R S T : Type u) [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) (C : DerivedCategory (ModuleCat.{u} R)) :
    (ModuleCat.extendScalars g).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0).obj
          ((DerivedCategory.fieldDerivedScalarExtension f).obj C)) ≅
      (ModuleCat.extendScalars (g.comp f)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj C) :=
  (ModuleCat.extendScalars g).mapIso
      ((DerivedCategory.fieldDerivedHomologyIso f 0).app C) ≪≫
    ((ModuleCat.extendScalarsComp f g).app
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj C)).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Canonical cohomology transport from a small coefficient model to its actual
subfield and then to the closure. This is the recorded cohomology and tensor tower.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointStageCohomology (A : Padic.FiniteCoefficientFields l Ω)
    (C : (DerivedCategory.pointFiniteDimensional
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).FullSubcategory) :
    (DerivedCategory.coefficientQbarCohomology l Ω 0).obj
        ⟨A, (DerivedCategory.pointFdScalarExtension
          (Shrink.algEquiv (Padic l) A.val).toRingHom).obj C⟩ ≅
      (ModuleCat.extendScalars
        (A.val.subtype.comp (Shrink.algEquiv (Padic l) A.val).toRingHom)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) 0).obj C) := by
  dsimp only [DerivedCategory.coefficientQbarCohomology, Functor.copyObj,
    DerivedCategory.coefficientFdCohomology, DerivedCategory.pointFdScalarExtension,
    ObjectProperty.lift, ObjectProperty.ι, Functor.comp_obj]
  exact zlPointCohomologyTower
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) A.val Ω
    (Shrink.algEquiv (Padic l) A.val).toRingHom A.val.subtype C.obj

/-- The specified finite-stage-to-closure comparison on degree-zero point fibres.
It uses the literal point-fibre object formula followed by canonical coefficient
cohomology transport. No vector-space basis or complex splitting is chosen.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointStageOmega (A : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) A) :
    (DerivedCategory.coefficientQbarCohomology l Ω 0).obj
        ((pointQbarFibre D l hl Ω).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion A).obj K)) ≅
      (ModuleCat.extendScalars
        (A.val.subtype.comp (Shrink.algEquiv (Padic l) A.val).toRingHom)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) 0).obj
          ((pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).obj K)) :=
  (DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
      (eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1 _)) ≪≫
    zlPointStageCohomology l Ω A
      ((pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).obj K)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [irreducible] zlPointStageOmega zlPointStageCohomology zlPointCohomologyTower

/-- The specified scalar comparison after pullback at the geometric point.
It uses the recorded literal pullback-stage comparison, followed by the canonical
point-fibre/cohomology scalar comparison, including the coefficient tower.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
def zlPointWeilStageOmega (A : Padic.FiniteCoefficientFields l Ω)
    (M : sfWeilComplex D l hl (zlPointHeartBase D)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
    (x : Spec (.of D.k) ⟶ (D.geometricFiber (zlPointHeartBase D)).left) :
    (zlPointWeilFibreAt D l hl Ω x).obj
        (sfWeilStageObject D l hl (zlPointHeartBase D) Ω A M) ≅
      (ModuleCat.extendScalars
        (A.val.subtype.comp (Shrink.algEquiv (Padic l) A.val).toRingHom)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) 0).obj
          (localPointComplex l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
            D hl (zlPointHeartBase D) M x)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl (zlPointHeartBase D)
  (pointQbarFibre D l hl Ω ⋙ DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
      (@localQbarPullbackStageIso l _ Ω _ _ _
        (Spec (.of D.k)) (D.geometricFiber (zlPointHeartBase D)).left x
        (fun y ↦ frobeniusPointPrimeInvertible D l hl y)
        (fun y ↦ sfWeilPrimeInvertible D l hl (zlPointHeartBase D) y)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion A).obj M.carrier)) ≪≫
    zlPointStageOmega D l hl Ω A
      ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) x).obj M.carrier)

attribute [irreducible] zlPointWeilStageOmega

/-- One simultaneous finite coefficient stage for the actual recorded point Weil sheaf.
M is a finite-stage Weil sheaf, not a private fixed-pair specialization. The target
retains its raw representative. All inverse and intertwining equations hold at A.
The fibre is taken along the specified geometric point x, as in the local convention.
Source: paragraph 7 (blueprint: lem-zl-point-heart-finite-stage). -/
structure ZlPointFiniteStageWitness
    (F : sfCommonStageWeilSheaf D l hl (zlPointHeartBase D) Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber (zlPointHeartBase D)).left) where
  A : Padic.FiniteCoefficientFields l Ω
  target_le : F.obj.carrier.stage ≤ A
  M : sfWeilSheaf D l hl (zlPointHeartBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
  targetTheta : (sfWeilFrobeniusPullback D l hl (zlPointHeartBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).obj
      (F.obj.carrier.toStage target_le) ≅ F.obj.carrier.toStage target_le
  u : M.obj.carrier ≅ F.obj.carrier.toStage target_le
  intertwining : M.obj.str.hom ≫ u.hom =
    (sfWeilFrobeniusPullback D l hl (zlPointHeartBase D)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).map u.hom ≫ targetTheta.hom
  target_structure :
    (sfCommonStageWeilFrobeniusPullback D l hl (zlPointHeartBase D) Ω).mapIso
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
          (D.geometricFiber (zlPointHeartBase D)).left).isoToStage F.obj.carrier target_le) ≪≫
      sfWeilStagePullbackIdentification D l hl (zlPointHeartBase D) Ω A
        (F.obj.carrier.toStage target_le) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion A).mapIso targetTheta ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
        (D.geometricFiber (zlPointHeartBase D)).left).isoToStage
          F.obj.carrier target_le).symm = F.obj.str
  e : sfWeilStageObject D l hl (zlPointHeartBase D) Ω A M.obj ≅ F.obj
  e_hom : e.hom.hom.f =
    (GeneralAlgebraicallyClosedCoefficients.inclusion A).map u.hom ≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
        (D.geometricFiber (zlPointHeartBase D)).left).isoToStage
          F.obj.carrier target_le).inv
  e_inv : e.inv.hom.f =
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
      (D.geometricFiber (zlPointHeartBase D)).left).isoToStage F.obj.carrier target_le).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion A).map u.inv
  fibre : (zlPointWeilFibreAt D l hl Ω x).obj F.obj ≅
    (ModuleCat.extendScalars
      (A.val.subtype.comp (Shrink.algEquiv (Padic l) A.val).toRingHom)).obj
      ((DerivedCategory.coefficientFdCohomology
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) 0).obj
        (localPointComplex l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          D hl (zlPointHeartBase D) M.obj x))
  fibre_normalization : fibre =
    (zlPointWeilFibreAt D l hl Ω x).mapIso e.symm ≪≫
      zlPointWeilStageOmega D l hl Ω A M.obj x

attribute [irreducible] zlPointHeartOmega zlPointCommonHeartOmega zlPointAmbient
  zlPointCommonAmbient zlPointHeartScalar zlPointScalarAmbient

end WeilConjectures
