/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.WeilOpenImageDelta
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.GeometricHypotheses
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Targets.SliceRestrictionStrictDerivedLimit
import Sheaf.Paper.SfConstructibleHeart
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.PbcCommonStageCones
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.TraceFormula.PointTransportComposition
import Sheaf.Paper.IntegralPointTransportTowerRealization
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Pointed constant-field charts and adic open-image comparison

Source: Stacks 04KV and 0D6G; main-20261015, sk-p-dl-a1-exact.proof.md,
“At a missing point, after shrinking” (blueprint: lem-dl-a1-constant-field-charts).

The finite residue field is identified with its prescribed subfield of the fixed closure.
The chart retains that identification. All sheaves, images, cohomology and local operators
are the published adic common-stage constructions. The packages below specify the
restriction and its comparisons, including their normalization, rather than choosing an
unspecified functor or an isomorphism from a mere existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D E : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (hl : l ≠ D.p) (he : l ≠ E.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Actual common-stage inverse image between the two specified geometric fibres.
Source: Stacks 0D6G (blueprint: lem-dl-a1-constant-field-charts). -/
def dlChartPull
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ f
    (sfWeilPrimeInvertible E l he Y) (sfWeilPrimeInvertible D l hl X)

/-- The return map is the normalized pullback compositor for h g_V = g_W^m h.
Source: Stacks 0D6G, Weil iterate paragraph
(blueprint: lem-dl-a1-constant-field-charts). -/
def dlChartReturnComparison
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (m : ℕ) (f : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (hf : (E.geometricFrobenius Y).hom ≫ f =
      f ≫ localPositivePower (D.geometricFrobenius X).hom (m - 1))
    (K : sfCommonStageWeilComplex D l hl X Ω) :
    (sfCommonStageWeilFrobeniusPullback E l he Y Ω).obj
        ((dlChartPull D E l hl he Ω X Y f).obj K.carrier) ≅
      (dlChartPull D E l hl he Ω X Y f).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (D.geometricFrobenius X).hom (m - 1))
          (sfWeilPrimeInvertible D l hl X) (sfWeilPrimeInvertible D l hl X)).obj
            K.carrier) :=
  letI := sfWeilPrimeInvertible D l hl X
  letI := sfWeilPrimeInvertible E l he Y
  (localQbarPullbackComposition l Ω (E.geometricFrobenius Y).hom f K.carrier).symm ≪≫
    eqToIso (congrArg (fun g ↦ (commonStageDerivedPullback l Ω g).obj K.carrier) hf) ≪≫
      localQbarPullbackComposition l Ω f
        (localPositivePower (D.geometricFrobenius X).hom (m - 1)) K.carrier

/-- A restriction means the actual inverse image on carriers and arrows, with precisely
h^*(theta^[m]) as Weil datum. The cohomology comparison is normalized by its truncation
unit and counit, using the existing ConstructiblePullbackComparison interface.
Source: Stacks 0D6G and the constant-field paragraph of sk-p-dl-a1-exact
(blueprint: lem-dl-a1-constant-field-charts). -/
structure DlChartRestriction
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (m : ℕ) (f : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (hf : (E.geometricFrobenius Y).hom ≫ f =
      f ≫ localPositivePower (D.geometricFrobenius X).hom (m - 1)) where
  pull : sfCommonStageWeilSheaf D l hl X Ω ⥤ sfCommonStageWeilSheaf E l he Y Ω
  carrier : pull ⋙ constantExtensionHeartForget E l he Ω Y ≅
    constantExtensionHeartForget D l hl Ω X ⋙ dlChartPull D E l hl he Ω X Y f
  weil : ∀ F : sfCommonStageWeilSheaf D l hl X Ω,
    (sfCommonStageWeilFrobeniusPullback E l he Y Ω).map (carrier.hom.app F) ≫
        (dlChartReturnComparison D E l hl he Ω X Y m f hf F.obj).hom ≫
          (dlChartPull D E l hl he Ω X Y f).map
            (localQbarWeilIterate l Ω D hl X F.obj (m - 1)).hom =
      (pull.obj F).obj.str.hom ≫ carrier.hom.app F
  cohomology : ConstructiblePullbackComparison
    (sfCommonStageStandardTStructure l (D.geometricFiber X).left Ω D hl)
    (sfCommonStageStandardTStructure l (E.geometricFiber Y).left Ω E he)
    (sfCommonStageHeartProperty l (D.geometricFiber X).left Ω)
    (sfCommonStageHeartProperty l (E.geometricFiber Y).left Ω)
    (dlChartPull D E l hl he Ω X Y f)
  shift : cohomology.commShift =
    @fieldCommonPullShift l _ Ω _ _ _ _ _ f
      (sfWeilPrimeInvertible E l he Y) (sfWeilPrimeInvertible D l hl X)

/-- A local module comparison, using the published common-stage stalk and geometric
Frobenius, with all choices of geometric point included. The exponent is the relative
residue degree, not the degree over either finite base.
Source: local degree calculation, md'=ed
(blueprint: lem-dl-a1-constant-field-charts). -/
def DlChartLocalConjugacy
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (F : sfCommonStageWeilSheaf D l hl X Ω)
    (G : sfCommonStageWeilSheaf E l he Y Ω)
    (x : {x : X.left // x ∈ closedPoints X.left})
    (y : {y : Y.left // y ∈ closedPoints Y.left}) (e : ℕ) : Prop :=
  ∀ (ι : X.left.residueField x.val →+* D.k)
    (hι : ι.comp (X.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (ι' : Y.left.residueField y.val →+* E.k)
    (hι' : ι'.comp (Y.hom.residueFieldAlgebraMap y.val) = algebraMap E.k₀ E.k),
    ∃ a : localQbarClosedStalk l Ω D hl X F.obj x ι hι ≅
        localQbarClosedStalk l Ω E he Y G.obj y ι' hι',
      a.hom ≫ localQbarClosedFrobeniusStalk l Ω E he Y G.obj y ι' hι' =
        ((End.of (localQbarClosedFrobeniusStalk l Ω D hl X F.obj x ι hι)) ^ e) ≫ a.hom

/-- A pointed affine chart, over the actual image of the chosen residue-field embedding.
The equivalence residue identifies this finite field with kappa(s), so transporting the
chart along it gives literally the kappa(s)-curve in the statement. The two open maps
and the Cartesian square retain the actual maps h and h_U.
Source: Stacks 04KV and the rational-point construction
(blueprint: lem-dl-a1-constant-field-charts). -/
structure DlPointedConstantChart (c : Scheme.MiddleExtensionCurve D)
    (s : {s : c.C.left // s ∈ closedPoints c.C.left})
    (ι : c.C.left.residueField s.val →+* D.k) where
  m : ℕ
  positive : 1 ≤ m
  residue : c.C.left.residueField s.val ≃+* D.extensionSubfield m positive
  embedding : (D.extensionSubfield m positive).subtype.comp residue.toRingHom = ι
  curve : Scheme.MiddleExtensionCurve (constantExtensionDatum D m positive)
  chart : curve.C ⟶ constantExtensionModel D m positive c.C
  [openChart : IsOpenImmersion chart.left]
  [affine : IsAffine curve.C.left]
  [dimension : SmoothOfRelativeDimension 1 curve.C.hom]
  [connected : GeometricallyConnected curve.C.hom]
  [openConnected : GeometricallyConnected curve.U.hom]
  openChartU : curve.U ⟶ constantExtensionModel D m positive c.U
  square : curve.j ≫ chart = openChartU ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m positive)))).map c.j
  t : {t : curve.C.left // t ∈ closedPoints curve.C.left}
  rational : Function.Bijective (curve.C.hom.residueFieldAlgebraMap t.val)
  image : (chart.left ≫ (constantExtensionProjection D m positive c.C).left) t.val = s.val
  residueMap : Function.Bijective
    ((chart.left ≫ (constantExtensionProjection D m positive c.C).left).residueFieldMap t.val)
  [etale : Etale (chart.left ≫ (constantExtensionProjection D m positive c.C).left)]
  cartesian : IsPullback
    (openChartU.left ≫ (constantExtensionProjection D m positive c.U).left) curve.j.left
    c.j.left (chart.left ≫ (constantExtensionProjection D m positive c.C).left)
  finiteBoundary : (Set.range curve.j.left)ᶜ.Finite
  closedBoundary : ∀ y ∈ (Set.range curve.j.left)ᶜ, y ∈ closedPoints curve.C.left

attribute [instance] DlPointedConstantChart.openChart DlPointedConstantChart.affine
  DlPointedConstantChart.dimension DlPointedConstantChart.connected
  DlPointedConstantChart.openConnected DlPointedConstantChart.etale


/-- The geometric map of the pointed chart is base change followed by the canonical
associativity isomorphism, hence is the specified open in W over the fixed closure.
Source: Stacks 04KV (blueprint: lem-dl-a1-constant-field-charts). -/
def DlPointedConstantChart.geometricMap {c : Scheme.MiddleExtensionCurve D}
    {s : {s : c.C.left // s ∈ closedPoints c.C.left}}
    {ι : c.C.left.residueField s.val →+* D.k} (A : DlPointedConstantChart D c s ι) :=
  zlFiberMap (constantExtensionDatum D A.m A.positive) A.chart ≫
    (constantExtensionFiberIso D A.m A.positive c.C).hom

/-- The same canonical map on the pulled-back dense open.
Source: Stacks 04KV (blueprint: lem-dl-a1-constant-field-charts). -/
def DlPointedConstantChart.geometricOpenMap {c : Scheme.MiddleExtensionCurve D}
    {s : {s : c.C.left // s ∈ closedPoints c.C.left}}
    {ι : c.C.left.residueField s.val →+* D.k} (A : DlPointedConstantChart D c s ι) :=
  zlFiberMap (constantExtensionDatum D A.m A.positive) A.openChartU ≫
    (constantExtensionFiberIso D A.m A.positive c.U).hom

/-- The inverse-image square between two finite-base presentations of an open immersion.
It uses only the normalized common-stage pullback compositor and the specified equality.
Source: Stacks 0D6G (blueprint: lem-dl-a1-constant-field-charts). -/
def dlChartPullSquare (c : Scheme.MiddleExtensionCurve D) (d : Scheme.MiddleExtensionCurve E)
    (a : (E.geometricFiber d.C).left ⟶ (D.geometricFiber c.C).left)
    (b : (E.geometricFiber d.U).left ⟶ (D.geometricFiber c.U).left)
    (h : zlFiberMap E d.j ≫ a = b ≫ zlFiberMap D c.j) :
    dlChartPull D E l hl he Ω c.C d.C a ⋙ zlPull E l he Ω d.j ≅
      zlPull D l hl Ω c.j ⋙ dlChartPull D E l hl he Ω c.U d.U b :=
  letI := sfWeilPrimeInvertible D l hl c.C
  letI := sfWeilPrimeInvertible D l hl c.U
  letI := sfWeilPrimeInvertible E l he d.C
  letI := sfWeilPrimeInvertible E l he d.U
  (zlPullComp l Ω (zlFiberMap E d.j) a).symm ≪≫
    eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f) h) ≪≫
      zlPullComp l Ω b (zlFiberMap D c.j)

/-- The canonical derived exchange is the counit mate of the actual pullback square.
In K-injective sections it is I(T times_W U) = I(T times_V U_V).
Source: Stacks 0D6G (blueprint: lem-dl-a1-constant-field-charts). -/
def dlChartDerivedExchange
    (c : Scheme.MiddleExtensionCurve D) (d : Scheme.MiddleExtensionCurve E)
    (a : (E.geometricFiber d.C).left ⟶ (D.geometricFiber c.C).left)
    (b : (E.geometricFiber d.U).left ⟶ (D.geometricFiber c.U).left)
    (h : zlFiberMap E d.j ≫ a = b ≫ zlFiberMap D c.j)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.U).left) :
    (dlChartPull D E l hl he Ω c.C d.C a).obj
        ((sfModelDerivedPush D l hl Ω c.j).obj K) ⟶
      (sfModelDerivedPush E l he Ω d.j).obj
        ((dlChartPull D E l hl he Ω c.U d.U b).obj K) :=
  (sfModelDerivedAdjunction E l he Ω d.j).homEquiv _ _
    ((dlChartPullSquare D E l hl he Ω c d a b h).hom.app
        ((sfModelDerivedPush D l hl Ω c.j).obj K) ≫
      (dlChartPull D E l hl he Ω c.U d.U b).map
        ((sfModelDerivedAdjunction D l hl Ω c.j).counit.app K))

set_option maxHeartbeats 800000 in
-- Elaborate the normalized higher-image equations in both common-stage Weil hearts.
/-- Natural comparisons for exactly r=0,1, normalized by the derived counit mate.
The boundary clause uses the published boundary data, including its heart-triangle
formula, so it compares the connecting maps of lem-dl-a1-weil-open-image-delta.
Source: Stacks 0D6G and sk-p-dl-a1-exact
(blueprint: lem-dl-a1-constant-field-charts). -/
structure DlChartOpenComparison
    (c : Scheme.MiddleExtensionCurve D) (d : Scheme.MiddleExtensionCurve E)
    (m : ℕ)
    (a : (E.geometricFiber d.C).left ⟶ (D.geometricFiber c.C).left)
    (b : (E.geometricFiber d.U).left ⟶ (D.geometricFiber c.U).left)
    (ha : (E.geometricFrobenius d.C).hom ≫ a =
      a ≫ localPositivePower (D.geometricFrobenius c.C).hom (m - 1))
    (hb : (E.geometricFrobenius d.U).hom ≫ b =
      b ≫ localPositivePower (D.geometricFrobenius c.U).hom (m - 1))
    (h : zlFiberMap E d.j ≫ a = b ≫ zlFiberMap D c.j)
    (R : DlChartRestriction D E l hl he Ω c.C d.C m a ha)
    (S : DlChartRestriction D E l hl he Ω c.U d.U m b hb)
    (I : DlOpenImageData D l hl Ω c) (J : DlOpenImageData E l he Ω d) where
  lisse : ∀ F : sfCommonStageWeilSheaf D l hl c.U Ω,
    DlOpenIsLisse D l hl Ω c F → DlOpenIsLisse E l he Ω d (S.pull.obj F)
  ordinary : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F →
      (R.pull.obj ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F) ≅
        (qbarCurveWeilOrdinaryPushforward E l he Ω d).obj (S.pull.obj F))
  higher : ∀ (r : ℤ), r = 0 ∨ r = 1 →
    ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω), DlOpenIsLisse D l hl Ω c F →
      (R.pull.obj ((dlOpenHigherImage D l hl Ω c r).obj F) ≅
        (dlOpenHigherImage E l he Ω d r).obj (S.pull.obj F))
  natural : ∀ (r : ℤ) (hr : r = 0 ∨ r = 1)
    (F G : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F) (hG : DlOpenIsLisse D l hl Ω c G) (f : F ⟶ G),
    R.pull.map ((dlOpenHigherImage D l hl Ω c r).map f) ≫ (higher r hr G hG).hom =
      (higher r hr F hF).hom ≫ (dlOpenHigherImage E l he Ω d r).map (S.pull.map f)
  normalization : ∀ (r : ℤ) (hr : r = 0 ∨ r = 1)
    (F : sfCommonStageWeilSheaf D l hl c.U Ω) (hF : DlOpenIsLisse D l hl Ω c F),
    (higher r hr F hF).hom.hom.hom.f =
      R.carrier.hom.app ((dlOpenHigherImage D l hl Ω c r).obj F) ≫
        (dlChartPull D E l hl he Ω c.C d.C a).map
          (dlHigherGeometricComparison D l hl Ω c r F).hom ≫
        (R.cohomology.cohomology r).hom.app
          ((sfModelDerivedPush D l hl Ω c.j).obj F.obj.carrier) ≫
        (sfModelCohomology E l he Ω d.C r).map
          (dlChartDerivedExchange D E l hl he Ω c d a b h F.obj.carrier ≫
            (sfModelDerivedPush E l he Ω d.j).map (S.carrier.inv.app F)) ≫
        (dlHigherGeometricComparison E l he Ω d r (S.pull.obj F)).inv
  degreeZero : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F),
    R.pull.map (I.degreeZero F hF).hom ≫ (ordinary F hF).hom =
      (higher 0 (Or.inl rfl) F hF).hom ≫ (J.degreeZero (S.pull.obj F) (lisse F hF)).hom
  boundary : ∀ (A : DlOpenLisseSES D l hl Ω c) (B : DlOpenLisseSES E l he Ω d)
    (f₁ : S.pull.obj A.S.X₁ ⟶ B.S.X₁) (f₂ : S.pull.obj A.S.X₂ ⟶ B.S.X₂)
    (f₃ : S.pull.obj A.S.X₃ ⟶ B.S.X₃),
    S.pull.map A.S.f ≫ f₂ = f₁ ≫ B.S.f → S.pull.map A.S.g ≫ f₃ = f₂ ≫ B.S.g →
    (ordinary A.S.X₃ A.lisse₃).hom ≫
        (qbarCurveWeilOrdinaryPushforward E l he Ω d).map f₃ ≫ J.boundary B =
      R.pull.map (I.boundary A) ≫ (higher 1 (Or.inr rfl) A.S.X₁ A.lisse₁).hom ≫
        (dlOpenHigherImage E l he Ω d 1).map f₁


/-- All adic clauses at a pointed chart: the actual iterated restriction, normalized
ordinary/higher image comparisons, the boundary square, local modules at the rational
lift, and the residue-degree power law and purity on the dense open.
Source: Stacks 0D6G and sk-p-dl-a1-exact, constant-field reduction
(blueprint: lem-dl-a1-constant-field-charts). -/
structure DlPointedChartAdicData (c : Scheme.MiddleExtensionCurve D)
    (s : {s : c.C.left // s ∈ closedPoints c.C.left})
    (ι : c.C.left.residueField s.val →+* D.k)
    (A : DlPointedConstantChart D c s ι) where
  returnC : ((constantExtensionDatum D A.m A.positive).geometricFrobenius A.curve.C).hom ≫
      A.geometricMap D = A.geometricMap D ≫
        localPositivePower (D.geometricFrobenius c.C).hom (A.m - 1)
  returnU : ((constantExtensionDatum D A.m A.positive).geometricFrobenius A.curve.U).hom ≫
      A.geometricOpenMap D = A.geometricOpenMap D ≫
        localPositivePower (D.geometricFrobenius c.U).hom (A.m - 1)
  square : zlFiberMap (constantExtensionDatum D A.m A.positive) A.curve.j ≫
      A.geometricMap D = A.geometricOpenMap D ≫ zlFiberMap D c.j
  restrictC : DlChartRestriction D (constantExtensionDatum D A.m A.positive)
    l hl hl Ω c.C A.curve.C A.m (A.geometricMap D) returnC
  restrictU : DlChartRestriction D (constantExtensionDatum D A.m A.positive)
    l hl hl Ω c.U A.curve.U A.m (A.geometricOpenMap D) returnU
  compare : ∀ (I : DlOpenImageData D l hl Ω c)
    (J : DlOpenImageData (constantExtensionDatum D A.m A.positive) l hl Ω A.curve),
    DlChartOpenComparison D (constantExtensionDatum D A.m A.positive) l hl hl Ω
      c A.curve A.m (A.geometricMap D) (A.geometricOpenMap D)
      returnC returnU square restrictC restrictU I J
  equalSize : Nat.card (A.curve.C.left.residueField A.t.val) =
    Nat.card (c.C.left.residueField s.val)
  localImage : ∀ (r : ℤ) (_hr : r = 0 ∨ r = 1)
    (F : sfCommonStageWeilSheaf D l hl c.U Ω), DlOpenIsLisse D l hl Ω c F →
    DlChartLocalConjugacy D (constantExtensionDatum D A.m A.positive) l hl hl Ω
      c.C A.curve.C ((dlOpenHigherImage D l hl Ω c r).obj F)
      ((dlOpenHigherImage (constantExtensionDatum D A.m A.positive) l hl Ω A.curve r).obj
        (restrictU.pull.obj F)) s A.t 1
  localOpen : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F →
    ∀ v : {v : A.curve.U.left // v ∈ closedPoints A.curve.U.left},
      ∃ u : {u : c.U.left // u ∈ closedPoints c.U.left},
        (A.openChartU.left ≫ (constantExtensionProjection D A.m A.positive c.U).left) v.val =
            u.val ∧
        Nat.card (A.curve.U.left.residueField v.val) =
          Nat.card (c.U.left.residueField u.val) ^
            (A.openChartU.left ≫
              (constantExtensionProjection D A.m A.positive c.U).left).residueDegree v.val ∧
        DlChartLocalConjugacy D (constantExtensionDatum D A.m A.positive) l hl hl Ω
          c.U A.curve.U F (restrictU.pull.obj F) u v
          ((A.openChartU.left ≫
            (constantExtensionProjection D A.m A.positive c.U).left).residueDegree v.val)
  pure : ∀ (iota : Ω ≃+* ℂ) (F : sfCommonStageWeilSheaf D l hl c.U Ω) (w : ℝ),
    DlOpenIsLisse D l hl Ω c F →
    SfIsPunctuallyPureOfWeight D l hl Ω c.U iota.toRingHom F w →
      SfIsPunctuallyPureOfWeight (constantExtensionDatum D A.m A.positive) l hl Ω
        A.curve.U iota.toRingHom (restrictU.pull.obj F) w

/-- Compatibility with two successive open restrictions, expressed on the actual derived
counit mates and then in degrees zero and one. Exact restriction identifies these with
the higher-image comparison maps; no replacement direct image is used.
Source: Stacks 0D6G, identity on K-injective sections
(blueprint: lem-dl-a1-constant-field-charts). -/
def DlOpenImageSuccessive : Prop :=
  ∀ (c d e : Scheme.MiddleExtensionCurve D)
    (a : d.C ⟶ c.C) (b : d.U ⟶ c.U) (a' : e.C ⟶ d.C) (b' : e.U ⟶ d.U)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left]
    [IsOpenImmersion a'.left] [IsOpenImmersion b'.left]
    (h : b ≫ c.j = d.j ≫ a) (h' : b' ≫ d.j = e.j ≫ a')
    (h'' : (b' ≫ b) ≫ c.j = e.j ≫ (a' ≫ a))
    (_p : IsPullback b.left d.j.left c.j.left a.left)
    (_p' : IsPullback b'.left e.j.left d.j.left a'.left)
    (F : sfCommonStageWeilSheaf D l hl c.U Ω), DlOpenIsLisse D l hl Ω c F →
    ∀ (r : ℤ), r = 0 ∨ r = 1 →
    (sfModelCohomology D l hl Ω e.C r).map
      ((sfModelPullComposition D l hl Ω a' a).hom.app
          ((sfModelDerivedPush D l hl Ω c.j).obj F.obj.carrier) ≫
        (zlPull D l hl Ω a').map
          (sfModelDerivedExchange D l hl Ω c.j a b d.j h F.obj.carrier) ≫
        sfModelDerivedExchange D l hl Ω d.j a' b' e.j h'
          ((zlPull D l hl Ω b).obj F.obj.carrier) ≫
        (sfModelDerivedPush D l hl Ω e.j).map
          ((sfModelPullComposition D l hl Ω b' b).inv.app F.obj.carrier)) =
      (sfModelCohomology D l hl Ω e.C r).map
        (sfModelDerivedExchange D l hl Ω c.j (a' ≫ a) (b' ≫ b) e.j h'' F.obj.carrier)

/-- Pointed affine constant-field charts and their actual adic open-image comparisons.
Source: Stacks 04KV, 0D6G; main-20261015 sk-p-dl-a1-exact.proof.md, the sentence
“At a missing point, after shrinking” (blueprint: lem-dl-a1-constant-field-charts).

Proof, following the node's thirteen steps:
1. W is Noetherian by lem-weil-pbc-finite-type-over-noetherian. A specialization chain
in the boundary would extend by a component generic point to length two. The boundary
is zero-dimensional and finite by lem-pc-zero-dimensional-closed-subscheme-finite.
By lem-kun-closed-point-field the residue field L is finite over k0. The polynomial
T^(#L)-T has derivative -1; L/k0 is separable and hence etale by
lem-weil-pbc-finite-separable-extension-etale.
2. Form Spec(A tensor L) by lem-weil-pbc-fibre-product-affine-spectra. Evaluation at s
has an L-rational lift. Smooth-relative-dimension permanence, lem-sc-smooth-normal,
and Noetherianity make this ring normal Noetherian. Its product-of-domains decomposition
from lem-sbc-normal-sections-finite-product selects the affine connected component
containing the lift. Identify L with the prescribed finite subfield through the embedding.
3. Open immersions, base change and composition are etale by the cited etale permanence
lemmas. The chart remains smooth of dimension one. Its rational point gives geometric
connectedness by lem-sbc-connected-rational-point-geometrically-connected. Etale maps
are open, so the pulled-back open is dense. Its boundary is again finite and closed.
4. Over k the smooth connected curve is normal Noetherian. Its finitely many components
are disjoint by normality, hence it is irreducible. Removing a finite boundary leaves a
nonempty connected open. Apply lem-weil-geometrically-connected-algebraic-closure.
5. The geometric chart is an open in W and h gV = gW^m h. Pull back the m-fold Weil
iterate with the normalized integral pullback compositions. Finite-level locally
constant trivializations and their quotient transitions pull back, proving lissity.
6. Use lem-weil-proetale-weakly-etale-localization to identify the coefficient sites
with slices. Finite constant rings and their completed limits restrict to the same
rings. Restriction is exact by lem-pur-site-restriction-module-adjunction-exact.
7. Apply lem-weil-pbc-ringed-derived-slice-localization and its specified ringed-site
localization. On K-injectives the comparison is I(T times_W U)=I(T times_V U_V).
This fixes the counit mate and preserves shifts and morphisms, without properness.
8. The completed-coefficient-pushforward comparison identifies the actual integral
image with its strict reduction tower. Slice restriction commutes with that derived
limit, including all projections, by lem-sp-slice-restriction-strict-derived-limit.
The identity-morphism case identifies integral inverse image with restriction too.
9. Rationalize these linear comparisons and descend over common finite coefficient
fields. Exact restriction commutes with cohomology, giving the stated r=0,1 maps.
Degree zero is the ordinary image by lem-dl-a1-weil-open-image-delta.
10. The unique heart triangle of a lisse short exact sequence gives its boundary.
Exact restriction preserves that triangle; naturality and shift compatibility of the
comparison give beta1 h^*delta = deltaV beta0. Use the published boundary_formula;
no triangulation of Weil pairs is assumed.
11. The same sectionwise identity intertwines the iterated Weil maps. Point pullback
composition and lem-weil-frobenius-point-transport-natural intertwine local operators.
12. Write d=[kappa(u):k0], d'=[kappa(v):L], e=[kappa(v):kappa(u)]. Then md'=ed.
Point-transport composition and its integral tower realization group the same md'
transports into e blocks, giving Fv=Fu^e and qv=qu^e. At t the residue map is an
isomorphism, so e=1 and Ft=Fs, qt=qs. Triangularization (p-linear-triangular) gives
purity of the same weight after taking the positive power e.
13. For ordinary open neighborhoods repeat the same slice argument. In two successive
restrictions both comparisons are the identity on the same sections. Their equality
survives strict towers, rationalization, common-stage descent and cohomology. -/
theorem dlConstantFieldCharts :
    (∀ (c : Scheme.MiddleExtensionCurve D) [IsAffine c.C.left]
      [SmoothOfRelativeDimension 1 c.C.hom],
      ((Set.range c.j.left)ᶜ).Finite ∧
      (∀ s ∈ (Set.range c.j.left)ᶜ, s ∈ closedPoints c.C.left) ∧
      ∀ (s : {s : c.C.left // s ∈ closedPoints c.C.left}), s.val ∉ Set.range c.j.left →
      ∀ (ι : c.C.left.residueField s.val →+* D.k),
        ι.comp (c.C.hom.residueFieldAlgebraMap s.val) = algebraMap D.k₀ D.k →
        ∃ A : DlPointedConstantChart D c s ι, Nonempty (DlPointedChartAdicData D l hl Ω c s ι A)) ∧
    (∀ I : ∀ c : Scheme.MiddleExtensionCurve D, DlOpenImageData D l hl Ω c,
      ∀ (c d : Scheme.MiddleExtensionCurve D) (a : d.C ⟶ c.C) (b : d.U ⟶ c.U)
        [IsOpenImmersion a.left] [IsOpenImmersion b.left],
        IsPullback b.left d.j.left c.j.left a.left →
        ∃ (ha : (D.geometricFrobenius d.C).hom ≫ zlFiberMap D a =
            zlFiberMap D a ≫ localPositivePower (D.geometricFrobenius c.C).hom (1 - 1))
          (hb : (D.geometricFrobenius d.U).hom ≫ zlFiberMap D b =
            zlFiberMap D b ≫ localPositivePower (D.geometricFrobenius c.U).hom (1 - 1))
          (hs : zlFiberMap D d.j ≫ zlFiberMap D a =
            zlFiberMap D b ≫ zlFiberMap D c.j)
          (R : DlChartRestriction D D l hl hl Ω c.C d.C 1 (zlFiberMap D a) ha)
          (S : DlChartRestriction D D l hl hl Ω c.U d.U 1 (zlFiberMap D b) hb),
          Nonempty (DlChartOpenComparison D D l hl hl Ω c d 1
            (zlFiberMap D a) (zlFiberMap D b) ha hb hs R S (I c) (I d))) ∧
    DlOpenImageSuccessive D l hl Ω := by
  sorry

end WeilConjectures
