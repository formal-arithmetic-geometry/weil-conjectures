module


public import Sheaf.Paper.AdicPurityScalarNaturality
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients


/-! # Localized smooth purity and canonical coefficient comparisons

Source: the current blueprint, sec-smooth-purity/sk-thm-purity-transport,
Steps 2--4, and sk-prop-sp-rational, the integral Hom localization argument
(blueprint: lem-pur-rational-scalar-comparison-identification).

This module hosts the unchanged coordinate definitions used by the normalized
source localization, scalar localization, and comparison descent lemmas.
`Result` and the final theorem remain in RationalScalarComparisonIdentification.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] WeilConjectures.AdicPurityScalarNaturality.scalar
  WeilConjectures.AdicPurityScalarNaturality.targetShift
  WeilConjectures.AdicPurityScalarNaturality.coefficientLinear
  WeilConjectures.RationalSmoothPurityCanonical.sourceScalar
universe u uI uR vI vR
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.RationalScalarComparisonIdentification
open AdicPurityScalarNaturality
/-- Equality of a localized comparison with the specified rational comparison,
expressed using the four localization identifications.
Source: smooth purity transport, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def LocalizesComparison
    {A B C D : Type uI} {A' B' C' D' : Type uR}
    [Category.{vI} A] [Category.{vI} B]
    [Category.{vI} C] [Category.{vI} D]
    [Category.{vR} A'] [Category.{vR} B']
    [Category.{vR} C'] [Category.{vR} D']
    {HE : A ⥤ B} {HF : C ⥤ D} {CX : B ⥤ D} {CY : A ⥤ C}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
    {hE : A' ⥤ B'} {hF : C' ⥤ D'} {TX : B' ⥤ D'} {TY : A' ⥤ C'}
    (eE : HE ⋙ QB ≅ QA ⋙ hE) (eF : HF ⋙ QD ≅ QC ⋙ hF)
    (eX : CX ⋙ QD ≅ QB ⋙ TX) (eY : CY ⋙ QC ≅ QA ⋙ TY)
    (ai : HE ⋙ CX ≅ CY ⋙ HF) (ar : hE ⋙ TX ≅ TY ⋙ hF) : Prop :=
  ∀ K : A, TX.map (eE.hom.app K) ≫ ar.hom.app (QA.obj K) =
    eX.inv.app (HE.obj K) ≫ QD.map (ai.hom.app K) ≫
      eF.hom.app (CY.obj K) ≫ hF.map (eY.hom.app K)

/-- The two purity squares, as equations on every rational object.
Source: smooth purity transport, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def PuritySquares {A B C D : Type uR}
    [Category.{vR} A] [Category.{vR} B] [Category.{vR} C] [Category.{vR} D]
    {HE GE : A ⥤ B} {HF GF : C ⥤ D} {TX : B ⥤ D} {TY : A ⥤ C}
    (eE : HE ≅ GE) (eF : HF ≅ GF)
    (a : HE ⋙ TX ≅ TY ⋙ HF) (b : GE ⋙ TX ≅ TY ⋙ GF) : Prop :=
  (∀ K : A, TX.map (eE.hom.app K) ≫ b.hom.app K =
    a.hom.app K ≫ eF.hom.app (TY.obj K)) ∧
  (∀ K : A, b.inv.app K ≫ TX.map (eE.inv.app K) =
    eF.inv.app (TY.obj K) ≫ a.inv.app K)

/-- The coefficient comparison's tensor-unit equation.
Source: smooth purity transport, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def UnitEquation {A B : Type uR} [Category.{vR} A] [Category.{vR} B]
    {H : A ⥤ B} {TX : B ⥤ B} {TY : A ⥤ A}
    (a : H ⋙ TX ≅ TY ⋙ H) (uX : TX ≅ 𝟭 B) (uY : TY ≅ 𝟭 A) : Prop :=
  ∀ K : A, a.hom.app K ≫ H.map (uY.hom.app K) = uX.hom.app (H.obj K)

/-- The coefficient comparison's tensor-associator equation.
Source: smooth purity transport, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def CompositionEquation {A B C D E F : Type uR}
    [Category.{vR} A] [Category.{vR} B] [Category.{vR} C]
    [Category.{vR} D] [Category.{vR} E] [Category.{vR} F]
    {HE : A ⥤ B} {HF : C ⥤ D} {HL : E ⥤ F}
    {TX : B ⥤ D} {TY : A ⥤ C} {UX : D ⥤ F} {UY : C ⥤ E}
    {VX : B ⥤ F} {VY : A ⥤ E}
    (a : HE ⋙ TX ≅ TY ⋙ HF) (b : HF ⋙ UX ≅ UY ⋙ HL)
    (c : HE ⋙ VX ≅ VY ⋙ HL) (eX : TX ⋙ UX ≅ VX) (eY : TY ⋙ UY ≅ VY) : Prop :=
  ∀ K : A, eX.hom.app (HE.obj K) ≫ c.hom.app K =
    UX.map (a.hom.app K) ≫ b.hom.app (TY.obj K) ≫ HL.map (eY.hom.app K)

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- The existing raw rational constructible category, without idempotent completion.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
abbrev RCat (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :=
  sfRationalConstructibleCategory C.l E.val W
/-- The recorded localization of the integral finite-Tor category.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def Q (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) : Cat D C E W ⥤ RCat D C E W :=
  ConstructibleExceptionalCoefficients.rationalization C.l C.Qbar (fieldStage D C E) W
/-- The specified rational pullback, Tate line and even shift, in canonical coordinates.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def H (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  RationalSmoothPurityCanonical.rationalSource C.l E.val f d
/-- The specified rational compact-support and exceptional adjunction.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def O (E : AdicPurityScalarNaturality.Field D C) :
    ConstructibleExceptionalCoefficients.Operation C.l C.Qbar X Y
    (.rational (fieldStage D C E)) :=
  S.ring.operation (integralExceptionalCompactification D f) (.rational (fieldStage D C E))
/-- The exceptional right adjoint in that specified rational adjunction.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def G (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  (O D C f S E).G
/-- The recorded strict integral scalar functor followed by raw scalar localization.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def T (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (W : Scheme.{u}) :
    RCat D C E W ⥤ RCat D C F W :=
  sfRationalScalarExtension C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero
    F.val (IntermediateField.inclusion h)
/-- The actual coefficient-passage exceptional comparison of the recorded system.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def b (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    G D C f S E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ G D C f S F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).b
/-- The recorded integral-to-rational exceptional comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def gLocalization (E : AdicPurityScalarNaturality.Field D C) :
    target D C f S E ⋙ Q D C E X ≅ Q D C E Y ⋙ G D C f S E :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).b
/-- The compact-support coefficient comparison of the same recorded system.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def c (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    (O D C f S E).F ⋙ T D C E F h Y ≅ T D C E F h X ⋙ (O D C f S F).F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).q
/-- The specified rational scalar associator.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def alpha (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) (W : Scheme.{u}) :
    T D C E F h W ⋙ T D C F L k W ≅ T D C E L (h.trans k) W :=
  sfRationalScalarComp C.l E.val F.val (IntermediateField.inclusion h) W 0
    (Fact.out : C.l.Prime).ne_zero L.val (IntermediateField.inclusion k)
/-- The specified scalar tensor unitor for a repeated field.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def unit (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :
    T D C E E le_rfl W ≅ 𝟭 (RCat D C E W) :=
  sfRationalScalarUnit C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero

/-- The rational scalar shift fixed by its integral degree-one comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def tShift (E F : AdicPurityScalarNaturality.Field D C)
    (h : E ≤ F) (W : Scheme.{u}) :
    (T D C E F h W).CommShift ℤ :=
  RationalSmoothPurityCanonical.scalarShift C.l E.val F.val
    (IntermediateField.inclusion h) W
/-- The specified exceptional-adjunction shift comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def gShift (E : AdicPurityScalarNaturality.Field D C) : (G D C f S E).CommShift ℤ :=
  (O D C f S E).rightShift

/-- The source-scheme localization shift from the recorded adjunction comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def qXShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E X).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftX
/-- The target-scheme localization shift from the recorded adjunction comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def qYShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E Y).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftY
/-- These same localization shifts, selected by the recorded endpoint convention.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def qSideShift (E : AdicPurityScalarNaturality.Field D C) (side : Bool) :
    (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).CommShift ℤ :=
  match side with
  | true => qXShift D C f S E
  | false => qYShift D C f S E

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The counit transpose following the inverse compact-support scalar comparison.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def coefficientTranspose (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (K : RCat D C E Y) :
    (T D C E F h X).obj ((G D C f S E).obj K) ⟶
      (G D C f S F).obj ((T D C E F h Y).obj K) :=
  ((O D C f S F).adjunction.homEquiv
    ((T D C E F h X).obj ((G D C f S E).obj K)) ((T D C E F h Y).obj K))
    ((c D C f S E F h).inv.app ((G D C f S E).obj K) ≫
      (T D C E F h Y).map ((O D C f S E).adjunction.counit.app K))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The supplied integral exceptional comparison, with its endpoint functors explicit.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
@[irreducible] def integralB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    target D C f S E ⋙ scalar D C I.scalarClosed E F h true ≅
      scalar D C I.scalarClosed E F h false ⋙ target D C f S F :=
  I.b E F h

/-- The degree-zero integral Tate line before derived localization.
Source: smooth purity transport, the integral twist and shift identification
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def lineComplex (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) (m : ℤ) :=
  (CochainComplex.singleFunctor (integralTowerModules C.l E.val W) 0).obj
    (integralTwistLine C.l E.val W m)

/-- The actual twist-to-tensor comparison on complexes, with the line first and
with the entire shift on the line. The maps are the site-tensor identification,
sheaf tensor symmetry, the single-summand totalization, and the first tensor shift.
Source: smooth purity transport Step 2, the natural identification of the source
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def twistToShiftedTensor (E : AdicPurityScalarNaturality.Field D C)
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)] (m n : ℤ)
    (P : CochainComplex (integralTowerModules C.l E.val W) ℤ) :
    (((integralSheafTwist C.l E.val W m).mapHomologicalComplex (.up ℤ)).obj P)⟦n⟧ ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted C.l E.val W)).obj
          ((lineComplex D C E W m)⟦n⟧, P) :=
  let R := completedIntegralCommRingSheafUnrestricted C.l E.val W
  let L := integralTwistLine C.l E.val W m
  let F := MonoidalCategory.curriedTensor (integralTowerModules C.l E.val W)
  let e := SheafOfModules.siteSheafTensorRightIso R L ≪≫
    ((BraidedCategory.curriedBraidingNatIso (integralTowerModules C.l E.val W)).app L).symm
  (shiftFunctor _ n).mapIso ((NatIso.mapHomologicalComplex e (.up ℤ)).app P ≪≫
    (CochainComplex.mapBifunctorSingle₁Iso F L P).symm) ≪≫
      (CochainComplex.mapBifunctorShift₁Iso (lineComplex D C E W m) P F n).symm

/-- The canonical comparison between the localized shifted single complex and the
shifted integral Tate coefficient, using the ordinary derived localization shift.
Source: smooth purity transport Step 2
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def shiftedLineLocalization (E : AdicPurityScalarNaturality.Field D C)
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)] (m n : ℤ) :
    DerivedCategory.Q.obj ((lineComplex D C E W m)⟦n⟧) ≅
      (sfIntegralTwistingCoefficient C.l E.val W m).obj⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app (lineComplex D C E W m) ≪≫
    (shiftFunctor _ n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules C.l E.val W) 0).app
        (integralTwistLine C.l E.val W m)).symm

attribute [local irreducible] integralCompletedTensor integralOperationsTensorComplexFunctor
  RationalSmoothPurityCanonical.tensorAugmentation

/-- On every good representative, the integral source comparison is the exact
termwise twist, tensor symmetry, single totalization, shift, and completion map.
The representative is allowed to be any resolution of the actual integral pullback.
Source: smooth purity transport Step 2
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def integralSourceComparisonOnGood (E : AdicPurityScalarNaturality.Field D C)
    (K : Cat D C E Y)
    (P : CochainComplex (integralTowerModules C.l E.val X) ℤ)
    (hP : integralOperationsGoodComplex C.l E.val X P)
    (hL : integralOperationsGoodComplex C.l E.val X
      ((lineComplex D C E X (d : ℤ))⟦2 * (d : ℤ)⟧))
    (eP : DerivedCategory.Q.obj P ≅ (integralDerivedPullback C.l E.val f).obj K.obj) :
    ((source D C f d E).obj K).obj ⟶
      (integralCompletedTensor C.l E.val X).obj
        (((sfIntegralTwistingCoefficient C.l E.val X (d : ℤ))⟦2 * (d : ℤ)⟧).obj,
          (integralDerivedPullback C.l E.val f).obj K.obj) :=
  let F := integralSheafTwist C.l E.val X (d : ℤ)
  let n : ℤ := 2 * (d : ℤ)
  let L := (lineComplex D C E X (d : ℤ))⟦n⟧
  let t := integralCompletedTensor C.l E.val X
  let r : F.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    F.mapDerivedCategoryFactors.app P
  let s : (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))⟦n⟧ ≅
      DerivedCategory.Q.obj (((F.mapHomologicalComplex (.up ℤ)).obj P)⟦n⟧) :=
    (shiftFunctor _ n).mapIso r ≪≫
      ((DerivedCategory.Q.commShiftIso n).app _).symm
  let v : DerivedCategory.Q.obj
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted C.l E.val X)).obj (L, P)) ⟶
      t.obj (DerivedCategory.Q.obj L, DerivedCategory.Q.obj P) :=
    DerivedCategory.Q.map
      ((RationalSmoothPurityCanonical.tensorAugmentation C.l E.val X).app (L, P)) ≫
      (integralCompletedTensorComparison C.l E.val X).inv.app (⟨L, hL⟩, ⟨P, hP⟩)
  let w : (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))⟦n⟧ ⟶
      t.obj (DerivedCategory.Q.obj L, DerivedCategory.Q.obj P) :=
    s.hom ≫ DerivedCategory.Q.map
      (twistToShiftedTensor D C E X (d : ℤ) n P).hom ≫ v
  (shiftFunctor _ n).map (F.mapDerivedCategory.map eP.inv) ≫ w ≫
    t.map (Prod.mkHom ((shiftedLineLocalization D C E X (d : ℤ) n).hom ≫
      ((sfIntegralConstructible C.l E.val X).ι.commShiftIso n).inv.app
        (sfIntegralTwistingCoefficient C.l E.val X (d : ℤ))) eP.hom)

/-- The object identification from the defining object clauses of rational pullback
and rational tensor. The integral line is precisely sfIntegralTwistingCoefficient.
Source: smooth purity transport Step 2
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def sourceObjectIdentification (E : AdicPurityScalarNaturality.Field D C)
    (K : Cat D C E Y) :
    (H D C f d E).obj ((Q D C E Y).obj K) ≅
      (sfRationalConstructibleLocalization C.l E.val X).obj
        ((constructibleIntegralTensor C.l E.val X).obj
          ((sfIntegralTwistingCoefficient C.l E.val X (d : ℤ))⟦2 * (d : ℤ)⟧,
            (constructibleIntegralPullback C.l E.val f).obj
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E.val Y).obj K))) :=
  (rationalDerivedTensor C.l E.val X).mapIso
    (Iso.prod (((sfRationalConstructibleLocalization C.l E.val X).commShiftIso
      (2 * (d : ℤ))).symm.app (sfIntegralTwistingCoefficient C.l E.val X (d : ℤ)))
      (eqToIso
      ((rationalDerivedPullback_existsUnique C.l E.val f).exists.choose_spec.2.1
        ((Q D C E Y).obj K)))) ≪≫
    eqToIso ((rationalDerivedTensor_existsUnique C.l E.val X).exists.choose_spec.1 _)

/-- The source localization is pinned to the actual integral comparison on every
good representative. Existence of a good shifted-line model is included explicitly,
so the component normalization cannot be vacuous.
Source: smooth purity transport Step 2, localization of integral purity
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def SourceLocalizationNormalization (E : AdicPurityScalarNaturality.Field D C)
    (e : source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E) : Prop :=
  integralOperationsGoodComplex C.l E.val X
    ((lineComplex D C E X (d : ℤ))⟦2 * (d : ℤ)⟧) ∧
  ∀ (K : Cat D C E Y)
    (P : CochainComplex (integralTowerModules C.l E.val X) ℤ)
    (hP : integralOperationsGoodComplex C.l E.val X P)
    (hL : integralOperationsGoodComplex C.l E.val X
      ((lineComplex D C E X (d : ℤ))⟦2 * (d : ℤ)⟧))
    (eP : DerivedCategory.Q.obj P ≅ (integralDerivedPullback C.l E.val f).obj K.obj),
    e.hom.app K ≫ (sourceObjectIdentification D C f d E K).hom =
      (sfRationalConstructibleLocalization C.l E.val X).map
        (ObjectProperty.homMk (integralSourceComparisonOnGood D C f d E K P hP hL eP))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  WeilConjectures.AdicPurityScalarNaturality.target
  WeilConjectures.AdicPurityScalarNaturality.source
  WeilConjectures.RationalSmoothPurityCanonical.rationalSource



end WeilConjectures.RationalScalarComparisonIdentification
