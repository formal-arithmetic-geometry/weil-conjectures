# WeilConjectures.RationalScalarComparisonIdentification coordinate declarations

## Reason

The source/scalar localization and descent lemmas need the original coordinate definitions.
Keeping those definitions beside the theorem would make the helper imports cyclic. Move only
these declarations to `Sheaf.Paper.RationalScalarComparisonData` and publicly import that
module from the original module. `Result` and `rationalScalarComparisonIdentification` remain
in the original module. Every moved name, signature, body and exposure is preserved; there is
no change to the mathematical meaning of a target or to an existing definition.
The helper statements are new, strictly partial steps of the original argument.
Unused private proof imports are removed from the coordinate-only module.
For coefficientTranspose, elaboration respects the existing irreducibility annotations,
preventing the adjunction coordinates from expanding during definitional equality checks.
The subsequent integral source-map declarations retain their original transparency setting.

## Old

The following declarations were in `Sheaf.Paper.RationalScalarComparisonIdentification`:

```lean
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



def PuritySquares {A B C D : Type uR}
    [Category.{vR} A] [Category.{vR} B] [Category.{vR} C] [Category.{vR} D]
    {HE GE : A ⥤ B} {HF GF : C ⥤ D} {TX : B ⥤ D} {TY : A ⥤ C}
    (eE : HE ≅ GE) (eF : HF ≅ GF)
    (a : HE ⋙ TX ≅ TY ⋙ HF) (b : GE ⋙ TX ≅ TY ⋙ GF) : Prop :=
  (∀ K : A, TX.map (eE.hom.app K) ≫ b.hom.app K =
    a.hom.app K ≫ eF.hom.app (TY.obj K)) ∧
  (∀ K : A, b.inv.app K ≫ TX.map (eE.inv.app K) =
    eF.inv.app (TY.obj K) ≫ a.inv.app K)



def UnitEquation {A B : Type uR} [Category.{vR} A] [Category.{vR} B]
    {H : A ⥤ B} {TX : B ⥤ B} {TY : A ⥤ A}
    (a : H ⋙ TX ≅ TY ⋙ H) (uX : TX ≅ 𝟭 B) (uY : TY ≅ 𝟭 A) : Prop :=
  ∀ K : A, a.hom.app K ≫ H.map (uY.hom.app K) = uX.hom.app (H.obj K)



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



abbrev RCat (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :=
  sfRationalConstructibleCategory C.l E.val W


def Q (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) : Cat D C E W ⥤ RCat D C E W :=
  ConstructibleExceptionalCoefficients.rationalization C.l C.Qbar (fieldStage D C E) W


def H (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  RationalSmoothPurityCanonical.rationalSource C.l E.val f d


def O (E : AdicPurityScalarNaturality.Field D C) :
    ConstructibleExceptionalCoefficients.Operation C.l C.Qbar X Y
    (.rational (fieldStage D C E)) :=
  S.ring.operation (integralExceptionalCompactification D f) (.rational (fieldStage D C E))


def G (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  (O D C f S E).G


def T (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (W : Scheme.{u}) :
    RCat D C E W ⥤ RCat D C F W :=
  sfRationalScalarExtension C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero
    F.val (IntermediateField.inclusion h)


def b (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    G D C f S E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ G D C f S F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).b


def gLocalization (E : AdicPurityScalarNaturality.Field D C) :
    target D C f S E ⋙ Q D C E X ≅ Q D C E Y ⋙ G D C f S E :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).b


def c (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    (O D C f S E).F ⋙ T D C E F h Y ≅ T D C E F h X ⋙ (O D C f S F).F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).q


def alpha (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) (W : Scheme.{u}) :
    T D C E F h W ⋙ T D C F L k W ≅ T D C E L (h.trans k) W :=
  sfRationalScalarComp C.l E.val F.val (IntermediateField.inclusion h) W 0
    (Fact.out : C.l.Prime).ne_zero L.val (IntermediateField.inclusion k)


def unit (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :
    T D C E E le_rfl W ≅ 𝟭 (RCat D C E W) :=
  sfRationalScalarUnit C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero



def tShift (E F : AdicPurityScalarNaturality.Field D C)
    (h : E ≤ F) (W : Scheme.{u}) :
    (T D C E F h W).CommShift ℤ :=
  RationalSmoothPurityCanonical.scalarShift C.l E.val F.val
    (IntermediateField.inclusion h) W


def gShift (E : AdicPurityScalarNaturality.Field D C) : (G D C f S E).CommShift ℤ :=
  (O D C f S E).rightShift



def qXShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E X).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftX


def qYShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E Y).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftY


def qSideShift (E : AdicPurityScalarNaturality.Field D C) (side : Bool) :
    (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).CommShift ℤ :=
  match side with
  | true => qXShift D C f S E
  | false => qYShift D C f S E



def coefficientTranspose (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (K : RCat D C E Y) :
    (T D C E F h X).obj ((G D C f S E).obj K) ⟶
      (G D C f S F).obj ((T D C E F h Y).obj K) :=
  ((O D C f S F).adjunction.homEquiv
    ((T D C E F h X).obj ((G D C f S E).obj K)) ((T D C E F h Y).obj K))
    ((c D C f S E F h).inv.app ((G D C f S E).obj K) ≫
      (T D C E F h Y).map ((O D C f S E).adjunction.counit.app K))



def integralB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    target D C f S E ⋙ scalar D C I.scalarClosed E F h true ≅
      scalar D C I.scalarClosed E F h false ⋙ target D C f S F :=
  I.b E F h



def lineComplex (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) (m : ℤ) :=
  (CochainComplex.singleFunctor (integralTowerModules C.l E.val W) 0).obj
    (integralTwistLine C.l E.val W m)



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



def shiftedLineLocalization (E : AdicPurityScalarNaturality.Field D C)
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)] (m n : ℤ) :
    DerivedCategory.Q.obj ((lineComplex D C E W m)⟦n⟧) ≅
      (sfIntegralTwistingCoefficient C.l E.val W m).obj⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app (lineComplex D C E W m) ≪≫
    (shiftFunctor _ n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules C.l E.val W) 0).app
        (integralTwistLine C.l E.val W m)).symm



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


```

## New

The identical declarations are now in `Sheaf.Paper.RationalScalarComparisonData`:

```lean
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



def PuritySquares {A B C D : Type uR}
    [Category.{vR} A] [Category.{vR} B] [Category.{vR} C] [Category.{vR} D]
    {HE GE : A ⥤ B} {HF GF : C ⥤ D} {TX : B ⥤ D} {TY : A ⥤ C}
    (eE : HE ≅ GE) (eF : HF ≅ GF)
    (a : HE ⋙ TX ≅ TY ⋙ HF) (b : GE ⋙ TX ≅ TY ⋙ GF) : Prop :=
  (∀ K : A, TX.map (eE.hom.app K) ≫ b.hom.app K =
    a.hom.app K ≫ eF.hom.app (TY.obj K)) ∧
  (∀ K : A, b.inv.app K ≫ TX.map (eE.inv.app K) =
    eF.inv.app (TY.obj K) ≫ a.inv.app K)



def UnitEquation {A B : Type uR} [Category.{vR} A] [Category.{vR} B]
    {H : A ⥤ B} {TX : B ⥤ B} {TY : A ⥤ A}
    (a : H ⋙ TX ≅ TY ⋙ H) (uX : TX ≅ 𝟭 B) (uY : TY ≅ 𝟭 A) : Prop :=
  ∀ K : A, a.hom.app K ≫ H.map (uY.hom.app K) = uX.hom.app (H.obj K)



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



abbrev RCat (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :=
  sfRationalConstructibleCategory C.l E.val W


def Q (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) : Cat D C E W ⥤ RCat D C E W :=
  ConstructibleExceptionalCoefficients.rationalization C.l C.Qbar (fieldStage D C E) W


def H (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  RationalSmoothPurityCanonical.rationalSource C.l E.val f d


def O (E : AdicPurityScalarNaturality.Field D C) :
    ConstructibleExceptionalCoefficients.Operation C.l C.Qbar X Y
    (.rational (fieldStage D C E)) :=
  S.ring.operation (integralExceptionalCompactification D f) (.rational (fieldStage D C E))


def G (E : AdicPurityScalarNaturality.Field D C) : RCat D C E Y ⥤ RCat D C E X :=
  (O D C f S E).G


def T (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (W : Scheme.{u}) :
    RCat D C E W ⥤ RCat D C F W :=
  sfRationalScalarExtension C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero
    F.val (IntermediateField.inclusion h)


def b (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    G D C f S E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ G D C f S F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).b


def gLocalization (E : AdicPurityScalarNaturality.Field D C) :
    target D C f S E ⋙ Q D C E X ≅ Q D C E Y ⋙ G D C f S E :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).b


def c (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    (O D C f S E).F ⋙ T D C E F h Y ≅ T D C E F h X ⋙ (O D C f S F).F :=
  (S.fields.rationalComparison (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)).q


def alpha (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) (W : Scheme.{u}) :
    T D C E F h W ⋙ T D C F L k W ≅ T D C E L (h.trans k) W :=
  sfRationalScalarComp C.l E.val F.val (IntermediateField.inclusion h) W 0
    (Fact.out : C.l.Prime).ne_zero L.val (IntermediateField.inclusion k)


def unit (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) :
    T D C E E le_rfl W ≅ 𝟭 (RCat D C E W) :=
  sfRationalScalarUnit C.l E.val W 0 (Fact.out : C.l.Prime).ne_zero



def tShift (E F : AdicPurityScalarNaturality.Field D C)
    (h : E ≤ F) (W : Scheme.{u}) :
    (T D C E F h W).CommShift ℤ :=
  RationalSmoothPurityCanonical.scalarShift C.l E.val F.val
    (IntermediateField.inclusion h) W


def gShift (E : AdicPurityScalarNaturality.Field D C) : (G D C f S E).CommShift ℤ :=
  (O D C f S E).rightShift



def qXShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E X).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftX


def qYShift (E : AdicPurityScalarNaturality.Field D C) : (Q D C E Y).CommShift ℤ :=
  (S.fields.rationalizationComparison (integralExceptionalCompactification D f)
    (fieldStage D C E)).shiftY


def qSideShift (E : AdicPurityScalarNaturality.Field D C) (side : Bool) :
    (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).CommShift ℤ :=
  match side with
  | true => qXShift D C f S E
  | false => qYShift D C f S E



def coefficientTranspose (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (K : RCat D C E Y) :
    (T D C E F h X).obj ((G D C f S E).obj K) ⟶
      (G D C f S F).obj ((T D C E F h Y).obj K) :=
  ((O D C f S F).adjunction.homEquiv
    ((T D C E F h X).obj ((G D C f S E).obj K)) ((T D C E F h Y).obj K))
    ((c D C f S E F h).inv.app ((G D C f S E).obj K) ≫
      (T D C E F h Y).map ((O D C f S E).adjunction.counit.app K))



def integralB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    target D C f S E ⋙ scalar D C I.scalarClosed E F h true ≅
      scalar D C I.scalarClosed E F h false ⋙ target D C f S F :=
  I.b E F h



def lineComplex (E : AdicPurityScalarNaturality.Field D C) (W : Scheme.{u}) (m : ℤ) :=
  (CochainComplex.singleFunctor (integralTowerModules C.l E.val W) 0).obj
    (integralTwistLine C.l E.val W m)



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



def shiftedLineLocalization (E : AdicPurityScalarNaturality.Field D C)
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)] (m n : ℤ) :
    DerivedCategory.Q.obj ((lineComplex D C E W m)⟦n⟧) ≅
      (sfIntegralTwistingCoefficient C.l E.val W m).obj⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app (lineComplex D C E W m) ≪≫
    (shiftFunctor _ n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules C.l E.val W) 0).app
        (integralTwistLine C.l E.val W m)).symm



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


```

The original module starts with `public import Sheaf.Paper.RationalScalarComparisonData`.
The original `Result` definition and theorem signature are unchanged. All original public
imports remain transitively public through the data module. The five new helper modules
publicly import the data module; the theorem imports those helpers privately.

## Users

`tools/downstream.py Sheaf.Paper.RationalScalarComparisonIdentification` reports zero current
Lean importers. Pending DAG parents retain the original theorem and its full statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Publicly re-exports the moved definitions; proves the original theorem from five strict intermediate steps. |
| Sheaf.Paper.RationalScalarComparisonData | new, E1 | Hosts the verbatim coordinate definitions. |
| Sheaf.Paper.RationalPuritySourceLocalization | new, E1 | States normalized source localization using the same definitions. |
| Sheaf.Paper.RationalPurityScalarLocalization | new, E1 | States normalized scalar localization using the same definitions. |
| Sheaf.Paper.RationalPurityComparisonDescent | new, E1 | States descent of the comparison maps. |
| Sheaf.Paper.RationalPurityCoherenceDescent | new, E1 | States descent of the forward square and source coherence. |
| Sheaf.Paper.RationalExceptionalFinalEquations | new, E1 | States the remaining fixed system equations. |

## Status

landed 20261025T122802-L-1807300 2026-10-25 (merge of deliver/E1/Sheaf.Paper.RationalScalarComparisonIdentification)
