# PodCommonStageReconstruction: separate the comparison interface from coherence

## Reason

The scalar comparison normalization step needs the existing Realization and
SameIndexRealization predicates, and the main theorem must import that new step.
Move the existing definitions into PodReconstructionCommonStageData and
publicly reexport them from the original module. This prevents an import cycle;
it is not a compile-time split. The original theorem signature and all existing definition signatures stay
identical. The object, representative and Coherence bodies factor through their
identical formulas over an abstract stage system. A diagnostic proof specialized
from the generic categorical argument timed out in kernel conversion; this
factoring lets the kernel compare the same predicate applied to the same arguments
without repeatedly unfolding coefficient categories and scalar transitions.
It is a definition interface optimization, with no mathematical change.
Other definition bodies, attributes and visibility stay identical. The new scalar theorem covers
only the actual finite-stage comparison normalization. The categorical coherence,
representative transport, descent and natural isomorphism are proved in the item.
No definition chooses data from a mere existence theorem. The local witness family
in the theorem proof is fixed by the supplied actual realization predicates.

## Old

The original module publicly imports:

```lean
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.CompletionUnitStrictQuotientModel
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PodReconstructionRawRationalNaturality
public import Sheaf.Paper.PodCompletionUnitScalarIntertwining
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfScalarExtensionComposition

```

The following declarations are in the original module:

```lean
/-- The actual integral restriction and raw rationalization, with their actual units.
The two predicates are the recorded dependency predicates, not new notions of completion.
Source: blueprint opening sentence, finite-stage reconstruction
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
structure Realization (E : Index l Ω)
    (A : CoefficientDerivedSystemCalculus l (Coefficient.{u} l Ω E) (point D)) where
  integral : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D) ⥤
    sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D)
  integralUnit : 𝟭 _ ≅ integral
  integral_actual : IntegralRealization D l (Coefficient.{u} l Ω E) A integral integralUnit
  rational : Stage l Ω (point D) E ⥤ Stage l Ω (point D) E
  rationalUnit : 𝟭 _ ≅ rational
  rational_actual : RationalRealization D l (Coefficient.{u} l Ω E)
    integral integralUnit rational rationalUnit

/-- The full strict identity-tower identification from the raw-rational dependency.
In particular its integral comparison has the recorded Roos projections, and the
rational comparison is its localization on every object.
Source: blueprint opening sentence, identity compactification
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def IdentitySupport (E : Index l Ω)
    (A : CoefficientDerivedSystemCalculus l (Coefficient.{u} l Ω E) (point D))
    (R : Realization D l Ω E A) : Prop :=
    ∃ (hk : IsUnit (l : D.k))
      (T : DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) (point D)) ⥤
        coefficientSequenceRestrictedDerived l (Coefficient.{u} l Ω E) (point D))
      (e : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l (Coefficient.{u} l Ω E) (point D) n ≅
        compactSupportRestrictedLevel l (Coefficient.{u} l Ω E)
          (Compactification.ofIsProper (𝟙 (point D))) n)
      (θ : A.reduction ⋙
        coefficientSequenceDerivedRestriction l (Coefficient.{u} l Ω E) (point D) ≅ T)
      (ρ : sfCompactSupportFiniteIntegralFunctor l D.k
          hk (Compactification.ofIsProper (𝟙 (point D))) (Coefficient.{u} l Ω E) ⋙
            (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι ≅
        (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι ⋙ T ⋙
          coefficientConstantTowerLimit l (Coefficient.{u} l Ω E) (point D))
      (η : R.integral ⋙ (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι ≅
        (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι ⋙
          completion.{u, u} D l (Coefficient.{u} l Ω E) A)
      (κ : R.integral ≅ sfCompactSupportFiniteIntegralFunctor l D.k
        hk (Compactification.ofIsProper (𝟙 (point D))) (Coefficient.{u} l Ω E))
      (κRat : R.rational ≅ sfCompactSupportFiniteFunctor l D.k
        hk (Compactification.ofIsProper (𝟙 (point D))) (Coefficient.{u} l Ω E)),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l (Coefficient.{u} l Ω E) D.k (point D) (point D)
          (𝟙 (point D)) hk
          (Compactification.ofIsProper (𝟙 (point D)))))).2.2 ∧
      (∀ (C : DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) (point D))) (n : ℕ),
        (coefficientConstantTowerEvaluation l (Coefficient.{u} l Ω E) (point D) n).map
            (θ.hom.app C) ≫
            (e n).hom.app C ≫ (finiteRestrictedIdentity D l (Coefficient.{u} l Ω E) n).hom.app C =
          (coefficientRestrictedEvaluationIso l (Coefficient.{u} l Ω E) (point D) n).hom.app
              (A.reduction.obj C) ≫
            (scalarReductionDerivedRestriction l (Coefficient.{u} l Ω E) (point D) n).map
              ((A.reductionEvaluation n).hom.app C)) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (C : DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) (point D))),
        (pbcTowerTransition (point D)
            (completedIntegralCommRingSheafUnrestricted l
              (Coefficient.{u} l Ω E) (point D)) m n h).app
              (T.obj C) ≫ (e n).hom.app C =
          (e m).hom.app C ≫ compactSupportRestrictedTransition l (Coefficient.{u} l Ω E)
            (Compactification.ofIsProper (𝟙 (point D))) m n h C) ∧
      (∀ C, HEq (η.hom.app C) (𝟙 ((completion.{u, u} D l (Coefficient.{u} l Ω E) A).obj C.obj))) ∧
      isoWhiskerRight κ (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι ≪≫ ρ =
        η ≪≫ isoWhiskerLeft (sfIntegralConstructible l (Coefficient.{u} l Ω E) (point D)).ι
          (isoWhiskerRight θ (coefficientConstantTowerLimit l (Coefficient.{u} l Ω E) (point D))) ∧
      (∀ (C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D)) (n : ℕ),
        HEq (ρ.hom.app C ≫
            (coefficientConstantTowerProjection l (Coefficient.{u} l Ω E) (point D) n).app
                (T.obj C.obj) ≫
              (e n).hom.app C.obj)
          (Classical.choose (Classical.choose_spec
            (exists_isDerivedLimit_and_iso
              (sfCompactSupportTerm l (Coefficient.{u} l Ω E)
                (Compactification.ofIsProper (𝟙 (point D))) C.obj)
              (sfCompactSupportTransition l (Coefficient.{u} l Ω E)
                (Compactification.ofIsProper (𝟙 (point D))) C.obj)).1) ≫
            Pi.π (sfCompactSupportTerm l (Coefficient.{u} l Ω E)
              (Compactification.ofIsProper (𝟙 (point D))) C.obj) n)) ∧
      ∀ C : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (point D),
        HEq (κRat.hom.app C)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) (point D)).map
            (κ.hom.app C.obj))

/-- The canonical scalar unit on the published stage system, transported by its
specified equality with the completed scalar functor.
Source: blueprint opening sentence, identity-extension equation
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def scalarUnit (E : Index l Ω) :
    stageTransition l Ω (point D) E E le_rfl ≅ 𝟭 (Stage l Ω (point D) E) :=
  eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω (point D)).exists.choose_spec.1 E E le_rfl) ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω (point D) E

variable
  (A : ∀ E : Index l Ω,
    CoefficientDerivedSystemCalculus l (Coefficient.{u} l Ω E) (point D))

/-- The existing quotient-model completion with its ringed-site parameters explicit.
Source: blueprint opening sentence, strict quotient model
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
abbrev quotientEndofunctor (E : Index l Ω)
    (CR : quotientModel.{u, u} D l (Coefficient.{u} l Ω E)) :=
  @CategoryTheory.PrincipalQuotientCompletion.Model.completion.{u + 1, u, u + 1, u + 2}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbSheafify.{u, u} (point D))
    (integralCoefficientAbLocallyBijective.{u, u} (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l (Coefficient.{u} l Ω E) (point D)) CR

/-- The existing change-of-rings model projection with explicit site parameters.
Source: blueprint opening sentence, scalar realization
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
abbrev scalarDerived (E L : Index l Ω) (h : E ≤ L)
    (F : scalarModel.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)) :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.T.{u + 1, u, u + 1, u + 2, u + 2}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbLocallyBijective.{u, u} (point D))
    (integralCoefficientAbSheafify.{u, u} (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω L) (point D))
    (completedCoefficientMap.{u, u} l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω L) (point D)) F

/-- The existing change-of-rings model projection with explicit site parameters.
Source: blueprint opening sentence, scalar realization
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
abbrev scalarOrdinary (E L : Index l Ω) (h : E ≤ L)
    (F : scalarModel.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)) :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.E.{u + 1, u, u + 1, u + 2, u + 2}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbLocallyBijective.{u, u} (point D))
    (integralCoefficientAbSheafify.{u, u} (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω L) (point D))
    (completedCoefficientMap.{u, u} l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω L) (point D)) F

/-- The existing change-of-rings model projection with explicit site parameters.
Source: blueprint opening sentence, scalar realization
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
abbrev scalarCounit (E L : Index l Ω) (h : E ≤ L)
    (F : scalarModel.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)) :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.ε.{u + 1, u, u + 1, u + 2, u + 2}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbLocallyBijective.{u, u} (point D))
    (integralCoefficientAbSheafify.{u, u} (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (completedIntegralCommRingSheafUnrestricted.{u, u} l (Coefficient.{u} l Ω L) (point D))
    (completedCoefficientMap.{u, u} l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (integralTowerHasDerivedCategory.{u, u} l (Coefficient.{u} l Ω L) (point D)) F

/-- Retain the specified same-index quotient-cone construction of the integral
comparison. The dependency predicates specify the actual quotient augmentations,
balanced residue maps, and both signed Roos coordinates before localization.
The last equation is its prescribed completed conjugation on each integral object.
Source: blueprint opening sentence, actual coefficient comparisons
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def SameIndexRealization (R : ∀ E, Realization D l Ω E (A E))
    (E L : Index l Ω) (h : E ≤ L)
    (b : (R E).integral ⋙ integralTransition l Ω (point D) E L h ≅
      integralTransition l Ω (point D) E L h ⋙ (R L).integral) : Prop :=
  ∃ (ME : CompletionUnit.OrdinaryModel.{u, u} l (Coefficient.{u} l Ω E) (point D))
    (ML : CompletionUnit.OrdinaryModel.{u, u} l (Coefficient.{u} l Ω L) (point D))
    (NE : CompletionUnit.DerivedModel.{u, u} l (Coefficient.{u} l Ω E) (point D) (A E) ME)
    (NL : CompletionUnit.DerivedModel.{u, u} l (Coefficient.{u} l Ω L) (point D) (A L) ML)
    (CR : quotientModel.{u, u} D l (Coefficient.{u} l Ω E))
    (CS : quotientModel.{u, u} D l (Coefficient.{u} l Ω L))
    (α : (quotientEndofunctor D l Ω E CR) ≅ completion.{u, u} D l (Coefficient.{u} l Ω E) (A E))
    (γ : (quotientEndofunctor D l Ω L CS) ≅ completion.{u, u} D l (Coefficient.{u} l Ω L) (A L))
    (F : scalarModel.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h))
    (hF : scalarOrdinary D l Ω E L h F = completedOrdinaryScalarExtension.{u, u} l
      (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D))
    (σ : scalarDerived D l Ω E L h F ≅ completedDerivedScalarExtension.{u, u} l
      (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D))
    (d : quotientEndofunctor D l Ω E CR ⋙ scalarDerived D l Ω E L h F ⟶
      scalarDerived D l Ω E L h F ⋙ quotientEndofunctor D l Ω L CS),
    QuotientRealization.{u, u} D l (Coefficient.{u} l Ω E) (A E) ME NE CR α ∧
    QuotientRealization.{u, u} D l (Coefficient.{u} l Ω L) (A L) ML NL CS γ ∧
    (∀ P : CochainComplex (integralTowerModules.{u, u} l (Coefficient.{u} l Ω E) (point D)) ℤ,
      σ.hom.app (DerivedCategory.Q.obj P) ≫
          completedScalarCounit.{u, u} l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) (point D) P =
        (scalarCounit D l Ω E L h F).app P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (eqToIso hF) (.up ℤ)).hom.app P)) ∧
    (∀ P : (integralOperationsGoodComplex.{u, u} l
      (Coefficient.{u} l Ω E) (point D)).FullSubcategory,
      SameIndexFormula.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) F CR CS d P.obj) ∧
    ∀ C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D),
      ∃ (χ : (completedDerivedScalarExtension.{u, u} l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).obj C.obj ≅
          (integralScalarExtensionOfUniverses.{u, u} l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).obj C.obj)
        (χH : (completedDerivedScalarExtension.{u, u} l (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).obj
                ((completion.{u, u} D l (Coefficient.{u} l Ω E) (A E)).obj C.obj) ≅
          (integralScalarExtensionOfUniverses.{u, u} l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).obj
              ((completion.{u, u} D l (Coefficient.{u} l Ω E) (A E)).obj C.obj)),
        χ.hom = (completedScalarComparison.{u, u} l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).app C.obj ∧
        χH.hom = (completedScalarComparison.{u, u} l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (point D)).app
            ((completion.{u, u} D l (Coefficient.{u} l Ω E) (A E)).obj C.obj) ∧
        HEq (b.hom.app C).hom
          (χH.inv ≫ (actualSameIndex.{u, u} D l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) (A E) (A L) F σ CR CS α γ d).app C.obj ≫
              (completion.{u, u} D l (Coefficient.{u} l Ω L) (A L)).map χ.hom)

/-- The object formula, retaining the same finite coefficient field.
Source: blueprint opening sentence, common-stage descent
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def object (R : ∀ E, Realization D l Ω E (A E))
    (X : (stageSystem l Ω (point D)).PairCategory) :
    (stageSystem l Ω (point D)).PairCategory :=
  ⟨X.stage, (R X.stage).rational.obj X.obj⟩

/-- The displayed comparison-conjugated representative, in Lean composition order.
Source: blueprint opening sentence, common-stage representative formula
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def representative (R : ∀ E, Realization D l Ω E (A E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
        stageTransition l Ω (point D) E L h ⋙ (R L).rational)
    (X Y : (stageSystem l Ω (point D)).PairCategory)
    (F : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY) :
    (object D l Ω A R X).toStage hX ⟶ (object D l Ω A R Y).toStage hY :=
  (β X.stage F hX).hom.app X.obj ≫ (R F).rational.map f ≫
    (β Y.stage F hY).inv.app Y.obj

/-- The actual comparisons satisfy scalar coherence and descend with the stated
object, arrow, unit, and inverse-unit formulas. The transition equation is asserted
before passing to classes, so it includes preservation by every further extension.
Source: blueprint opening sentence, identity compact support
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def Coherence (R : ∀ E, Realization D l Ω E (A E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
        stageTransition l Ω (point D) E L h ⋙ (R L).rational) : Prop :=
  (∀ (E : Index l Ω) (C : Stage l Ω (point D) E),
    (β E E le_rfl).hom.app C ≫
        (R E).rational.map ((scalarUnit D l Ω E).hom.app C) =
      (scalarUnit D l Ω E).hom.app ((R E).rational.obj C)) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (C : Stage l Ω (point D) E),
    (stageTransition l Ω (point D) L M k).map ((β E L h).hom.app C) ≫
        (β L M k).hom.app ((stageTransition l Ω (point D) E L h).obj C) ≫
        (R M).rational.map (((stageSystem l Ω (point D)).assoc h k).hom.app C) =
      ((stageSystem l Ω (point D)).assoc h k).hom.app ((R E).rational.obj C) ≫
        (β E M (h.trans k)).hom.app C) ∧
  (∀ (X Y : (stageSystem l Ω (point D)).PairCategory)
    (F G : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F) (h : F ≤ G)
    (f : X.toStage hX ⟶ Y.toStage hY),
    (stageSystem l Ω (point D)).tr h (representative D l Ω A R β X Y F hX hY f) =
      representative D l Ω A R β X Y G (hX.trans h) (hY.trans h)
        ((stageSystem l Ω (point D)).tr h f)) ∧
  (∀ (X Y : (stageSystem l Ω (point D)).PairCategory)
    (F : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY),
    (R F).rational.map f ≫ (R F).rationalUnit.inv.app (Y.toStage hY) =
      (R F).rationalUnit.inv.app (X.toStage hX) ≫ f) ∧
  (∀ (X Y : (stageSystem l Ω (point D)).PairCategory)
    (F : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY),
    representative D l Ω A R β X Y F hX hY f ≫
        (stageTransition l Ω (point D) Y.stage F hY).map
          ((R Y.stage).rationalUnit.inv.app Y.obj) =
      (stageTransition l Ω (point D) X.stage F hX).map
          ((R X.stage).rationalUnit.inv.app X.obj) ≫ f) ∧
  ∃ (H : (stageSystem l Ω (point D)).PairCategory ⥤
      (stageSystem l Ω (point D)).PairCategory)
    (v : H ≅ 𝟭 ((stageSystem l Ω (point D)).PairCategory)),
    (∀ X, H.obj X = object D l Ω A R X) ∧
    (∀ (X Y : (stageSystem l Ω (point D)).PairCategory)
      (F : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
      (f : X.toStage hX ⟶ Y.toStage hY),
      HEq (H.map (CategoryTheory.StageSystem.PairCategory.mkHom F hX hY f))
        (CategoryTheory.StageSystem.PairCategory.mkHom
          (X := object D l Ω A R X) (Y := object D l Ω A R Y) F hX hY
          (representative D l Ω A R β X Y F hX hY f))) ∧
    (∀ X : (stageSystem l Ω (point D)).PairCategory,
      HEq (v.hom.app X) (((stageSystem l Ω (point D)).ι X.stage).map
        ((R X.stage).rationalUnit.inv.app X.obj)) ∧
      HEq (v.inv.app X) (((stageSystem l Ω (point D)).ι X.stage).map
        ((R X.stage).rationalUnit.hom.app X.obj))) ∧
    ∀ (X Y : (stageSystem l Ω (point D)).PairCategory) (f : X ⟶ Y),
      H.map f ≫ v.hom.app Y = v.hom.app X ≫ f

```

## New

The old definitions, except the final three displayed below, move verbatim to
Sheaf.Paper.PodReconstructionCommonStageData. The original module publicly imports
this data module and privately imports the scalar sublemma and the proved
StageSystem.Functor API. The new generic definitions and specializations are:

```lean
section Generic
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category (C i)]
  (S : StageSystem C) (H : ∀ i, C i ⥤ C i) (unit : ∀ i, 𝟭 (C i) ≅ H i)
  (e : ∀ i, S.T (i := i) le_rfl ≅ 𝟭 (C i))

/-- Stage-preserving object formula for a family of endofunctors.
Source: blueprint common-stage descent, object part
(blueprint: def-pod-reconstruction-common-stage-data). -/
def stageObject (X : S.PairCategory) : S.PairCategory :=
  ⟨X.stage, (H X.stage).obj X.obj⟩

/-- Comparison-conjugated arrow at a common stage.
Source: blueprint common-stage descent, representative part
(blueprint: def-pod-reconstruction-common-stage-data). -/
def stageRepresentative
    (β : ∀ (E L : I) (h : E ≤ L), H E ⋙ S.T h ≅ S.T h ⋙ H L)
    (X Y : S.PairCategory) (F : I) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY) :
    (stageObject S H X).toStage hX ⟶ (stageObject S H Y).toStage hY :=
  (β X.stage F hX).hom.app X.obj ≫ (H F).map f ≫ (β Y.stage F hY).inv.app Y.obj

/-- Unit, associator, representative and descent equations for a family on a stage system.
This generic form keeps the coefficient categories abstract during type checking.
Source: blueprint common-stage descent, Steps 2--7
(blueprint: def-pod-reconstruction-common-stage-data). -/
def stageCoherence
    (β : ∀ (E L : I) (h : E ≤ L), H E ⋙ S.T h ≅ S.T h ⋙ H L) : Prop :=
  (∀ (E : I) (C : C E),
    (β E E le_rfl).hom.app C ≫
        (H E).map ((e E).hom.app C) =
      (e E).hom.app ((H E).obj C)) ∧
  (∀ (E L M : I) (h : E ≤ L) (k : L ≤ M)
    (C : C E),
    (S.T k).map ((β E L h).hom.app C) ≫
        (β L M k).hom.app ((S.T h).obj C) ≫
        (H M).map ((S.assoc h k).hom.app C) =
      (S.assoc h k).hom.app ((H E).obj C) ≫
        (β E M (h.trans k)).hom.app C) ∧
  (∀ (X Y : S.PairCategory)
    (F G : I) (hX : X.stage ≤ F) (hY : Y.stage ≤ F) (h : F ≤ G)
    (f : X.toStage hX ⟶ Y.toStage hY),
    S.tr h (stageRepresentative S H β X Y F hX hY f) =
      stageRepresentative S H β X Y G (hX.trans h) (hY.trans h)
        (S.tr h f)) ∧
  (∀ (X Y : S.PairCategory)
    (F : I) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY),
    (H F).map f ≫ (unit F).inv.app (Y.toStage hY) =
      (unit F).inv.app (X.toStage hX) ≫ f) ∧
  (∀ (X Y : S.PairCategory)
    (F : I) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY),
    stageRepresentative S H β X Y F hX hY f ≫
        (S.T hY).map
          ((unit Y.stage).inv.app Y.obj) =
      (S.T hX).map
          ((unit X.stage).inv.app X.obj) ≫ f) ∧
  ∃ (Ftotal : S.PairCategory ⥤
      S.PairCategory)
    (v : Ftotal ≅ 𝟭 (S.PairCategory)),
    (∀ X, Ftotal.obj X = stageObject S H X) ∧
    (∀ (X Y : S.PairCategory)
      (F : I) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
      (f : X.toStage hX ⟶ Y.toStage hY),
      HEq (Ftotal.map (CategoryTheory.StageSystem.PairCategory.mkHom F hX hY f))
        (CategoryTheory.StageSystem.PairCategory.mkHom
          (X := stageObject S H X) (Y := stageObject S H Y) F hX hY
          (stageRepresentative S H β X Y F hX hY f))) ∧
    (∀ X : S.PairCategory,
      HEq (v.hom.app X) ((S.ι X.stage).map
        ((unit X.stage).inv.app X.obj)) ∧
      HEq (v.inv.app X) ((S.ι X.stage).map
        ((unit X.stage).hom.app X.obj))) ∧
    ∀ (X Y : S.PairCategory) (f : X ⟶ Y),
      Ftotal.map f ≫ v.hom.app Y = v.hom.app X ≫ f


end Generic

/-- The object formula, retaining the same finite coefficient field.
Source: blueprint opening sentence, common-stage descent
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def object (R : ∀ E, Realization D l Ω E (A E))
    (X : (stageSystem l Ω (point D)).PairCategory) :
    (stageSystem l Ω (point D)).PairCategory :=
  stageObject (stageSystem l Ω (point D)) (fun E ↦ (R E).rational) X

/-- The displayed comparison-conjugated representative, in Lean composition order.
Source: blueprint opening sentence, common-stage representative formula
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def representative (R : ∀ E, Realization D l Ω E (A E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
        stageTransition l Ω (point D) E L h ⋙ (R L).rational)
    (X Y : (stageSystem l Ω (point D)).PairCategory)
    (F : Index l Ω) (hX : X.stage ≤ F) (hY : Y.stage ≤ F)
    (f : X.toStage hX ⟶ Y.toStage hY) :
    (object D l Ω A R X).toStage hX ⟶ (object D l Ω A R Y).toStage hY :=
  stageRepresentative (stageSystem l Ω (point D)) (fun E ↦ (R E).rational)
    β X Y F hX hY f

/-- The actual comparisons satisfy scalar coherence and descend with the stated
object, arrow, unit, and inverse-unit formulas. The transition equation is asserted
before passing to classes, so it includes preservation by every further extension.
Source: blueprint opening sentence, identity compact support
(blueprint: lem-pod-reconstruction-common-stage-coherence). -/
def Coherence (R : ∀ E, Realization D l Ω E (A E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
        stageTransition l Ω (point D) E L h ⋙ (R L).rational) : Prop :=
  stageCoherence (stageSystem l Ω (point D)) (fun E ↦ (R E).rational)
    (fun E ↦ (R E).rationalUnit) (scalarUnit D l Ω) β

```

The specialized formulas are definitionally equal to the old bodies. All public
names and their mathematical meanings are unchanged. The data node records the
relocated declaration ownership and the three generic formulas.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | D4 | Public reexport preserves the complete interface; theorem gets a proof. |
| Sheaf.Paper.PodReconstructionCommonStageData | new, D4 | Declarations moved here to avoid an import cycle; common-stage formulas factor generically. |
| Sheaf.Paper.PodReconstructionScalarRealizations | new, D4 | Uses the fixed-family realization interface, with one named normalization hole. |

`tools/downstream.py Sheaf.Paper.PodReconstructionCommonStageCoherence` reports
zero downstream modules. DAG parents with unfinished proofs keep the original
node and theorem unchanged. Challenge.lean and every definition's meaning remain
unchanged, so no target-statement review is reopened.

## Status

landed 20261025T204504-L-2962801 2026-10-25 (merge of deliver/D4/Sheaf.Paper.PodReconstructionCommonStageCoherence)
