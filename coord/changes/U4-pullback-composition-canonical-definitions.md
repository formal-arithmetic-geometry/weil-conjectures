# PullbackCompositionTransport.RepresentativeLaws

## Reason

Profiling the original item showed repeated conversion of the large representative
equations while elaborating the structure. Name the two existing predicates and
keep them locally folded while forming RepresentativeLaws. The two unfolded predicates, including all quantifiers, stay identical.
RepresentativeLaws is now their conjunction, with proved forward/backward
projection theorems. It has the same mathematical content as the old two-field
Prop structure; there are no external consumers of its constructor or recursor. Local
reducibility annotations also prevent repeated elaborator unfolding of the
derived functors and comparisons. No mathematical data or normalization changes.

The item now also consistently names `integralComparisonSequencePullback` and
`integralComparisonDerivedSequencePullback` wherever it previously named
`PrimitiveCounit.inverse` and `PrimitiveCounit.pull`. These are the same chosen
left adjoints and derived functors: the primitive direct image differs only by
identity transports of coefficient-section types. The canonical names prevent
repeated conversion across these presentations inside every representative
formula. The theorem retains its original mathematical statement.

`strictComposition` omits its redundant complex-composition identity isomorphism.
`Functor.mapHomologicalComplexCompIso_refl_hom_app` proves that isomorphism's
hom is the identity; mapping and composing it changes no map. This makes the
strict representative agree syntactically with the localization-factor API.

The two localization factors now have explicit source and target types. This
keeps expanded instances out of their inferred public types; kernel time fell
from above the file limit to a 37-second successful compile.

## Old

```lean
def evaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PrimitiveCounit.pull l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  (Functor.mapDerivedCategoryCompIso (PrimitiveCounit.inverse l E f)
    (coefficientSequenceEvaluation l E X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (PrimitiveCounit.inverseEvaluation l E f n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E Y n)
      (integralOperationsLevelPullback l E f n)

/-- Finite adjunction-normalized derived compositor, obtained termwise by exactness.
Its ordinary map is the mate of fibre-product direct-image composition.
Source: Stacks 03D8, 0D6D
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def finiteComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E (h ≫ f) n).mapDerivedCategory ≅
      (integralOperationsLevelPullback l E f n).mapDerivedCategory ⋙
        (integralOperationsLevelPullback l E h n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  letI : (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E h n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E h n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E h n
  letI : (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E (h ≫ f) n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E (h ≫ f) n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E (h ≫ f) n
  letI : (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E f n
  Functor.mapDerivedCategoryNatIso
      (Scheme.coefficientModulePullbackComposition h f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOperationsLevelPullback l E f n)
      (integralOperationsLevelPullback l E h n)

/-- Finite evaluation and both actual quotient-transition squares for the already
constructed whole-system compositor. The last two equations are the extension-form
squares for the actual transition adjoints, with no unit-transition input assumption.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure SystemLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Z) : Prop where
  finite : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Z n).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (evaluation l E h n).hom.app ((PrimitiveCounit.pull l E f).obj C) ≫
      (integralOperationsLevelPullback l E h n).mapDerivedCategory.map
        ((evaluation l E f n).hom.app C) =
      (evaluation l E (h ≫ f) n).hom.app C ≫
        (finiteComposition l E h f n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj C)
  transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).hom.app C))
  inverse_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).inv.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).inv.app C))
  adjoint_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).hom.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).hom.app C)
  inverse_adjoint_transition :
    ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).inv.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).inv.app C)

/-- The strict complex compositor, before localization, with every quotient transition.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def strictComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (PrimitiveCounit.restrictComplex l E Z).mapIso
    ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E h f)
        (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (PrimitiveCounit.inverse l E f ⋙ PrimitiveCounit.inverse l E h))
          (.up ℤ)).app C)

/-- Restriction of derived pullback agrees with restriction of its exact complex model.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def restrictionFactor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- Iterated version of the same localization comparison, preserving the given parentheses.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def iteratedRestrictionFactor {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (coefficientSequenceDerivedRestriction l E Z).mapIso
      ((PrimitiveCounit.pull l E h).mapIso
        ((PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.app C)) ≪≫
    restrictionFactor l E h (((PrimitiveCounit.inverse l E f).mapHomologicalComplex
      (.up ℤ)).obj C)

/-- The actual product/cone map realizes L(a), and likewise its inverse, on every
strict complex presentation, including complexes representing arbitrary input systems.
The Roos functor is the existing product map on both shifted cone coordinates.
Source: Stacks 0941; node proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure RepresentativeLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop where
  forward : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((restrictionFactor l E (h ≫ f) C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).hom.app (DerivedCategory.Q.obj C)) ≫
        (iteratedRestrictionFactor l E h f C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).hom) ≫
        ρ.comparison.hom.app _
  backward : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((iteratedRestrictionFactor l E h f C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).inv.app (DerivedCategory.Q.obj C)) ≫
        (restrictionFactor l E (h ≫ f) C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).inv) ≫
        ρ.comparison.hom.app _

variable {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
  (SY : CoefficientDerivedSystemReduction l E Y)
  (SX : CoefficientDerivedSystemReduction l E X)
  (SZ : CoefficientDerivedSystemCalculus l E Z)
  (rf : integralDerivedPullback l E f ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X)
  (rh : integralDerivedPullback l E h ≅
    SX.reduction ⋙ PrimitiveCounit.pull l E h ⋙ coefficientSequenceLimit l E Z)
  (rhf : integralDerivedPullback l E (h ≫ f) ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E (h ≫ f) ⋙ coefficientSequenceLimit l E Z)

/-- Recursive comparison for P=F_(f h)(C); the input comparison is the identity.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaSource (C : coefficientSequenceDerived l E Y) :=
  PrimitiveCounit.pullBeta l E (h ≫ f) SY rhf C

/-- Recursive comparison for Q=F_h(F_f(C)), applying the inner beta before outer beta.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaTarget (C : coefficientSequenceDerived l E Y) :=
  (integralDerivedPullback l E h).map (PrimitiveCounit.pullBeta l E f SY rf C) ≫
    PrimitiveCounit.pullBeta l E h SX rh ((PrimitiveCounit.pull l E f).obj C)

/-- Coherent reduction of beta_P followed by the one whole-system counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaSource (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaSource l E h f SY rhf C) ≫
    SZ.adjunction.counit.app ((PrimitiveCounit.pull l E (h ≫ f)).obj C)

/-- Coherent reduction of beta_Q followed by that same counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaTarget (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaTarget l E h f SY SX rf rh C) ≫
    SZ.adjunction.counit.app ((PrimitiveCounit.pull l E h).obj
      ((PrimitiveCounit.pull l E f).obj C))

/-- The actual completed compositor: conjugate total limit of the canonical whole-system
compositor by the recursively defined primitive quotient-model comparisons.
Source: node displayed formula and proof steps 4--5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def completed (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] :=
  asIso (betaSource l E h f SY rhf C) ≪≫
    (coefficientSequenceLimit l E Z).mapIso ((integralComparisonSystemComposition l E h f).app C)
      ≪≫ (asIso (betaTarget l E h f SY SX rf rh C)).symm

/-- Transport equations and naturality, retaining the actual reduced system morphisms.
Source: node proof steps 4--6
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure TransportLaws (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop where
  reduction : SZ.reduction.map (completed l E h f SY SX rf rh rhf C).hom ≫
      gammaTarget l E h f SY SX SZ rf rh C =
    gammaSource l E h f SY SZ rhf C ≫ (integralComparisonSystemComposition l E h f).hom.app C
  inverse_reduction : SZ.reduction.map (completed l E h f SY SX rf rh rhf C).inv ≫
      gammaSource l E h f SY SZ rhf C =
    gammaTarget l E h f SY SX SZ rf rh C ≫ (integralComparisonSystemComposition l E h f).inv.app C
  naturality : ∀ (C' : coefficientSequenceDerived l E Y)
    (_hC' : IsNormalizedCoefficientSequence l E Y C')
    [IsIso (betaSource l E h f SY rhf C')]
    [IsIso (betaTarget l E h f SY SX rf rh C')]
    [IsIso (gammaSource l E h f SY SZ rhf C')]
    [IsIso (gammaTarget l E h f SY SX SZ rf rh C')]
    (v : C ⟶ C'),
    (integralDerivedPullback l E (h ≫ f)).map ((coefficientSequenceLimit l E Y).map v) ≫
        (completed l E h f SY SX rf rh rhf C').hom =
      (completed l E h f SY SX rf rh rhf C).hom ≫
        (integralDerivedPullback l E h).map
          ((integralDerivedPullback l E f).map ((coefficientSequenceLimit l E Y).map v))

```

## New

```lean
def evaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  Functor.mapDerivedCategorySquareIso (ordinaryEvaluation l E f n)

/-- Finite adjunction-normalized derived compositor, obtained termwise by exactness.
Its ordinary map is the mate of fibre-product direct-image composition.
Source: Stacks 03D8, 0D6D
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def finiteComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E (h ≫ f) n).mapDerivedCategory ≅
      (integralOperationsLevelPullback l E f n).mapDerivedCategory ⋙
        (integralOperationsLevelPullback l E h n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  letI : (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E h n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E h n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E h n
  letI : (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E (h ≫ f) n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E (h ≫ f) n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E (h ≫ f) n
  letI : (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E f n
  Functor.mapDerivedCategoryTriangleIso
    (Scheme.coefficientModulePullbackComposition h f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

attribute [local irreducible] evaluation finiteComposition

/-- Finite evaluation and both actual quotient-transition squares for the already
constructed whole-system compositor. The last two equations are the extension-form
squares for the actual transition adjoints, with no unit-transition input assumption.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure SystemLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Z) : Prop where
  finite : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Z n).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (evaluation l E h n).hom.app ((integralComparisonDerivedSequencePullback l E f).obj C) ≫
      (integralOperationsLevelPullback l E h n).mapDerivedCategory.map
        ((evaluation l E f n).hom.app C) =
      (evaluation l E (h ≫ f) n).hom.app C ≫
        (finiteComposition l E h f n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj C)
  transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).hom.app C))
  inverse_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).inv.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).inv.app C))
  adjoint_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).hom.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).hom.app C)
  inverse_adjoint_transition :
    ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).inv.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).inv.app C)

/-- The strict complex compositor, before localization, with every quotient transition.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def strictComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (PrimitiveCounit.restrictComplex l E Z).mapIso
    ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E h f)
      (.up ℤ)).app C)

/-- Restriction of derived pullback agrees with restriction of its exact complex model.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def restrictionFactor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (coefficientSequenceDerivedRestriction l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj ((PrimitiveCounit.restrictComplex l E X).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- Iterated version of the same localization comparison, preserving the given parentheses.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def iteratedRestrictionFactor {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (coefficientSequenceDerivedRestriction l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj C))) ≅
      DerivedCategory.Q.obj ((PrimitiveCounit.restrictComplex l E Z).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C))) :=
  (coefficientSequenceDerivedRestriction l E Z).mapIso
      ((integralComparisonDerivedSequencePullback l E h).mapIso
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app C)) ≪≫
    restrictionFactor l E h (((integralComparisonSequencePullback l E f).mapHomologicalComplex
      (.up ℤ)).obj C)

attribute [local irreducible] strictComposition restrictionFactor iteratedRestrictionFactor

/-- The actual product/cone map realizes L(a), and likewise its inverse, on every
strict complex presentation, including complexes representing arbitrary input systems.
The Roos functor is the existing product map on both shifted cone coordinates.
Source: Stacks 0941; node proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeForward {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((restrictionFactor l E (h ≫ f) C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).hom.app (DerivedCategory.Q.obj C)) ≫
        (iteratedRestrictionFactor l E h f C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).hom) ≫
        ρ.comparison.hom.app _

/-- The unchanged inverse strict-complex/Roos representative equation.
Source: Stacks 0941; parent proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeBackward {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((iteratedRestrictionFactor l E h f C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).inv.app (DerivedCategory.Q.obj C)) ≫
        (restrictionFactor l E (h ≫ f) C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).inv) ≫
        ρ.comparison.hom.app _


attribute [local irreducible] RepresentativeForward RepresentativeBackward

/-- Both actual strict-complex representative equations, with their predicate types folded.
Source: Stacks 0941; parent proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  RepresentativeForward l E h f ρ ∧ RepresentativeBackward l E h f ρ

/-- Forward projection of the two representative equations. -/
theorem RepresentativeLaws.forward {X Y Z : Scheme.{t}} {h : Z ⟶ X} {f : X ⟶ Y}
    {ρ : PrimitiveCounit.RoosRealization l E Z} (H : RepresentativeLaws l E h f ρ) :
    RepresentativeForward l E h f ρ := H.1

/-- Backward projection of the two representative equations. -/
theorem RepresentativeLaws.backward {X Y Z : Scheme.{t}} {h : Z ⟶ X} {f : X ⟶ Y}
    {ρ : PrimitiveCounit.RoosRealization l E Z} (H : RepresentativeLaws l E h f ρ) :
    RepresentativeBackward l E h f ρ := H.2

variable {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
  (SY : CoefficientDerivedSystemReduction l E Y)
  (SX : CoefficientDerivedSystemReduction l E X)
  (SZ : CoefficientDerivedSystemCalculus l E Z)
  (rf : integralDerivedPullback l E f ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X)
  (rh : integralDerivedPullback l E h ≅
    SX.reduction ⋙ PrimitiveCounit.pull l E h ⋙ coefficientSequenceLimit l E Z)
  (rhf : integralDerivedPullback l E (h ≫ f) ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E (h ≫ f) ⋙
      coefficientSequenceLimit l E Z)

/-- The primitive comparison as a natural transformation, with canonical codomain.
Source: the recursive beta formula, Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def canonicalBetaTransformation {V W : Scheme.{t}} (g : V ⟶ W)
    (S : CoefficientDerivedSystemReduction l E W)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V) :
    coefficientSequenceLimit l E W ⋙ integralDerivedPullback l E g ⟶
      integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E V :=
  Functor.whiskerLeft (coefficientSequenceLimit l E W) r.hom ≫
    Functor.whiskerRight S.adjunction.counit
      (PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V)

/-- The component of the recursive primitive comparison.
Source: the recursive beta formula, Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def canonicalBeta {V W : Scheme.{t}} (g : V ⟶ W)
    (S : CoefficientDerivedSystemReduction l E W)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V)
    (A : coefficientSequenceDerived l E W) :
    (integralDerivedPullback l E g).obj ((coefficientSequenceLimit l E W).obj A) ⟶
      (coefficientSequenceLimit l E V).obj
        ((integralComparisonDerivedSequencePullback l E g).obj A) :=
  (canonicalBetaTransformation l E g S r).app A

attribute [local irreducible] canonicalBetaTransformation canonicalBeta

/-- Recursive comparison for P=F_(f h)(C); the input comparison is the identity.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaSource (C : coefficientSequenceDerived l E Y) :=
  canonicalBeta l E (h ≫ f) SY rhf C

/-- Recursive comparison for Q=F_h(F_f(C)), applying the inner beta before outer beta.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaTarget (C : coefficientSequenceDerived l E Y) :=
  (integralDerivedPullback l E h).map (canonicalBeta l E f SY rf C) ≫
    canonicalBeta l E h SX rh ((integralComparisonDerivedSequencePullback l E f).obj C)

/-- Coherent reduction of beta_P followed by the one whole-system counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaSource (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaSource l E h f SY rhf C) ≫
    SZ.adjunction.counit.app ((integralComparisonDerivedSequencePullback l E (h ≫ f)).obj C)

/-- Coherent reduction of beta_Q followed by that same counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaTarget (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaTarget l E h f SY SX rf rh C) ≫
    SZ.adjunction.counit.app ((integralComparisonDerivedSequencePullback l E h).obj
      ((integralComparisonDerivedSequencePullback l E f).obj C))

/-- The actual completed compositor: conjugate total limit of the canonical whole-system
compositor by the recursively defined primitive quotient-model comparisons.
Source: node displayed formula and proof steps 4--5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def completed (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] :=
  asIso (betaSource l E h f SY rhf C) ≪≫
    (coefficientSequenceLimit l E Z).mapIso ((integralComparisonSystemComposition l E h f).app C)
      ≪≫ (asIso (betaTarget l E h f SY SX rf rh C)).symm

attribute [local irreducible] betaSource betaTarget gammaSource gammaTarget completed

/- Transport equations and naturality, retaining the actual reduced system morphisms.
Source: node proof steps 4--6
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
--
/-- The unchanged TransportReduction equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportReduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  SZ.reduction.map (completed l E h f SY SX rf rh rhf C).hom ≫
      gammaTarget l E h f SY SX SZ rf rh C =
    gammaSource l E h f SY SZ rhf C ≫ (integralComparisonSystemComposition l E h f).hom.app C

/-- The unchanged TransportInverseReduction equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportInverseReduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  SZ.reduction.map (completed l E h f SY SX rf rh rhf C).inv ≫
      gammaSource l E h f SY SZ rhf C =
    gammaTarget l E h f SY SX SZ rf rh C ≫ (integralComparisonSystemComposition l E h f).inv.app C

/-- The unchanged TransportNaturality equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportNaturality (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  ∀ (C' : coefficientSequenceDerived l E Y)
    (_hC' : IsNormalizedCoefficientSequence l E Y C')
    [IsIso (betaSource l E h f SY rhf C')]
    [IsIso (betaTarget l E h f SY SX rf rh C')]
    [IsIso (gammaSource l E h f SY SZ rhf C')]
    [IsIso (gammaTarget l E h f SY SX SZ rf rh C')]
    (v : C ⟶ C'),
    (integralDerivedPullback l E (h ≫ f)).map ((coefficientSequenceLimit l E Y).map v) ≫
        (completed l E h f SY SX rf rh rhf C').hom =
      (completed l E h f SY SX rf rh rhf C).hom ≫
        (integralDerivedPullback l E h).map
          ((integralDerivedPullback l E f).map ((coefficientSequenceLimit l E Y).map v))

attribute [local irreducible] TransportReduction TransportInverseReduction TransportNaturality

/-- Completed transport, inverse transport, and naturality.
Source: Stacks 0941 (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportLaws (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  TransportReduction l E h f SY SX SZ rf rh rhf C ∧
    TransportInverseReduction l E h f SY SX SZ rf rh rhf C ∧
      TransportNaturality l E h f SY SX SZ rf rh rhf C

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.reduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportReduction l E h f SY SX SZ rf rh rhf C := H.1

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.inverse_reduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportInverseReduction l E h f SY SX SZ rf rh rhf C := H.2.1

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.naturality (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportNaturality l E h f SY SX SZ rf rh rhf C := H.2.2


```

`canonicalBetaTransformation` composes the whiskered realization with the
whiskered counit; `canonicalBeta` is its component. Expanding whiskering and
composition gives precisely the original `PrimitiveCounit.pullBeta` formula,
with its codomain expressed by the definitionally equal canonical system pullback.
The realization parameters rf, rh, rhf retain their original types.

## Users

The same profiling issue occurs for TransportLaws: its three equations are now
named predicates assembled by conjunction. The original projection names are
proved theorems. No equation or quantifier changes. Both usage searches report
only the defining module and zero downstream modules.


`tools/downstream.py Sheaf.Paper.NormalizedPullbackCompositionTransport --uses
RepresentativeLaws` reports zero downstream modules and the defining module as its
only user. The two predicates unfold to the original field types.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NormalizedPullbackCompositionTransport | U4 | Prove the unchanged theorem using the folded predicates. |

No source-library declaration changes. Targets and definitions retain their
meaning; their review is reopened for this definitionally equal presentation.

## Status

landed 20261025T204936-L-3059420 2026-10-25 (merge of deliver/U4/Sheaf.Paper.NormalizedPullbackCompositionTransport)
