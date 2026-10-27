# PbcProperIntegral ordinary input interfaces

## Reason

Extract the thirteen existing interfaces into `Sheaf.Paper.ProperIntegralOrdinaryData`
so the separate ambient strict-model comparison can use them without importing its
consumer theorem. The item publicly imports the data module and retains every old
public import. This is an interface relocation, not a mathematical definition repair.
Every signature, body, name, visibility and instance is preserved verbatim. Only the
owning blueprint labels change. A text comparison verified this exact preservation.
The target meanings and the source-library boundary are unchanged.

## Old

In `lean/Sheaf/Paper/ProperIntegralOrdinaryInputs.lean`:

```lean
/-- Coefficient, exactness, inverse-image and adjunction clauses for one edge.
The inverse-image identification sends a section to its tensor with 1.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 03D3 and 04JC
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def PbcProperIntegralEdgeInputs {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T) : Prop :=
  IsIso (completedCoefficientMap h d) ∧
  (∀ n : ℕ,
    completedCoefficientMap h d ≫ pbcAdicProjection U d n =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (pbcAdicProjection T d n) ≫
        completedFiniteCoefficientMap h d n) ∧
  (∀ (a b : ℕᵒᵖ) (v : a ⟶ b),
    completedFiniteCoefficientMap h d a.unop ≫ (pbcAdicRings U d).map v =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        ((pbcAdicRings T d).map v) ≫ completedFiniteCoefficientMap h d b.unop) ∧
  PreservesFiniteLimits (completedModulePullback h d) ∧
  PreservesFiniteColimits (completedModulePullback h d) ∧
  Nonempty (completedModulePullback h d ⊣ completedModuleDirectImage h d) ∧
  ∃! e : proEtaleModuleInverseImage h (pbcAdicCompletion T d) ≅
      completedModulePullback h d ⋙ pbcRestrict (completedCoefficientMap h d),
    ∀ (M : pbcModules T (pbcAdicCompletion T d)) (V : U.ProEtᵒᵖ)
      (x : ((proEtaleModuleInverseImage h (pbcAdicCompletion T d)).obj M).val.obj V),
      (e.hom.app M).val.app V x =
        reductionTensorSection U (completedCoefficientMap h d)
          ((proEtaleModuleInverseImage h (pbcAdicCompletion T d)).obj M) V 1 x

/-- Agreement with both published stratified-perfect presentations, including effectivity
of coefficient transport. The transport is fixed by every finite quotient projection.
Source: Bhatt--Scholze, Proposition 6.6.11 and Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def PbcProperIntegralMembershipAgreement (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) : Prop :=
  (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
    IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K) ∧
  (∃ L : DerivedCategory (integralTowerModules l E T),
    Nonempty ((integralDetailedTransport T l E).obj L ≅ K)) ∧
  ∀ (L : DerivedCategory (integralTowerModules l E T))
    (_e : (integralDetailedTransport T l E).obj L ≅ K),
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      sfIntegralConstructible l E T L

/-- The canonical localization factorization for the published coefficient transport.
Its exactness instances are supplied by the recorded scalar-restriction theorem.
Source: Bhatt--Scholze, Definition 6.5.1; Stacks 06YY
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def pbcIntegralDetailedTransportFactors (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  letI := (integralDetailedCoefficientRestriction_exact T l E).1
  letI := (integralDetailedCoefficientRestriction_exact T l E).2
  (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).mapDerivedCategoryFactors

/-- The normalized ordinary tensor/pullback identification between the two published
coefficient presentations. Module components preserve the actual adjunction-unit sections;
derived components preserve the universal counits on every flat-term K-flat complex.
These conditions fix the identification, rather than merely comparing its endpoints.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03D3 and 06YY
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
structure PbcProperIntegralPullbackIdentification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) where
  /-- Tensor/pullback comparison with the quotient-normalized scalar restrictions. -/
  moduleIso : ordinaryIntegralModulePull l E h ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison U l E).hom ≅
    SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom ⋙
      completedModulePullback h (pbcIntegralDatum l E)
  /-- The comparison takes the actual tensor-unit generator to the actual generator. -/
  module_unit : ∀ (M : integralTowerModules l E T) (V : T.ProEt)
      (x : M.val.obj (op V)),
    (moduleIso.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
      (((ordinaryIntegralModuleAdjunction l E h).unit.app M).val.app (op V) x) =
    ((pbcActualModuleAdjunction h (pbcIntegralDatum l E)).unit.app
      ((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom).obj M)).val.app (op V) x
  /-- Ordinary derived pullback, before any completion. -/
  derivedIso : ordinaryIntegralDerivedPull l E h ⋙ integralDetailedTransport U l E ≅
    integralDetailedTransport T l E ⋙ completedOrdinaryPullback h (pbcIntegralDatum l E)
  /-- The derived identification is induced by moduleIso, with its actual counits. -/
  derived_counit : ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (completedOrdinaryPullback h (pbcIntegralDatum l E)).map
        ((pbcIntegralDetailedTransportFactors T l E).hom.app
            P.obj) ≫
      completedOrdinaryPullbackComplexCounit h (pbcIntegralDatum l E)
        (((SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison T l E).hom).mapHomologicalComplex (.up ℤ)).obj
            P.obj) =
    (integralDetailedTransport U l E).map (ordinaryIntegralPullComplexCounit l E h P.obj) ≫
      (pbcIntegralDetailedTransportFactors U l E).hom.app
          ((ordinaryIntegralPullComplex l E h).obj P.obj) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex moduleIso.hom (.up ℤ)).app P.obj)

/-- The existing scalar restriction on modules, with its quotient-normalized ring map.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
abbrev pbcIntegralTransportModules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  SheafOfModules.restrictScalars.{u + 1} (integralDetailedCoefficientComparison T l E).hom

/-- Termwise restriction along the same coefficient comparison.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
abbrev pbcIntegralTransportComplex (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (pbcIntegralTransportModules T l E).mapHomologicalComplex (.up ℤ)

/-- The actual pulled-back strict reduction tower of a transported representative.
Source: Stacks 099N(5); the node's proof step 6
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def pbcIntegralActualTower (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  ((completedTowerModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj
    ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
      ((pbcIntegralTransportComplex T l E).obj P))

/-- The actual computation map from derived pulled-back reductions to that strict tower.
It uses only the coefficient-localization factor and the two universal derived counits.
Source: Stacks 06YY and 099N(5); the node's proof step 6
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def pbcIntegralActualTowerCounit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (completedTowerPullback h (pbcIntegralDatum l E)).obj
        ((completedReductionTower T (pbcIntegralDatum l E)).obj
          ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P))) ⟶
      DerivedCategory.Q.obj (pbcIntegralActualTower l E h P) :=
  (completedTowerPullback h (pbcIntegralDatum l E)).map
    ((completedReductionTower T (pbcIntegralDatum l E)).map
        ((pbcIntegralDetailedTransportFactors T l E).hom.app P) ≫
      completedReductionTowerComplexCounit T (pbcIntegralDatum l E)
        ((pbcIntegralTransportComplex T l E).obj P)) ≫
    completedTowerPullbackComplexCounit h (pbcIntegralDatum l E)
      ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
        ((pbcIntegralTransportComplex T l E).obj P))

attribute [local irreducible] pbcIntegralActualTowerCounit

/-- Actual quotient augmentation after ordinary ambient module pullback.
Source: Stacks 099N(5); the node's proof step 6
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def pbcIntegralActualTowerAugmentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :=
  letI := completedReductionModuleTowerFunctor_additive T (pbcIntegralDatum l E)
  ((completedModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).map
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit (pbcIntegralDatum l E) T)
        (.up ℤ)).app ((pbcIntegralTransportComplex T l E).obj P))).app (op n))

attribute [local irreducible] pbcIntegralActualTowerAugmentation

/-- Countable products in the actual completed coefficient module category.
Source: Bhatt--Scholze, Proposition 4.2.8
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
instance pbcIntegralActualProducts (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    HasCountableProducts (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  (ProEt.countableProducts_exact.{u, u, 0} T
    (pbcAdicCompletion T (pbcIntegralDatum l E))).1

/-- Both cone coordinates of coefficient transport, with the given strict tower map.
Source: Stacks 0941; the node's proof step 7
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def PbcIntegralRoosTransportCoordinates (U : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : ℕᵒᵖ ⥤ CochainComplex
      (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E U) ℤ)
    (t : C ≅ D ⋙ pbcIntegralTransportComplex U l E)
    (z : (pbcIntegralTransportComplex U l E).obj (integralOperationsRoos D) ≅
      integralOperationsRoos C) : Prop :=
  (∀ (n : ℕ) (i : ℤ),
        z.hom.f i ≫ (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
              (integralOperationsTowerStep C))).f i ≫
          (Pi.π (fun m : ℕ ↦
            C.obj (op m)) n).f i =
        ((pbcIntegralTransportModules U l E).map
          ((CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
              (integralOperationsTowerStep D))).f i ≫
            (Pi.π (fun m : ℕ ↦
              D.obj (op m)) n).f i)) ≫
          (t.inv.app (op n)).f i) ∧
  (∀ (n : ℕ) (i j : ℤ) (hij : i + -1 = j),
        z.hom.f i ≫ (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
              (integralOperationsTowerStep C))).v i j hij ≫
          (Pi.π (fun m : ℕ ↦
            C.obj (op m)) n).f j =
        ((pbcIntegralTransportModules U l E).map
          ((CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
              (integralOperationsTowerStep D))).v i j hij ≫
            (Pi.π (fun m : ℕ ↦
              D.obj (op m)) n).f j)) ≫
          (t.inv.app (op n)).f j)

attribute [local irreducible] PbcIntegralRoosTransportCoordinates

/-- The independently pinned model comparison. The strict tower isomorphism preserves
quotient-unit generators; both coordinates pin transport of the Roos cone. On every
good representative and every entire-tower K-injective resolution, b is the composite
Cone(r') followed by the inverse (0,iota) inclusion and the universal Rlim computation.
Neither eta nor gamma occurs in these conditions.
Source: Stacks 0941, 099N(5); the node's proof steps 6--7
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def PbcProperIntegralModelMatching (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
        completedTowerPullback h (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) U) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    IsIso (pbcIntegralActualTowerCounit l E h P.obj) ∧
    ∃ (t : (pbcIntegralActualTower l E h P.obj).asFunctor ≅
        (integralOperationsPullbackTowerFunctor l E h).obj P.obj ⋙
          pbcIntegralTransportComplex U l E)
      (z : (pbcIntegralTransportComplex U l E).obj
          ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) ≅
        integralOperationsRoos ((pbcIntegralActualTower l E h P.obj).asFunctor)),
      (∀ n : ℕ,
        (NatTrans.mapHomologicalComplex a.moduleIso.hom (.up ℤ)).app P.obj ≫
            pbcIntegralActualTowerAugmentation l E h P.obj n ≫ t.hom.app (op n) =
          (pbcIntegralTransportComplex U l E).map
            (((ordinaryIntegralQuotientAugmentation l E h).app P.obj).app (op n))) ∧
      PbcIntegralRoosTransportCoordinates U l E
        (pbcIntegralActualTower l E h P.obj).asFunctor
        ((integralOperationsPullbackTowerFunctor l E h).obj P.obj) t z ∧
      ∀ (I : CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
        (r : pbcIntegralActualTower l E h P.obj ⟶ I) [QuasiIso r] [I.IsKInjective]
        (_hi : ∀ i : ℤ, Injective (I.X i)),
        ∃ ι : ((lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
              pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))).mapHomologicalComplex
                (.up ℤ)).obj I ⟶ integralOperationsRoos I.asFunctor,
          (∀ (n : ℕ) (i : ℤ),
            ι.f i ≫ (CochainComplex.mappingCocone.fst
                (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).f i ≫
              (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i) ∧
          (∀ (i j : ℤ) (hij : i + -1 = j),
            ι.f i ≫ (CochainComplex.mappingCocone.snd
              (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).v
                i j hij = 0) ∧
          b.hom.app (DerivedCategory.Q.obj P.obj) ≫
              (completedTowerRlim (pbcIntegralDatum l E) U).map
                (pbcIntegralActualTowerCounit l E h P.obj ≫ DerivedCategory.Q.map r) ≫
              (Functor.rightDerivedFunctorObjQIso
                (lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
                  pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) I).hom ≫
              DerivedCategory.Q.map ι =
            (integralDetailedTransport U l E).map
                ((integralDerivedPullbackComparison l E h).hom.app P) ≫
              (pbcIntegralDetailedTransportFactors U l E).hom.app
                ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) ≫
              DerivedCategory.Q.map z.hom ≫
              DerivedCategory.Q.map (integralOperationsRoosFunctor.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r))

attribute [local irreducible] PbcProperIntegralModelMatching

/-- Match eta with gamma using a model comparison pinned independently by whole strict
towers, the zero-coordinate limit inclusion, and Cone(r') on good representatives.
The equation is tested on every coefficient presentation and every isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4) and Remark 6.8.15
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs). -/
def PbcProperIntegralCompletionMatching (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) : Prop :=
  ∃ (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
        completedTowerPullback h (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) U),
    PbcProperIntegralModelMatching l E h a b ∧
    ∀ (L : DerivedCategory (integralTowerModules l E T))
      (e : (integralDetailedTransport T l E).obj L ≅ K),
      (integralDetailedTransport U l E).map
          ((ordinaryIntegralCompletionComparison l E h).app L) ≫ b.hom.app L ≫
          (completedTowerRlim (pbcIntegralDatum l E) U).map
            ((completedTowerPullback h (pbcIntegralDatum l E)).map
              ((completedReductionTower T (pbcIntegralDatum l E)).map e.hom)) =
        a.derivedIso.hom.app L ≫
          (completedOrdinaryPullback h (pbcIntegralDatum l E)).map e.hom ≫
            completedPullbackComparison h (pbcIntegralDatum l E) K

attribute [local irreducible] PbcProperIntegralCompletionMatching
```

## New

In `lean/Sheaf/Paper/ProperIntegralOrdinaryData.lean`, publicly re-exported by the old module:

```lean
/-- Coefficient, exactness, inverse-image and adjunction clauses for one edge.
The inverse-image identification sends a section to its tensor with 1.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 03D3 and 04JC
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def PbcProperIntegralEdgeInputs {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T) : Prop :=
  IsIso (completedCoefficientMap h d) ∧
  (∀ n : ℕ,
    completedCoefficientMap h d ≫ pbcAdicProjection U d n =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (pbcAdicProjection T d n) ≫
        completedFiniteCoefficientMap h d n) ∧
  (∀ (a b : ℕᵒᵖ) (v : a ⟶ b),
    completedFiniteCoefficientMap h d a.unop ≫ (pbcAdicRings U d).map v =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        ((pbcAdicRings T d).map v) ≫ completedFiniteCoefficientMap h d b.unop) ∧
  PreservesFiniteLimits (completedModulePullback h d) ∧
  PreservesFiniteColimits (completedModulePullback h d) ∧
  Nonempty (completedModulePullback h d ⊣ completedModuleDirectImage h d) ∧
  ∃! e : proEtaleModuleInverseImage h (pbcAdicCompletion T d) ≅
      completedModulePullback h d ⋙ pbcRestrict (completedCoefficientMap h d),
    ∀ (M : pbcModules T (pbcAdicCompletion T d)) (V : U.ProEtᵒᵖ)
      (x : ((proEtaleModuleInverseImage h (pbcAdicCompletion T d)).obj M).val.obj V),
      (e.hom.app M).val.app V x =
        reductionTensorSection U (completedCoefficientMap h d)
          ((proEtaleModuleInverseImage h (pbcAdicCompletion T d)).obj M) V 1 x

/-- Agreement with both published stratified-perfect presentations, including effectivity
of coefficient transport. The transport is fixed by every finite quotient projection.
Source: Bhatt--Scholze, Proposition 6.6.11 and Proposition 6.8.11(3)
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def PbcProperIntegralMembershipAgreement (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) : Prop :=
  (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
    IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K) ∧
  (∃ L : DerivedCategory (integralTowerModules l E T),
    Nonempty ((integralDetailedTransport T l E).obj L ≅ K)) ∧
  ∀ (L : DerivedCategory (integralTowerModules l E T))
    (_e : (integralDetailedTransport T l E).obj L ≅ K),
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      sfIntegralConstructible l E T L

/-- The canonical localization factorization for the published coefficient transport.
Its exactness instances are supplied by the recorded scalar-restriction theorem.
Source: Bhatt--Scholze, Definition 6.5.1; Stacks 06YY
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def pbcIntegralDetailedTransportFactors (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  letI := (integralDetailedCoefficientRestriction_exact T l E).1
  letI := (integralDetailedCoefficientRestriction_exact T l E).2
  (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).mapDerivedCategoryFactors

/-- The normalized ordinary tensor/pullback identification between the two published
coefficient presentations. Module components preserve the actual adjunction-unit sections;
derived components preserve the universal counits on every flat-term K-flat complex.
These conditions fix the identification, rather than merely comparing its endpoints.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03D3 and 06YY
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
structure PbcProperIntegralPullbackIdentification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) where
  /-- Tensor/pullback comparison with the quotient-normalized scalar restrictions. -/
  moduleIso : ordinaryIntegralModulePull l E h ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison U l E).hom ≅
    SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom ⋙
      completedModulePullback h (pbcIntegralDatum l E)
  /-- The comparison takes the actual tensor-unit generator to the actual generator. -/
  module_unit : ∀ (M : integralTowerModules l E T) (V : T.ProEt)
      (x : M.val.obj (op V)),
    (moduleIso.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
      (((ordinaryIntegralModuleAdjunction l E h).unit.app M).val.app (op V) x) =
    ((pbcActualModuleAdjunction h (pbcIntegralDatum l E)).unit.app
      ((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom).obj M)).val.app (op V) x
  /-- Ordinary derived pullback, before any completion. -/
  derivedIso : ordinaryIntegralDerivedPull l E h ⋙ integralDetailedTransport U l E ≅
    integralDetailedTransport T l E ⋙ completedOrdinaryPullback h (pbcIntegralDatum l E)
  /-- The derived identification is induced by moduleIso, with its actual counits. -/
  derived_counit : ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (completedOrdinaryPullback h (pbcIntegralDatum l E)).map
        ((pbcIntegralDetailedTransportFactors T l E).hom.app
            P.obj) ≫
      completedOrdinaryPullbackComplexCounit h (pbcIntegralDatum l E)
        (((SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison T l E).hom).mapHomologicalComplex (.up ℤ)).obj
            P.obj) =
    (integralDetailedTransport U l E).map (ordinaryIntegralPullComplexCounit l E h P.obj) ≫
      (pbcIntegralDetailedTransportFactors U l E).hom.app
          ((ordinaryIntegralPullComplex l E h).obj P.obj) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex moduleIso.hom (.up ℤ)).app P.obj)

/-- The existing scalar restriction on modules, with its quotient-normalized ring map.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
abbrev pbcIntegralTransportModules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  SheafOfModules.restrictScalars.{u + 1} (integralDetailedCoefficientComparison T l E).hom

/-- Termwise restriction along the same coefficient comparison.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
abbrev pbcIntegralTransportComplex (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (pbcIntegralTransportModules T l E).mapHomologicalComplex (.up ℤ)

/-- The actual pulled-back strict reduction tower of a transported representative.
Source: Stacks 099N(5); the node's proof step 6
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def pbcIntegralActualTower (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  ((completedTowerModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj
    ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
      ((pbcIntegralTransportComplex T l E).obj P))

/-- The actual computation map from derived pulled-back reductions to that strict tower.
It uses only the coefficient-localization factor and the two universal derived counits.
Source: Stacks 06YY and 099N(5); the node's proof step 6
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def pbcIntegralActualTowerCounit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (completedTowerPullback h (pbcIntegralDatum l E)).obj
        ((completedReductionTower T (pbcIntegralDatum l E)).obj
          ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P))) ⟶
      DerivedCategory.Q.obj (pbcIntegralActualTower l E h P) :=
  (completedTowerPullback h (pbcIntegralDatum l E)).map
    ((completedReductionTower T (pbcIntegralDatum l E)).map
        ((pbcIntegralDetailedTransportFactors T l E).hom.app P) ≫
      completedReductionTowerComplexCounit T (pbcIntegralDatum l E)
        ((pbcIntegralTransportComplex T l E).obj P)) ≫
    completedTowerPullbackComplexCounit h (pbcIntegralDatum l E)
      ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
        ((pbcIntegralTransportComplex T l E).obj P))

attribute [local irreducible] pbcIntegralActualTowerCounit

/-- Actual quotient augmentation after ordinary ambient module pullback.
Source: Stacks 099N(5); the node's proof step 6
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def pbcIntegralActualTowerAugmentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :=
  letI := completedReductionModuleTowerFunctor_additive T (pbcIntegralDatum l E)
  ((completedModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).map
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit (pbcIntegralDatum l E) T)
        (.up ℤ)).app ((pbcIntegralTransportComplex T l E).obj P))).app (op n))

attribute [local irreducible] pbcIntegralActualTowerAugmentation

/-- Countable products in the actual completed coefficient module category.
Source: Bhatt--Scholze, Proposition 4.2.8
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
instance pbcIntegralActualProducts (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    HasCountableProducts (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  (ProEt.countableProducts_exact.{u, u, 0} T
    (pbcAdicCompletion T (pbcIntegralDatum l E))).1

/-- Both cone coordinates of coefficient transport, with the given strict tower map.
Source: Stacks 0941; the node's proof step 7
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def PbcIntegralRoosTransportCoordinates (U : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : ℕᵒᵖ ⥤ CochainComplex
      (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E U) ℤ)
    (t : C ≅ D ⋙ pbcIntegralTransportComplex U l E)
    (z : (pbcIntegralTransportComplex U l E).obj (integralOperationsRoos D) ≅
      integralOperationsRoos C) : Prop :=
  (∀ (n : ℕ) (i : ℤ),
        z.hom.f i ≫ (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
              (integralOperationsTowerStep C))).f i ≫
          (Pi.π (fun m : ℕ ↦
            C.obj (op m)) n).f i =
        ((pbcIntegralTransportModules U l E).map
          ((CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
              (integralOperationsTowerStep D))).f i ≫
            (Pi.π (fun m : ℕ ↦
              D.obj (op m)) n).f i)) ≫
          (t.inv.app (op n)).f i) ∧
  (∀ (n : ℕ) (i j : ℤ) (hij : i + -1 = j),
        z.hom.f i ≫ (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
              (integralOperationsTowerStep C))).v i j hij ≫
          (Pi.π (fun m : ℕ ↦
            C.obj (op m)) n).f j =
        ((pbcIntegralTransportModules U l E).map
          ((CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
              (integralOperationsTowerStep D))).v i j hij ≫
            (Pi.π (fun m : ℕ ↦
              D.obj (op m)) n).f j)) ≫
          (t.inv.app (op n)).f j)

attribute [local irreducible] PbcIntegralRoosTransportCoordinates

/-- The independently pinned model comparison. The strict tower isomorphism preserves
quotient-unit generators; both coordinates pin transport of the Roos cone. On every
good representative and every entire-tower K-injective resolution, b is the composite
Cone(r') followed by the inverse (0,iota) inclusion and the universal Rlim computation.
Neither eta nor gamma occurs in these conditions.
Source: Stacks 0941, 099N(5); the node's proof steps 6--7
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def PbcProperIntegralModelMatching (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
        completedTowerPullback h (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) U) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    IsIso (pbcIntegralActualTowerCounit l E h P.obj) ∧
    ∃ (t : (pbcIntegralActualTower l E h P.obj).asFunctor ≅
        (integralOperationsPullbackTowerFunctor l E h).obj P.obj ⋙
          pbcIntegralTransportComplex U l E)
      (z : (pbcIntegralTransportComplex U l E).obj
          ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) ≅
        integralOperationsRoos ((pbcIntegralActualTower l E h P.obj).asFunctor)),
      (∀ n : ℕ,
        (NatTrans.mapHomologicalComplex a.moduleIso.hom (.up ℤ)).app P.obj ≫
            pbcIntegralActualTowerAugmentation l E h P.obj n ≫ t.hom.app (op n) =
          (pbcIntegralTransportComplex U l E).map
            (((ordinaryIntegralQuotientAugmentation l E h).app P.obj).app (op n))) ∧
      PbcIntegralRoosTransportCoordinates U l E
        (pbcIntegralActualTower l E h P.obj).asFunctor
        ((integralOperationsPullbackTowerFunctor l E h).obj P.obj) t z ∧
      ∀ (I : CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
        (r : pbcIntegralActualTower l E h P.obj ⟶ I) [QuasiIso r] [I.IsKInjective]
        (_hi : ∀ i : ℤ, Injective (I.X i)),
        ∃ ι : ((lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
              pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))).mapHomologicalComplex
                (.up ℤ)).obj I ⟶ integralOperationsRoos I.asFunctor,
          (∀ (n : ℕ) (i : ℤ),
            ι.f i ≫ (CochainComplex.mappingCocone.fst
                (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).f i ≫
              (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i) ∧
          (∀ (i j : ℤ) (hij : i + -1 = j),
            ι.f i ≫ (CochainComplex.mappingCocone.snd
              (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).v
                i j hij = 0) ∧
          b.hom.app (DerivedCategory.Q.obj P.obj) ≫
              (completedTowerRlim (pbcIntegralDatum l E) U).map
                (pbcIntegralActualTowerCounit l E h P.obj ≫ DerivedCategory.Q.map r) ≫
              (Functor.rightDerivedFunctorObjQIso
                (lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
                  pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) I).hom ≫
              DerivedCategory.Q.map ι =
            (integralDetailedTransport U l E).map
                ((integralDerivedPullbackComparison l E h).hom.app P) ≫
              (pbcIntegralDetailedTransportFactors U l E).hom.app
                ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) ≫
              DerivedCategory.Q.map z.hom ≫
              DerivedCategory.Q.map (integralOperationsRoosFunctor.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r))

attribute [local irreducible] PbcProperIntegralModelMatching

/-- Match eta with gamma using a model comparison pinned independently by whole strict
towers, the zero-coordinate limit inclusion, and Cone(r') on good representatives.
The equation is tested on every coefficient presentation and every isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4) and Remark 6.8.15
(blueprint: def-weil-pbc-proper-integral-ordinary-data). -/
def PbcProperIntegralCompletionMatching (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) : Prop :=
  ∃ (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
        completedTowerPullback h (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) U),
    PbcProperIntegralModelMatching l E h a b ∧
    ∀ (L : DerivedCategory (integralTowerModules l E T))
      (e : (integralDetailedTransport T l E).obj L ≅ K),
      (integralDetailedTransport U l E).map
          ((ordinaryIntegralCompletionComparison l E h).app L) ≫ b.hom.app L ≫
          (completedTowerRlim (pbcIntegralDatum l E) U).map
            ((completedTowerPullback h (pbcIntegralDatum l E)).map
              ((completedReductionTower T (pbcIntegralDatum l E)).map e.hom)) =
        a.derivedIso.hom.app L ≫
          (completedOrdinaryPullback h (pbcIntegralDatum l E)).map e.hom ≫
            completedPullbackComparison h (pbcIntegralDatum l E) K

attribute [local irreducible] PbcProperIntegralCompletionMatching
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperIntegralOrdinaryInputs | Q5 | Same interfaces through a public import; theorem signature unchanged. |
| Sheaf.Paper.ProperIntegralStrictModelComparison | Q5, new | Uses the normalized interfaces for the separate ambient comparison. |

`tools/downstream.py Sheaf.Paper.ProperIntegralOrdinaryInputs --uses
PbcProperIntegralCompletionMatching` reported zero downstream modules and only the
item itself as a textual user. A repository search found the interface names only
in the original item. Its DAG parent
`lem-weil-pbc-realization-completed-mate` continues to cite the original theorem.
No consumer theorem, target, unit route, or adopted source declaration changes.
The original node now attaches only its theorem; the new data node attaches the
thirteen moved interfaces. No forced adaptation is needed.

## Status

landed 20261024T015835-L-2458186 2026-10-24 (merge of deliver/Q5/Sheaf.Paper.ProperIntegralOrdinaryInputs)
