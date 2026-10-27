# WeilConjectures.IntegralCompletedComparison comparison interface

## Reason

Move the existing interface into a definition-only module, publicly reexported from the
original module. The new comparison factors need the interface without importing the
existence theorem that assembles them. Every declaration retains its name, universe parameters, visibility, elaborated type,
public attributes and mathematical definition, except for unused automatically generated
constructor-injectivity and size-specification helper theorems. `finiteComplexComparison` now writes its previously inferred
return type explicitly; this is the same natural-transformation type and avoids repeatedly
unfolding the large coefficient functors during elaboration. Local transparency attributes
freeze the derived-category and coefficient data during interface elaboration.
The two original local additive bindings in `finiteComplexComparison` are retained.
The finite functors remain transparent where section formulas and projection types
require reduction. The `Comparison` declaration disables `genSizeOfSpec` and `genInjectivity`,
as already done for `FinitePullbackStrictTower.Comparison`. Profiling attributed
16.4 seconds to `Meta.sizeOf` and 9.2 seconds to `Comparison.mk.injEq`.
No source module refers to these helpers: `rg` for `Comparison.mk.inj`,
`Comparison.mk.injEq` and comparison size helpers in both Lean roots returned no hits.
No constructor, field, recursor or mathematical structure datum is changed.
The moved mathematical interface is otherwise unchanged.
No target changes meaning, and no consumer needs an adaptation. The signed shift
helpers already live in IntegralPullbackShiftCoordinates and stay there.

Reviewer correction (independent review of 48c083339be9): the elaborated terms are not
byte-identical. Under the new module's instance attributes the `HasDerivedCategory`
instance elaborated inside `integralComputation`, `integralProjection`,
`finiteComputation`, `finiteComplexComparison` (type) and the `projections` field of
`Comparison` (hence `Comparison.mk`/`Comparison.rec`) is now
`integralTowerHasDerivedCategory` where the published module elaborated
`integralOperationsCommHasDerivedCategory`; some quiver projections are also reached
through `ReflQuiver.toQuiver` instead of `CategoryStruct.toQuiver`. Both instances are
`HasDerivedCategory.standard _` on the same module category, so every changed type is
definitionally equal to the published one at instance transparency; the other public
declarations (`modules` … `Complete`, `Comparison` and its other fields) have identical
types. The size-specification and constructor-injectivity helpers
`Comparison.mk.sizeOf_spec`, `Comparison.mk.inj` and `Comparison.mk.injEq` are no longer
generated. All twelve direct importers of the item module compile unchanged against the
delivery (reviewer sandbox, 2026-10-25).

## Old

In `Sheaf.Paper.IntegralPullbackCompletedComparison`:

```lean
/-- The existing completed-ring transport, on modules before localization.
Source: Stacks 099N, coefficient identification
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev modules (T : Scheme.{u}) :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv

/-- The same transport on complexes.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev complexes (T : Scheme.{u}) := (modules l E T).mapHomologicalComplex (.up ℤ)

/-- The existing exact transport on derived categories.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev derived (T : Scheme.{u}) := ImmersionCompletedPullback.transport l E T

/-- Exact coefficient restriction inherits the standard termwise derived shift.
Source: Stacks 014E (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance derived_commShift (T : Scheme.{u}) : (derived l E T).CommShift ℤ :=
  inferInstanceAs ((modules l E T).mapDerivedCategory.CommShift ℤ)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Finite pullback followed by restriction, in the integral presentation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteIntegral (n : ℕ) :=
  modules l E Y ⋙ unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
      SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))

/-- Additivity of the composite finite pullback and exact coefficient restriction.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteIntegral_additive (n : ℕ) : (finiteIntegral l E g n).Additive := by
  have := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  have := integralOperationsLevelPullback_additive.{u, u} l E g n
  unfold finiteIntegral
  infer_instance

/-- The same finite pullback in the adic presentation, transported to the same ring.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteCompleted (n : ℕ) :=
  reductionChange Y (completedReductionProjection Y (pbcIntegralDatum l E) n) ⋙
    completedReductionFiniteModules g (pbcIntegralDatum l E) n ⋙
      pbcRestrict (completedReductionProjection X (pbcIntegralDatum l E) n) ⋙ modules l E X

/-- Additivity of the finite target and its coefficient transports.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteCompleted_additive (n : ℕ) : (finiteCompleted l E g n).Additive := by
  unfold finiteCompleted
  infer_instance

/-- Apply the actual finite natural comparison to complexes, with inherited zero preservation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComplexComparison (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) :=
  letI := finiteIntegral_additive l E g n
  letI := finiteCompleted_additive l E g n
  NatTrans.mapHomologicalComplex e.hom (.up ℤ)

/-- The finite comparison sends each pulled-back tensor-unit generator to itself.
This fixes the comparison on the actual finite quotient modules, rather than allowing
an arbitrary automorphism of a derived tower evaluation.
Source: Stacks 099N(5), tensor balancing
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def FiniteNormalization (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (V : Y.ProEt) (x : M.val.obj (op V)),
    ((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator.{u, u} l E g n
        ((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).obj ((modules l E Y).obj M)) V
        (unrestrictedIntegralTensorSection.{u, u} l E Y n ((modules l E Y).obj M) (op V) 1 x)) =
      completedReductionFiniteGenerator g (pbcIntegralDatum l E) n M V
        ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x

/-- The representative computation map of the specified integral pullback.
Source: Stacks 099N(5), resolving-class descent
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) :=
  (integralDerivedPullback.{u, u} l E g).map ((modules l E Y).mapDerivedCategoryFactors.hom.app P) ≫
    (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨(complexes l E Y).obj P, hP⟩

/-- The actual integral projection is the first mapping-cocone map and the nth product leg.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralProjection
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) (n : ℕ) :=
  integralComputation l E g P hP ≫ DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)).obj (op k))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)))) ≫
      Pi.π (fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
        ((complexes l E Y).obj P)).obj (op k)) n)

/-- The existing unique unit-compatible strict-tower/reflector comparison.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def towerIso := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).exists.choose

/-- The defining strict derived-limit projection, followed by its normalized finite evaluation.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def completedProjection (K : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K) (n : ℕ) :=
  (derived l E X).map
    ((towerIso l E g).inv.app ⟨K, hK⟩ ≫
      (completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
        ((completedTowerPullback g (pbcIntegralDatum l E)).obj
          ((completedReductionTower Y (pbcIntegralDatum l E)).obj K)) ≫
      (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app K)

/-- The canonical finite computation map, retaining both exact restriction comparisons.
Source: Stacks 099N(5), universal derived counits
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :=
  (derived l E X).map
    ((pbcDerivedRestrict (completedReductionProjection X (pbcIntegralDatum l E) n)).map
      (completedReductionFiniteModelMap g (pbcIntegralDatum l E) n P) ≫
      (completedReductionRestrictionFactors X
        (completedReductionProjection X (pbcIntegralDatum l E) n)).hom.app
        (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
          (.up ℤ)).obj
          (((reductionChange Y (completedReductionProjection Y
            (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P))) ≫
    (modules l E X).mapDerivedCategoryFactors.hom.app
      (((pbcRestrict (completedReductionProjection X
        (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
            (.up ℤ)).obj
              (((reductionChange Y (completedReductionProjection Y
                (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P)))

/-- The integral pullback after the existing coefficient identification.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev integral := derived l E Y ⋙ integralDerivedPullback.{u, u} l E g

/-- The completed pullback after the same coefficient identification.
The shift is the normalized shift of completedPullback-preserves-triangles.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev completed := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙ derived l E X

/-- Derived completeness is the recorded Roos predicate after canonical coefficient transport.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev Complete (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) : Prop :=
  IntegralOnSlice.IsComplete l E Y none ((derived l E Y).obj K)

/-- The clauses of the comparison, with all projections and shifts specified.
The finite isomorphisms identify the two exact finite module pullbacks on their
canonical generators. Every gamma is a morphism over the completed coefficient ring.
Source: Stacks 099N(5), 0941
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
structure Comparison where
  intrinsic : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K
  finite : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n
  finite_normalization : ∀ n : ℕ, FiniteNormalization l E g n (finite n)
  chainShift : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ
  chainShift_coordinates : ShiftCoordinates l E g chainShift
  derivedShift : (integralDerivedPullback.{u, u} l E g).CommShift ℤ
  derivedShift_descent : ShiftDescent l E g chainShift derivedShift
  gamma : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    ((integral l E g).obj K ≅ (completed l E g).obj K)
  naturality : ∀ (K L : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : Complete l E K) (hL : Complete l E L) (a : K ⟶ L),
    (integral l E g).map a ≫ (gamma L hL).hom =
      (gamma K hK).hom ≫ (completed l E g).map a
  projections : ∀
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
    (hK : Complete l E (DerivedCategory.Q.obj P)) (n : ℕ),
    (gamma (DerivedCategory.Q.obj P) hK).inv ≫ integralProjection l E g P hP n ≫
        DerivedCategory.Q.map
          ((finiteComplexComparison l E g n (finite n)).app P) =
      completedProjection l E g (DerivedCategory.Q.obj P)
          (intrinsic (DerivedCategory.Q.obj P) hK) n ≫ finiteComputation l E g P n
  shifts : (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
    ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) (r : ℤ),
      ∃ hKr : Complete l E (K⟦r⟧),
        (gamma (K⟦r⟧) hKr).hom ≫ ((completed l E g).commShiftIso r).hom.app K =
          ((integral l E g).commShiftIso r).hom.app K ≫ ((gamma K hK).hom)⟦r⟧')
    (_d := derivedShift)
```

## New

In `Sheaf.Paper.IntegralPullbackCompletedComparisonData`, publicly imported by the old module:

```lean
/-- The existing completed-ring transport, on modules before localization.
Source: Stacks 099N, coefficient identification
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev modules (T : Scheme.{u}) :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv

/-- The same transport on complexes.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev complexes (T : Scheme.{u}) := (modules l E T).mapHomologicalComplex (.up ℤ)

/-- The existing exact transport on derived categories.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev derived (T : Scheme.{u}) := ImmersionCompletedPullback.transport l E T

/-- Exact coefficient restriction inherits the standard termwise derived shift.
Source: Stacks 014E (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance derived_commShift (T : Scheme.{u}) : (derived l E T).CommShift ℤ :=
  inferInstanceAs ((modules l E T).mapDerivedCategory.CommShift ℤ)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Finite pullback followed by restriction, in the integral presentation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteIntegral (n : ℕ) :=
  modules l E Y ⋙ unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
      SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))

/-- Additivity of the composite finite pullback and exact coefficient restriction.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteIntegral_additive (n : ℕ) : (finiteIntegral l E g n).Additive := by
  have := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  have := integralOperationsLevelPullback_additive.{u, u} l E g n
  unfold finiteIntegral
  infer_instance

/-- The same finite pullback in the adic presentation, transported to the same ring.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteCompleted (n : ℕ) :=
  reductionChange Y (completedReductionProjection Y (pbcIntegralDatum l E) n) ⋙
    completedReductionFiniteModules g (pbcIntegralDatum l E) n ⋙
      pbcRestrict (completedReductionProjection X (pbcIntegralDatum l E) n) ⋙ modules l E X

/-- Additivity of the finite target and its coefficient transports.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteCompleted_additive (n : ℕ) : (finiteCompleted l E g n).Additive := by
  unfold finiteCompleted
  infer_instance

/-- Apply the actual finite natural comparison to complexes, with inherited zero preservation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComplexComparison (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) :
    (finiteIntegral l E g n).mapHomologicalComplex (.up ℤ) ⟶
      (finiteCompleted l E g n).mapHomologicalComplex (.up ℤ) :=
  letI := finiteIntegral_additive l E g n
  letI := finiteCompleted_additive l E g n
  NatTrans.mapHomologicalComplex e.hom (.up ℤ)

/-- The finite comparison sends each pulled-back tensor-unit generator to itself.
This fixes the comparison on the actual finite quotient modules, rather than allowing
an arbitrary automorphism of a derived tower evaluation.
Source: Stacks 099N(5), tensor balancing
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def FiniteNormalization (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (V : Y.ProEt) (x : M.val.obj (op V)),
    ((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator.{u, u} l E g n
        ((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).obj ((modules l E Y).obj M)) V
        (unrestrictedIntegralTensorSection.{u, u} l E Y n ((modules l E Y).obj M) (op V) 1 x)) =
      completedReductionFiniteGenerator g (pbcIntegralDatum l E) n M V
        ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x

/-- The representative computation map of the specified integral pullback.
Source: Stacks 099N(5), resolving-class descent
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) :=
  (integralDerivedPullback.{u, u} l E g).map ((modules l E Y).mapDerivedCategoryFactors.hom.app P) ≫
    (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨(complexes l E Y).obj P, hP⟩

/-- The actual integral projection is the first mapping-cocone map and the nth product leg.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralProjection
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) (n : ℕ) :=
  integralComputation l E g P hP ≫ DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)).obj (op k))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)))) ≫
      Pi.π (fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
        ((complexes l E Y).obj P)).obj (op k)) n)

/-- The existing unique unit-compatible strict-tower/reflector comparison.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def towerIso := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).exists.choose

/-- The defining strict derived-limit projection, followed by its normalized finite evaluation.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def completedProjection (K : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K) (n : ℕ) :=
  (derived l E X).map
    ((towerIso l E g).inv.app ⟨K, hK⟩ ≫
      (completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
        ((completedTowerPullback g (pbcIntegralDatum l E)).obj
          ((completedReductionTower Y (pbcIntegralDatum l E)).obj K)) ≫
      (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app K)

/-- The canonical finite computation map, retaining both exact restriction comparisons.
Source: Stacks 099N(5), universal derived counits
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :=
  (derived l E X).map
    ((pbcDerivedRestrict (completedReductionProjection X (pbcIntegralDatum l E) n)).map
      (completedReductionFiniteModelMap g (pbcIntegralDatum l E) n P) ≫
      (completedReductionRestrictionFactors X
        (completedReductionProjection X (pbcIntegralDatum l E) n)).hom.app
        (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
          (.up ℤ)).obj
          (((reductionChange Y (completedReductionProjection Y
            (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P))) ≫
    (modules l E X).mapDerivedCategoryFactors.hom.app
      (((pbcRestrict (completedReductionProjection X
        (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
            (.up ℤ)).obj
              (((reductionChange Y (completedReductionProjection Y
                (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P)))

/-- The integral pullback after the existing coefficient identification.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev integral := derived l E Y ⋙ integralDerivedPullback.{u, u} l E g

/-- The completed pullback after the same coefficient identification.
The shift is the normalized shift of completedPullback-preserves-triangles.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev completed := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙ derived l E X

/-- Derived completeness is the recorded Roos predicate after canonical coefficient transport.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev Complete (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) : Prop :=
  IntegralOnSlice.IsComplete l E Y none ((derived l E Y).obj K)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] pbcIntegralDatum finiteComputation integralProjection
  completedProjection finiteComplexComparison towerIso
  integralDerivedPullback integralOperationsPullbackComplexFunctor
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex pbcActualCompletedPull


-- Avoid unused generated size and constructor-injectivity lemmas for this large record.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The clauses of the comparison, with all projections and shifts specified.
The finite isomorphisms identify the two exact finite module pullbacks on their
canonical generators. Every gamma is a morphism over the completed coefficient ring.
Source: Stacks 099N(5), 0941
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
structure Comparison where
  intrinsic : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K
  finite : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n
  finite_normalization : ∀ n : ℕ, FiniteNormalization l E g n (finite n)
  chainShift : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ
  chainShift_coordinates : ShiftCoordinates l E g chainShift
  derivedShift : (integralDerivedPullback.{u, u} l E g).CommShift ℤ
  derivedShift_descent : ShiftDescent l E g chainShift derivedShift
  gamma : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    ((integral l E g).obj K ≅ (completed l E g).obj K)
  naturality : ∀ (K L : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : Complete l E K) (hL : Complete l E L) (a : K ⟶ L),
    (integral l E g).map a ≫ (gamma L hL).hom =
      (gamma K hK).hom ≫ (completed l E g).map a
  projections : ∀
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
    (hK : Complete l E (DerivedCategory.Q.obj P)) (n : ℕ),
    (gamma (DerivedCategory.Q.obj P) hK).inv ≫ integralProjection l E g P hP n ≫
        DerivedCategory.Q.map
          ((finiteComplexComparison l E g n (finite n)).app P) =
      completedProjection l E g (DerivedCategory.Q.obj P)
          (intrinsic (DerivedCategory.Q.obj P) hK) n ≫ finiteComputation l E g P n
  shifts : (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
    ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) (r : ℤ),
      ∃ hKr : Complete l E (K⟦r⟧),
        (gamma (K⟦r⟧) hKr).hom ≫ ((completed l E g).commShiftIso r).hom.app K =
          ((integral l E g).commShiftIso r).hom.app K ≫ ((gamma K hK).hom)⟦r⟧')
    (_d := derivedShift)

```

## Users

The table contains the union of all whole-word declaration searches made by
`tools/downstream.py Sheaf.Paper.IntegralPullbackCompletedComparison --uses` for every
moved declaration. Generic names over-approximate the actual consumers. Each preserves
its existing interpretation because the mathematical declarations are preserved; none uses the omitted
automatically generated size or constructor-injectivity helper theorems.
Claims were read when this record was written; no other group's file is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | C8 | Unchanged public interface reexported; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Unchanged public interface reexported; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | X2 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicScalarFlatReductionModel | D9 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | S7 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | S4 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.DlLocalHeartCoverDefects | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | W9 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.IntegralStratumChartRestrictions | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | T1 | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Unchanged public interface reexported; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Unchanged public interface reexported; no adaptation. |

## Status

landed 20261025T124343-L-1983617 2026-10-25 (merge of deliver/X3/Sheaf.Paper.IntegralPullbackCompletedComparison)
