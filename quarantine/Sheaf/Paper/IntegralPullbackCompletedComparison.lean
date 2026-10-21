/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.IntegralOperationsWellDefined
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Integral and strict-tower completed pullback

Source: Stacks Project, proetale.tex, Tag 099N(5), with sites-cohomology.tex,
Tag 0941 (blueprint: lem-a1-integral-pullback-completed-comparison).

The coefficient transport is the existing projection-normalized ring isomorphism.
Finite comparisons below are fixed on inverse-image generators; the integral
projections are the actual mapping-cocone projections on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

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

/-- Pin the existing countable-product structure to the actual coefficient universe.
Source: Bhatt--Scholze 4.2.8
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance (priority := 2500) products (T : Scheme.{u}) :
    HasCountableProducts (integralTowerModules.{u, u} l E T) :=
  integralOperationsCountableProducts.{u, u} l E T

/-- Termwise products of integral complexes in the fixed coefficient universe.
Source: Stacks 0941 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance (priority := 2500) complexProducts (T : Scheme.{u}) :
    HasCountableProducts (CochainComplex (integralTowerModules.{u, u} l E T) ℤ) where
  out J := by
    intro hJ
    have : HasProductsOfShape J (integralTowerModules.{u, u} l E T) :=
      (products l E T).out J
    exact HomologicalComplex.instHasLimitsOfShape


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

/-- The canonical finite-level termwise shift comparison.
Source: Stacks 014E, 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def levelShift (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (integralOperationsPullbackLevel.{u, u} l E g n).obj (P⟦r⟧) ≅
      ((integralOperationsPullbackLevel.{u, u} l E g n).obj P)⟦r⟧ :=
  letI := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  letI := integralOperationsLevelPullback_additive.{u, u} l E g n
  ((unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
    SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)))
          |>.mapCochainComplexShiftIso r).app P

/-- The product of the canonical finite-level shift comparisons.
Source: Stacks 014E, 0941
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def productShift (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
      (P⟦r⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
        P).obj (op n))⟦r⟧ :=
  Pi.mapIso.{0, u + 1, u + 2}
    (C := CochainComplex (integralTowerModules.{u, u} l E X) ℤ)
    (fun n : ℕ ↦ levelShift l E g P r n) ≪≫
    (PreservesProduct.iso.{0, u + 1, u + 1, u + 2, u + 2}
      (shiftFunctor (CochainComplex (integralTowerModules.{u, u} l E X) ℤ) r)
      (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj (op n))).symm

/-- The endomorphism whose mapping cocone defines integral pullback on a representative.
Source: Stacks 0941 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev roosEnd (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj (op n))
    (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P))

/-- Shift on the actual Roos complex is (x,y) mapped to (x,(-1)^r y) in
mapping-cocone coordinates, equivalently (y,x) mapped to ((-1)^r y,x).
Source: Stacks 014E, 0941; the node's final proof step
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def ShiftCoordinates
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ),
    (∀ j : ℤ,
      (CochainComplex.mappingCocone.inl (roosEnd l E g (P⟦r⟧))).v j j (by omega) ≫
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P).f j =
        (productShift l E g P r).hom.f j ≫
          (CochainComplex.mappingCocone.inl (roosEnd l E g P)).v
            (j + r) (j + r) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso
            ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P)
            r j (j + r) rfl).inv) ∧
    (∀ (i j : ℤ) (h : i + 1 = j),
      (CochainComplex.mappingCocone.inr (roosEnd l E g (P⟦r⟧))).1.v i j h ≫
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P).f j =
        r.negOnePow • ((productShift l E g P r).hom.f i ≫
          (CochainComplex.mappingCocone.inr (roosEnd l E g P)).1.v
            (i + r) (j + r) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso
            ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P)
            r j (j + r) rfl).inv))

/-- The integral derived shift is the descent of the specified representative shift.
Source: Stacks 014E, 0941, resolving-class localization
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def ShiftDescent
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ) : Prop :=
  ∀ (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory) (r : ℤ),
    ∃ hP : integralOperationsGoodComplex.{u, u} l E Y (P.obj⟦r⟧),
      (Functor.commShiftIso (integralDerivedPullback.{u, u} l E g) (self := d) r).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
        ((integralDerivedPullbackComparison.{u, u} l E g).hom.app P)⟦r⟧' =
      (integralDerivedPullback.{u, u} l E g).map
          ((DerivedCategory.Q.commShiftIso r).inv.app P.obj) ≫
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P.obj⟦r⟧, hP⟩ ≫
        DerivedCategory.Q.map
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P.obj) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P.obj)

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

/-- Integral derived pullback agrees naturally with strict-tower completed pullback,
including the intrinsic domain, all finite derived-limit projections and every shift.
The two coefficient presentations are related by the already recorded unique
projection-normalized completed-ring isomorphism, not an extra hypothesis on K.
Source: Stacks Project, proetale.tex, Tag 099N(5), and sites-cohomology.tex, Tag 0941
(blueprint: lem-a1-integral-pullback-completed-comparison).

Proof:
1. The coefficient integer ring is a Noetherian DVR, with nonzero uniformizer and
finite residue field. Positive quotients are finite, additive torsion and perfect:
[A --t^n--> A] is their two-term free resolution. This gives the stated adic datum.
2. Exact constant-sheafification and flat constant-to-completed scalar extension
make [R --t^n--> R] a resolution of the finite constant quotient on each site.
The transitions are (t,1) and commute strictly with their quotient augmentations.
3. Apply finite-free-completed-scalar-comparison at L=E to the imported Roos
completeness predicate. It makes the actual zero-second-coordinate quotient unit
invertible. Exact countable products and normalized strict-Roos comparison carry
it to the canonical strict derived-limit unit, which is therefore invertible.
4. Koszul-reconstruction intertwines this unit with the Koszul unit. The signed
coordinate identification (x,y) mapped to (-y,x) sends the explicit intrinsic
fiber unit (u,0) to the cone unit (0,u). Thus K is intrinsically complete.
5. On one flat-term K-flat representative P, tensor the strict two-term Koszul
resolutions with P. K-flatness makes the resulting map to the quotient tower a
levelwise quasi-isomorphism. The Koszul tensor levels are K-flat with flat terms:
tensor with an acyclic complex gives a cone on an acyclic tensor complex.
6. Ringed-topos K-flat pullback preserves these properties. It identifies this
strict replacement after pullback with the corresponding target Koszul tower.
Its augmentation to the target finite reduction tower is a quasi-isomorphism.
No invertibility of the completed coefficient structure map is assumed.
7. Tensor reassociation identifies the target finite reductions with Res g_n*P_n.
The balancing map sends (x tensor b) tensor a to x tensor bar(b)a, with inverse
inserting 1. It preserves every transition and the tensor-unit generators used
in finite_normalization. Finite constant-coefficient pullback is exact.
8. The integral construction is the Roos cone C(B); the completed construction is
Rlim(VK_bullet). The strict comparison b:VK_bullet ≅ B and normalized Roos map
rho give gamma = rho followed by inverse Rlim(b). These are coefficient-linear.
9. All comparisons are natural on good representatives and descend through the
resolving-class localization by integral-operations-well-defined. This gives
naturality on every derived arrow and independence of the chosen resolution.
10. The normalized Roos map and functorial limit projections give
p_comp gamma = p_int, equivalently gamma inverse followed by p_int = p_comp.
The displayed representative projection equation is this equality after the
canonical finite computation maps; all such representatives are quantified.
11. On cone coordinates the shift map is (y,x) mapped to ((-1)^r y,x).
It commutes with the differential and has the zero and addition shift laws.
Use P[r] and a shifted K-injective tower resolution. Koszul augmentation,
balancing, zero-coordinate limit inclusion and rho commute with that signed
shift. The completed shift is the composite reduction/pullback/limit shift of
completed-pullback-triangles, so gamma has exactly the asserted shift square.
-/
theorem integralPullback_completedComparison
    (g : X ⟶ Y) (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparison l E g) := by
  sorry

end WeilConjectures.IntegralCompletedComparison
