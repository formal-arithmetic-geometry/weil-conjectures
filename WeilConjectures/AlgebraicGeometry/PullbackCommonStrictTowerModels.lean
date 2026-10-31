/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.FdCoefficientComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap

/-! # Common strict towers for the two completed pullbacks

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Stacks 099N(2),(5) and 0941
(blueprint: lem-fd-pullback-common-strict-tower-models).

The helper definitions retain the actual reduction tower, derived counits and
coefficient identity. `FdCommonStrictTowerModels` packages its strict comparisons,
both cone coordinates and the resolution-normalized natural comparison.
`fdPullbackCommonStrictTowerModels` states existence under the node's hypotheses.
-/

@[expose] public noncomputable section
set_option genCtorIdx false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual PBC strict quotient tower on the fixed coefficient presentation.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonStrictTower {U T : Scheme.{u}} (h : U ⟶ T) :
    CochainComplex (integralTowerModules l E T) ℤ ⥤
      CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ :=
  (fdCoefficientTransport l E T).mapHomologicalComplex (.up ℤ) ⋙
    completedReductionComplexTowerFunctor T (pbcIntegralDatum l E) ⋙
      (completedTowerModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)

/-- The actual derived strict tower before total inverse limit.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonDerivedTower {U T : Scheme.{u}} (h : U ⟶ T) :
    DerivedCategory (integralTowerModules l E T) ⥤
      DerivedCategory (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) :=
  integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
    completedTowerPullback h (pbcIntegralDatum l E)

/-- The canonical resolution comparison, with both defining left-derived counits retained.
Source: Stacks 099N(5), common-tower proof step 3
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonTowerCounit {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (fdCommonDerivedTower l E h).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((fdCommonStrictTower l E h).obj P) :=
  (completedTowerPullback h (pbcIntegralDatum l E)).map
    ((completedReductionTower T (pbcIntegralDatum l E)).map
      ((fdCoefficientTransportFactors l E T).hom.app P)) ≫
  (completedTowerPullback h (pbcIntegralDatum l E)).map
    (completedReductionTowerComplexCounit T (pbcIntegralDatum l E)
      (((fdCoefficientTransport l E T).mapHomologicalComplex (.up ℤ)).obj P)) ≫
  Functor.leftDerivedCounitOnComplex
    (completedTowerModulePullback h (pbcIntegralDatum l E))
    (completedTowerPullback h (pbcIntegralDatum l E))
    (completedTowerPullbackCounit h (pbcIntegralDatum l E))
    ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
      (((fdCoefficientTransport l E T).mapHomologicalComplex (.up ℤ)).obj P))

/-- Termwise-limit presentation of the actual right-derived inverse-limit unit.
Source: Stacks 0941, proof; the canonical limit cone of a diagram of complexes
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonRlimUnit (U : Scheme.{u})
    (X : CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ) :
    DerivedCategory.Q.obj (limit X.asFunctor) ⟶
      (completedTowerRlim (pbcIntegralDatum l E) U).obj (DerivedCategory.Q.obj X) :=
  DerivedCategory.Q.map
    (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩).hom ≫
  (DerivedCategory.quotientCompQhIso _).inv.app
    (((lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
      pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))).mapHomologicalComplex
        (.up ℤ) |>.obj X) ≫
  DerivedCategory.Qh.map
    ((((lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
      pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app X) ≫
  (lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
    pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj X) ≫
  (completedTowerRlim (pbcIntegralDatum l E) U).map
    ((DerivedCategory.quotientCompQhIso _).hom.app X)


/-- The fixed endomorphism of the framework strict quotient tower.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkEnd {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (∏ᶜ (fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))) ⟶
      (∏ᶜ (fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))
    (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E h).obj P))

/-- The fixed unshifted quotient projection of the framework cone.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkProjection {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (n : ℕ) :
    ((integralOperationsPullbackComplexFunctor l E h).obj P).X i ⟶
      (((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)).X i :=
  (CochainComplex.mappingCocone.fst (fdCommonFrameworkEnd l E h P)).f i ≫
    (Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op k)) n).f i

/-- The shifted quotient projection of the framework cone.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkShiftedProjection {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (p : ℤ) (n : ℕ) :
    ((integralOperationsPullbackComplexFunctor l E h).obj P).X (p + 1) ⟶
      (((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)).X p :=
  (CochainComplex.mappingCocone.snd (fdCommonFrameworkEnd l E h P)).v
    (p + 1) p (by omega) ≫
      (Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op k)) n).f p

/-- The canonical unit generator in the actual strict quotient tower.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonStrictGenerator {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (n : ℕ) (V : T.ProEt)
    (x : ((fdCoefficientTransport l E T).obj (P.X i)).val.obj (op V)) :
    (((fdCommonStrictTower l E h).obj P).X i).obj (op n) |>.val.obj
      (op ((proEtaleBaseChange h).obj V)) :=
  pbcActualModuleUnitSection h (pbcIntegralDatum l E)
    ((completedReductionLevel T (pbcIntegralDatum l E) n).obj
      ((fdCoefficientTransport l E T).obj (P.X i))) V
    (reductionTensorSection T (completedReductionProjection T (pbcIntegralDatum l E) n)
      ((fdCoefficientTransport l E T).obj (P.X i)) (op V) 1 x)

/-- The fixed exact coefficient transport on the framework computation complex.
Source: the quotient-normalized coefficient identity in the trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkCoefficientComparison {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    (integralDetailedTransport U l E).obj
      ((integralOperationsPullbackOnGood l E h).obj P) ⟶
    DerivedCategory.Q.obj (((fdCoefficientTransport l E U).mapHomologicalComplex (.up ℤ)).obj
      ((integralOperationsPullbackComplexFunctor l E h).obj P.obj)) :=
  (fdCoefficientTransportFactors l E U).hom.app
    ((integralOperationsPullbackComplexFunctor l E h).obj P.obj)

/-- Expanded endpoint presentation of the canonical tower resolution comparison.
Source: Stacks 099N(5), common-tower proof step 3
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonExpandedTowerCounit {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (completedReductionTower T (pbcIntegralDatum l E) ⋙
      completedTowerPullback h (pbcIntegralDatum l E)).obj
        ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((fdCommonStrictTower l E h).obj P) :=
  fdCommonTowerCounit l E h P

attribute [local irreducible] fdCommonStrictTower fdCommonDerivedTower
  fdCommonFrameworkEnd fdCommonFrameworkProjection fdCommonFrameworkShiftedProjection
  fdCommonStrictGenerator integralDetailedTransport
  integralDerivedPullback integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor fdCoefficientTransport

/-- The common strict-tower model, its two realizations, and their normalized descent.
The tower isomorphism is a natural isomorphism of entire strict diagrams. Its generator
formula fixes the quotient maps. The two cone projection equations fix the cone map,
including its shifted coordinate. The resolution formula holds for every resolution;
`ambient` is natural on the full ambient derived category and `integral` is its full
constructible restriction. No quotient-level K-flatness is assumed.
Source: trace-definition final sentence; Stacks 099N(2),(5) and 0941, proof
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
structure FdCommonStrictTowerModels {U T : Scheme.{u}} (h : U ≅ T) where
  [coefficient_iso : IsIso
    (AlgebraicGeometry.Scheme.completedCoefficientMap h.hom (pbcIntegralDatum l E))]
  ordinary_exact : PreservesFiniteLimits (completedModulePullback h.hom
    (pbcIntegralDatum l E)) ∧ PreservesFiniteColimits (completedModulePullback h.hom
      (pbcIntegralDatum l E))
  action : completedModulePullback h.hom (pbcIntegralDatum l E) ≅
    proEtaleModuleInverseImage h.hom (pbcAdicCompletion T (pbcIntegralDatum l E)) ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap h.hom
            (pbcIntegralDatum l E))).inv)
  ordinary_computation : ∀ P : CochainComplex
    (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (pbcActualPullComplexCounit h.hom (pbcIntegralDatum l E) P)
  tower_computation : ∀ P : CochainComplex
    (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (Functor.leftDerivedCounitOnComplex
      (completedTowerModulePullback h.hom (pbcIntegralDatum l E))
      (completedTowerPullback h.hom (pbcIntegralDatum l E))
      (completedTowerPullbackCounit h.hom (pbcIntegralDatum l E)) P)
  tower : fdCommonStrictTower l E h.hom ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
    integralOperationsPullbackTowerFunctor l E h.hom ⋙
      (Functor.whiskeringRight _ _ _).obj
        ((fdCoefficientTransport l E U).mapHomologicalComplex (.up ℤ))
  generators : ∀ (P : CochainComplex (integralTowerModules l E T) ℤ)
    (i : ℤ) (n : ℕ) (V : T.ProEt) (x : (P.X i).val.obj (op V))
    (x' : ((fdCoefficientTransport l E T).obj (P.X i)).val.obj (op V)),
    HEq x' x →
    HEq ((((tower.hom.app P).app (op n)).f i).val.app
      (op ((proEtaleBaseChange h.hom).obj V))
        (fdCommonStrictGenerator l E h.hom P i n V x'))
      (integralOperationsPullbackGenerator l E h.hom n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (coefficientIntegralScalarUnitSection l E T n (P.X i) (op V) x))
  cone : fdCommonStrictTower l E h.hom ⋙ roosF ≅
    integralOperationsPullbackComplexFunctor l E h.hom ⋙
      (fdCoefficientTransport l E U).mapHomologicalComplex (.up ℤ)
  cone_product : ∀ (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (n : ℕ),
    HEq ((cone.hom.app P).f i ≫ (fdCoefficientTransport l E U).map
      (fdCommonFrameworkProjection l E h.hom P i n))
      ((roosEval ((fdCommonStrictTower l E h.hom).obj P) n).f i ≫
        ((tower.hom.app P).app (op n)).f i)
  cone_shifted : ∀ (P : CochainComplex (integralTowerModules l E T) ℤ) (p : ℤ) (n : ℕ),
    HEq ((cone.hom.app P).f (p + 1) ≫ (fdCoefficientTransport l E U).map
      (fdCommonFrameworkShiftedProjection l E h.hom P p n))
      ((roosχ ((fdCommonStrictTower l E h.hom).obj P) p).hom ≫ biprod.fst ≫
        (Pi.π (fun k ↦ ((fdCommonStrictTower l E h.hom).obj P).asFunctor.obj (op k))
          n).f p ≫ ((tower.hom.app P).app (op n)).f p)
  derived_tower : integralOperationsGoodLocalization l E T ⋙ fdCommonDerivedTower l E h.hom ≅
    (integralOperationsGoodComplex l E T).ι ⋙ fdCommonStrictTower l E h.hom ⋙ DerivedCategory.Q
  derived_tower_counit : ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    derived_tower.hom.app P = fdCommonTowerCounit l E h.hom P.obj
  roosDerived : DerivedCategory (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ⥤
    DerivedCategory (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))
  roosDescent : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ roosDerived
  rho : roosDerived ≅ completedTowerRlim (pbcIntegralDatum l E) U
  resolution : ∀ (X I : CochainComplex
    (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
    (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] (_hinj : ∀ p : ℤ, Injective (I.X p)),
    QuasiIso (roosF.map q) ∧ QuasiIso (roosι I) ∧
    ∃ (e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
        DerivedCategory.Q.obj (roosF.obj I))
      (d : DerivedCategory.Q.obj (limit I.asFunctor) ≅
        (completedTowerRlim (pbcIntegralDatum l E) U).obj (DerivedCategory.Q.obj X)),
      e.hom = DerivedCategory.Q.map (roosι I) ∧
      d.hom ≫ (completedTowerRlim (pbcIntegralDatum l E) U).map (DerivedCategory.Q.map q) =
        fdCommonRlimUnit l E U I ∧
      roosDescent.hom.app X ≫ rho.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map (roosF.map q) ≫ e.inv ≫ d.hom
  ambient : integralDerivedPullback l E h.hom ⋙ integralDetailedTransport U l E ≅
    integralDetailedTransport T l E ⋙ pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.hom
  normalization : ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
    ambient.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (completedTowerRlim (pbcIntegralDatum l E) U).map
        (fdCommonExpandedTowerCounit l E h.hom P.obj) =
    (integralDetailedTransport U l E).map
      ((integralDerivedPullbackComparison l E h.hom).hom.app P) ≫
    fdCommonFrameworkCoefficientComparison l E h.hom P ≫
    DerivedCategory.Q.map (cone.inv.app P.obj) ≫
    roosDescent.hom.app ((fdCommonStrictTower l E h.hom).obj P.obj) ≫
    rho.hom.app (DerivedCategory.Q.obj ((fdCommonStrictTower l E h.hom).obj P.obj))
  source_mem : ∀ K : sfIntegralConstructibleCategory l E T,
    PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E)
      ((integralDetailedTransport U l E).obj ((integralDerivedPullback l E h.hom).obj K.obj))
  input_mem : ∀ K : sfIntegralConstructibleCategory l E T,
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((integralDetailedTransport T l E).obj K.obj)
  actual_ambient : (sfIntegralConstructible l E T).ι ⋙ integralDerivedPullback l E h.hom ⋙
      integralDetailedTransport U l E ≅
    (sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E ⋙
      pbcActualCompletedPull h.hom (pbcIntegralDatum l E)
  actual_normalization : ∀ K : sfIntegralConstructibleCategory l E T,
    actual_ambient.hom.app K = ambient.hom.app K.obj ≫
      ((pbcActualCompletedPullback_tower (pbcIntegralDatum l E) h.hom).exists.choose).hom.app
        ⟨(integralDetailedTransport T l E).obj K.obj, (input_mem K).1⟩
  target_mem : ∀ K : sfIntegralConstructibleCategory l E T,
    PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E)
      ((pbcActualCompletedPull h.hom (pbcIntegralDatum l E)).obj
        ((integralDetailedTransport T l E).obj K.obj))
  integral : ObjectProperty.lift (PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E))
      ((sfIntegralConstructible l E T).ι ⋙ integralDerivedPullback l E h.hom ⋙
        integralDetailedTransport U l E) source_mem ≅
    ObjectProperty.lift (PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E))
      ((sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E ⋙
        pbcActualCompletedPull h.hom (pbcIntegralDatum l E)) target_mem
  lift : ∀ K : sfIntegralConstructibleCategory l E T,
    (integral.hom.app K).hom = actual_ambient.hom.app K

/-- Both completed pullbacks are the specified realizations of the common strict tower.
Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Stacks 099N(2),(5) and 0941
(blueprint: lem-fd-pullback-common-strict-tower-models).

Proof plan (the six steps of the node):
1. Isomorphism inverse image is an exact equivalence and preserves the coefficient limit.
   Its finite constant maps commute with quotient maps. The limit projection equations
   identify the quotient-defined structure map with this isomorphism and with the PBC
   map (prop-weil-pbc-proetale-constant-ring-map). Scalar extension along a ring isomorphism
   is transported action, by lem-weil-sheaf-scalar-extension-ring-iso, with inverse x↦1⊗x.
   The exact-functor factorization and derived-functor lemmas compute ordinary pullback
   on every complex.
2. On a flat-term K-flat P the framework is its defining Roos cone H(Q). The finite
   tensor/transported-action isomorphism is multiplication, with inverse inserting 1.
   On generators both transition routes reduce the coefficient by the actual quotient
   map; hence the comparison is an isomorphism of strict towers, including transitions.
3. The adic coefficient datum reduces that same P simultaneously at every level.
   Levelwise completed-module pullback is exact because tower kernels and cokernels are
   levelwise. Its derived counit is therefore invertible on EVERY tower complex. Combine
   that counit with the reduction counit and the fixed coefficient transport. This gives
   derived_tower with precisely fdCommonTowerCounit, requiring no completed-ring K-flatness
   of the individual quotient complexes.
4. Countable products of pro-etale module sheaves are exact. Apply strictRoosComparison
   to this entire tower: both H(q) and the inclusion z↦(0,z) are quasi-isomorphisms.
   Its natural comparison is Q(H(q)) Q(ι)⁻¹, followed by the unit-normalized derived-limit
   identification. The same formula holds for every K-injective tower resolution with
   injective terms.
5. Whisker the natural Roos comparison by the ambient derived reduction/pullback tower.
   The framework's defining comparison and derived_tower give the displayed ambient
   normalization. Naturality holds on all derived morphisms. Changing P or a refinement
   conjugates this same component by the defining comparison maps; changing q uses the
   same normalized Roos component. Thus all canonical resolution comparisons agree.
6. Framework pullback preserves constructibility. The integral stratified-perfect
   characterization identifies the full integral subcategories under the fixed quotient
   coefficient identity. The ambient isomorphism places its PBC target in that same
   subcategory; fullness restricts it and its inverse and their naturality. This gives
   integral with exactly the asserted ambient lift, for every finite E. -/
theorem fdPullbackCommonStrictTowerModels {U T : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian T]
    (_hdimU : ∃ n : ℕ, topologicalKrullDim U ≤ n)
    (_hdimT : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hinvU : ∀ x : U, IsUnit (l : U.presheaf.stalk x))
    (_hinvT : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (h : U ≅ T) : Nonempty (FdCommonStrictTowerModels l E (U := U) (T := T) h) := by
  sorry

end WeilConjectures
