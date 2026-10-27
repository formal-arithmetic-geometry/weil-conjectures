/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralCoefficientPresentationComparison
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.IntegralReductionTowerUnrestricted

/-! # Data for the strict point quotient towers

(blueprint: def-trf-point-quotient-tower-data)

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3)
(blueprint: lem-trf-point-quotient-tower-homotopy).

The index n denotes the positive exponent n+1. Both functors are constructed from
published strict quotient diagrams before localization. The coherent-source comparison
uses the normalized coefficient-presentation isomorphisms on the entire diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointQuotientTower

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted scalarReductionDerivedExistence
  HasDerivedCategory.standard pointIntegralSectionMap unrestrictedModuleStep
  unrestrictedTowerResolutionIso unrestrictedTowerUnit unrestrictedIntegralTransition
  unrestrictedIntegralReductionExistence scalarReductionExistence


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing strict sheaf quotient tower, reordered degreewise.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def sourceSheafTower :=
  (Functor.ofOpSequence
    (X := fun n ↦ unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (HomologicalComplex.functorEquivalence
        (integralTowerModules l E (Spec (.of D.k))) (.up ℤ) ℕᵒᵖ).inverse

/-- The existing strict finite-pullback diagram, including its coefficient-induced steps.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def targetSheafTower (g : Spec (.of D.k) ⟶ Spec (.of D.k)) :=
  integralOperationsPullbackTowerFunctor l E g ⋙
    (HomologicalComplex.functorEquivalence
      (integralTowerModules l E (Spec (.of D.k))) (.up ℤ) ℕᵒᵖ).inverse

/-- Exact point sections applied to a strict diagram, with constant integral scalars.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
abbrev sectionsTowers :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k)

/-- Exact evaluation remains left exact on the whole diagram category.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
instance sectionsTowersLimits : PreservesFiniteLimits (sectionsTowers D l E) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Exact evaluation remains right exact on the whole diagram category.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
instance sectionsTowersColimits : PreservesFiniteColimits (sectionsTowers D l E) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- D(P) consists of Gamma(P tensor S_n), with the published quotient transitions.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def source := sourceSheafTower D l E ⋙ (sectionsTowers D l E).mapHomologicalComplex (.up ℤ)

/-- B(P) consists of Gamma(Res g_n^*(P tensor S_n)), with the same representative P.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def target (g : Spec (.of D.k) ⟶ Spec (.of D.k)) :=
  targetSheafTower D l E g ⋙ (sectionsTowers D l E).mapHomologicalComplex (.up ℤ)

/-- The module functor acting on each component of the source homotopy.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def sourceLevel (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n)) ⋙
      pointIntegralSections l E D.k

/-- The module functor acting on each component of the pullback homotopy.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def targetLevel (g : Spec (.of D.k) ⟶ Spec (.of D.k)) (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n ⋙
    integralOperationsLevelPullback l E g n ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n)) ⋙
        pointIntegralSections l E D.k

/-- The homotopy relation on the full category of flat-term K-flat representatives.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def goodHomotopyRelation : HomRel
    (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory :=
  fun _ _ f f' ↦ Nonempty (Homotopy f.hom f'.hom)

/-- Standard localization for the strict integral module towers.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
instance moduleTowersHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- Transport a whole strict diagram from the Cont-presentation to the detailed one.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
abbrev restrictTowers
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict e.inv)

/-- Scalar restriction preserves finite limits on strict diagrams.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
instance restrictTowersLimits
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) :
    PreservesFiniteLimits (restrictTowers D l E e) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Scalar restriction preserves finite colimits on strict diagrams.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
instance restrictTowersColimits
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) :
    PreservesFiniteColimits (restrictTowers D l E e) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The termwise Cont-presentation reduction tower, transported back to R-modules.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def presentedSheafTower
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) :=
  (pbcRestrict e.hom).mapHomologicalComplex (.up ℤ) ⋙
    completedReductionComplexTowerFunctor (Spec (.of D.k)) (pbcIntegralDatum l E) ⋙
      (restrictTowers D l E e).mapHomologicalComplex (.up ℤ)

/-- Sections of the actual coherent reduction tower, after coefficient transport.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def coherentSections
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) :=
  pbcDerivedRestrict e.hom ⋙
    completedReductionTower (Spec (.of D.k)) (pbcIntegralDatum l E) ⋙
      (restrictTowers D l E e).mapDerivedCategory ⋙ (sectionsTowers D l E).mapDerivedCategory

/-- The canonical whole-diagram comparison, normalized on sheafified pure tensors.
The last equation identifies sections of the derived coherent tower with D(P) by
transporting its actual universal counit, rather than choosing a derived isomorphism.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
def CoherentSourceComparison
    (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
    ∃ r : (presentedSheafTower D l E e).obj P.obj ≅ (sourceSheafTower D l E).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (b : ((pbcAdicRings (Spec (.of D.k)) (pbcIntegralDatum l E)).obj (op n)).obj.obj U)
        (x : (P.obj.X i).val.obj U),
        (((r.hom.f i).app (op n)).val.app U)
            (reductionTensorSection (Spec (.of D.k))
              (completedReductionProjection (Spec (.of D.k)) (pbcIntegralDatum l E) n)
              ((pbcRestrict e.hom).obj (P.obj.X i)) U b x) =
          unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.obj.X i) U
            ((IntegralCoefficientPresentation.level l E (Spec (.of D.k)) q n).hom.hom.app U b)
            x) ∧
      ∃ γ : (coherentSections D l E e).obj (DerivedCategory.Q.obj P.obj) ≅
          DerivedCategory.Q.obj ((source D l E).obj P.obj),
        γ.hom =
          (sectionsTowers D l E).mapDerivedCategory.map
            ((restrictTowers D l E e).mapDerivedCategory.map
              ((completedReductionTower (Spec (.of D.k)) (pbcIntegralDatum l E)).map
                ((pbcRestrict e.hom).mapDerivedCategoryFactors.hom.app P.obj) ≫
                completedReductionTowerComplexCounit (Spec (.of D.k)) (pbcIntegralDatum l E)
                  (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ)).obj P.obj))) ≫
            (sectionsTowers D l E).mapDerivedCategory.map
              ((restrictTowers D l E e).mapDerivedCategoryFactors.hom.app
                ((completedReductionComplexTowerFunctor (Spec (.of D.k))
                  (pbcIntegralDatum l E)).obj
                    (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ)).obj P.obj))) ≫
            (sectionsTowers D l E).mapDerivedCategory.map (DerivedCategory.Q.map r.hom) ≫
            (sectionsTowers D l E).mapDerivedCategoryFactors.hom.app
              ((sourceSheafTower D l E).obj P.obj)


end WeilConjectures.PointQuotientTower
