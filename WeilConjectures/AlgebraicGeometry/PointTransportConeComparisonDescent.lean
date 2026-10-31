/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.CompletedStalkReparametrizationCoherence
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExact
import all WeilConjectures.TraceFormula.StrictQuotientConeAugmentation
import WeilConjectures.AlgebraicGeometry.PointTransportResolutionCancellation
import all WeilConjectures.SixFunctors.FrobeniusPointTransportNatural
import all WeilConjectures.AlgebraicGeometry.PointPullbackConeLocalization
import all WeilConjectures.AlgebraicGeometry.PointQuotientAugmentationDiagram
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

/-! # Point transport, both Roos coordinates, and descent through roofs

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).

The natural index n denotes the positive exponent n+1. All section complexes have
one integral coefficient ring. The cone and its section comparison are the existing
constructions, including their shifted product coordinate. No completeness is assumed.

## Main statements

* `pointTransportConeComparison`: the strict equality and both resolution identities.
* `pointTransportConeComparisonDescent`: independence and naturality for all derived roofs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

attribute [local irreducible] limit WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard CochainComplex.mappingCocone towerTransitionEndomorphism
attribute [local irreducible] WeilConjectures.pointIntegralSections
  WeilConjectures.integralOperationsPullbackLevel
namespace WeilConjectures.PointTransportCone

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q Functor.mapDerivedCategory
  integralDerivedPullback integralDerivedPullbackComparison
  unrestrictedTowerUnit unrestrictedIntegralTransition inverseImageReductionTheta
  inverseImageRoosComparisonComplex frobeniusPointIntegralSigma
  frobeniusPointTransportIntegralComplex integralOperationsRoosMap
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose unrestrictedIntegralComplexFunctor
  unrestrictedIntegralReductionFunctor scalarReductionExtension scalarReductionExistence
  unrestrictedIntegralReductionExistence Functor.ofOpSequence Functor.ofSequence
  Functor.mapHomologicalComplex
  integralOperationsRoosFunctor integralOperationsRoos
  integralOperationsPullbackComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsGoodLocalization integralOperationsPullbackOnGood
  trfQuotientTowerFunctor PointPullbackCone.source PointPullbackCone.target
  PointPullbackCone.representativeComparison PointPullbackCone.sectionsFactors

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The exact section-complex functor with its canonical integral action.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def sections := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)

/-- The existing small-Hom localization for integral module complexes at the point.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def moduleQ := CompletedStalk.moduleQ l E

attribute [local implicit_reducible] sections moduleQ

/-- The exact-sections localization comparison, with both localization sizes explicit.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def sectionsFactors :
    @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) ⋙
        pointFibreIntegralAmbient D l E ≅ sections D l E ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _

/-- The section tower D(P) as one named object, with the original quotient transitions.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionTower
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  ((Functor.ofOpSequence (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip.obj P) ⋙ sections D l E

/-- The section tower B(P) as one named object, with the actual pullback transitions.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def pullbackTower
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  (integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P ⋙
    sections D l E

/-- D(P), the strict tower of sections of restricted finite reductions.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionTowers :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  let F := (Functor.ofOpSequence
    (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
  { obj := reductionTower D l E
    map := F.map
    map_id := F.map_id
    map_comp := F.map_comp }

/-- B(P), the strict tower of sections of the actual finite pullbacks C(P).
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def pullbackTowers :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  let F := integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
  { obj := pullbackTower D l E
    map := F.map
    map_id := F.map_id
    map_comp := F.map_comp }

attribute [local implicit_reducible] reductionTowers pullbackTowers sectionsFactors
  reductionTower pullbackTower

private theorem reductionTowers_eq_original :
    reductionTowers D l E =
      (Functor.ofOpSequence (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
        (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E) := by
  unfold reductionTowers reductionTower
  rfl

private theorem pullbackTowers_eq_original :
    pullbackTowers D l E =
      integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E) := by
  unfold pullbackTowers pullbackTower
  rfl

/-- The two published scalar-extension presentations give the identical section complex.
Source: blueprint clause (3), the common integral coefficient convention
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: unfold unrestrictedTowerComplex and unrestrictedTowerFiniteComplex, then
scalarReductionExtension and scalarReductionExistence. Unfold reductionTowers and
unrestrictedIntegralComplexFunctor, unrestrictedIntegralFiniteComplex,
unrestrictedIntegralReductionFunctor and unrestrictedIntegralReductionExistence.
The two witnesses are the same derived-change-of-rings theorem on the same limit
projection with the same standard localization instances. Restriction of scalars
and termwise sections are identical. The resulting object equality is reflexivity. -/
theorem reductionSectionModel_eq
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    (sections D l E).obj (unrestrictedTowerComplex l E (Spec (.of D.k)) n P) =
      ((reductionTowers D l E).obj P).obj (op n) := by
  unfold reductionTowers
  rfl

/-- Gamma(r_n), in the definitionally identical published reduction models.
This uses the existing unit, with no choice of a different reduction map.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionUnit
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    (sections D l E).obj P ⟶ ((reductionTowers D l E).obj P).obj (op n) :=
  (sections D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P n)

/-- The product of the maps Gamma(r_n), using the published tensor-unit reduction.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionProduct (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj P ⟶
      ∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n) :=
  Pi.lift (f := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (fun n ↦ reductionUnit D l E P n)

/-- The actual one-minus-shift endomorphism of the product of D(P).
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n)) :=
  towerTransitionEndomorphism (K := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((reductionTowers D l E).obj P))

attribute [local implicit_reducible] reductionEnd

private theorem reduction_step
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    integralOperationsTowerStep ((reductionTowers D l E).obj P) n =
      (sections D l E).map
        ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P) := by
  dsimp only [integralOperationsTowerStep, reductionTowers, reductionTower,
    Functor.comp_obj, Functor.comp_map, Functor.flip_obj_map,
    Functor.whiskeringRight_obj_obj]
  rw [Functor.ofOpSequence_map_homOfLE_succ]

set_option maxHeartbeats 600000 in
-- Reconcile the two scalar-reduction presentations when mapping their unit square.
/-- Strict compatibility of reductions makes the zero-homotopy lift a chain map.
Source: blueprint clause (3), node proof step 1
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: reduction sends 1 tensor x to 1 tensor x. Thus r_(n+1) followed by t_n is r_n.
After each product projection the product of reductions followed by 1-s is zero.
Product extensionality gives zero before localization. The differential of the zero
cochain is zero, which is precisely the mapping-cocone lift condition. -/
theorem augmentation_condition
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain ((sections D l E).obj P)
          (∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (reductionProduct D l E P ≫ reductionEnd D l E P) = 0 := by
  have hγ (n : ℕ) : reductionUnit D l E P (n + 1) ≫
      integralOperationsTowerStep ((reductionTowers D l E).obj P) n =
      reductionUnit D l E P n := by
    rw [reduction_step]
    have h := congrArg ((sections D l E).map)
      (trfStrictQuotientUnit_compatible l E (Spec (.of D.k)) P n)
    erw [CategoryTheory.Functor.map_comp] at h
    exact h
  have h : reductionProduct D l E P ≫ reductionEnd D l E P = 0 := by
    exact tuple_difference_zero
      (integralOperationsTowerStep ((reductionTowers D l E).obj P))
      (fun n ↦ reductionUnit D l E P n) hγ
  rw [h]
  simp only [CochainComplex.HomComplex.δ_zero,
    CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

/-- a_P is the specified lift (0,(Gamma(r_n)z)_n), with zero shifted component.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj P ⟶ integralOperationsRoos ((reductionTowers D l E).obj P) :=
  CochainComplex.mappingCocone.lift
    (reductionEnd D l E P)
    (reductionProduct D l E P) 0
    (augmentation_condition D l E P)

/-- c_C is the existing unique comparison preserving both sectionwise cone coordinates.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def coneSections (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj
        ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj P) ≅
      integralOperationsRoos ((pullbackTowers D l E).obj P) :=
  CompletedStalk.sectionsRoos D l E
    ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P)

/-- The specified b_q: completed pullback comparison, exact sections, then c_C.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def representativeComparison
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj N)) ≅
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P.obj)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E (frobeniusPointIso D).hom).mapIso
        (asIso (DerivedCategory.Q.map q)).symm) ≪≫
    (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).app P) ≪≫
    (sectionsFactors D l E).app
      ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj P.obj) ≪≫
    (moduleQ l E).mapIso (coneSections D l E P.obj)

attribute [local implicit_reducible] coneSections representativeComparison

/-- The actual chain map H(u)a_P in its localized section-complex presentation.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def coneArrow (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :
    (moduleQ l E).obj ((sections D l E).obj P) ⟶
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P)) :=
  (moduleQ l E).map (augmentation D l E P ≫ integralOperationsRoosMap v)

/-- The same arrow with domain the derived sections of [P], via the canonical factorization.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def resolvedArrow
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :
    (pointFibreIntegralAmbient D l E).obj (DerivedCategory.Q.obj P) ⟶
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P)) :=
  (sectionsFactors D l E).hom.app P ≫ coneArrow D l E P v

private theorem sections_map_f
    {P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ}
    (f : P ⟶ Q) (i : ℤ) :
    ((sections D l E).map f).f i = (pointIntegralSections l E D.k).map (f.f i) := rfl

/-- Exact point sections send a quasi-isomorphism to an invertible localized map.
Source: blueprint clause (3), exact point sections
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: the exact point-sections functor preserves homology, so its termwise complex
functor preserves quasi-isomorphisms. Derived localization inverts these maps. -/
theorem sections_map_isIso
    {P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ}
    (f : P ⟶ Q) [QuasiIso f] :
    IsIso ((moduleQ l E).map ((sections D l E).map f)) := by
  change IsIso ((CompletedStalk.moduleQ l E).map
    (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map f))
  infer_instance

attribute [local instance] sections_map_isIso

private theorem roos_ext
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {M : CochainComplex A ℤ} (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (f g : M ⟶ integralOperationsRoos T)
    (hf : ∀ n i, f.f i ≫ CompletedStalk.roosFirst T n i =
      g.f i ≫ CompletedStalk.roosFirst T n i)
    (hs : ∀ n i, f.f i ≫ CompletedStalk.roosSecond T n i =
      g.f i ≫ CompletedStalk.roosSecond T n i) : f = g := by
  ext i : 1
  apply WeilConjectures.cocone_degree_ext _ _ _ i
  · apply WeilConjectures.complexProduct_hom_ext (fun n ↦ T.obj (op n)) i
    intro n
    exact (Category.assoc _ _ _).trans ((hf n i).trans (Category.assoc _ _ _).symm)
  · apply WeilConjectures.complexProduct_hom_ext (fun n ↦ T.obj (op n)) (i - 1)
    intro n
    exact (Category.assoc _ _ _).trans ((hs n i).trans (Category.assoc _ _ _).symm)

private theorem augmentation_first
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ) :
    (augmentation D l E P).f i ≫
        CompletedStalk.roosFirst ((reductionTowers D l E).obj P) n i =
      (reductionUnit D l E P n).f i := by
  simp only [augmentation, reductionEnd, CompletedStalk.roosFirst, ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_fst_f]
  change (reductionProduct D l E P ≫ Pi.π _ n).f i = _
  simp only [reductionProduct, Pi.lift_π]

private theorem augmentation_second
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ) :
    (augmentation D l E P).f i ≫
      CompletedStalk.roosSecond ((reductionTowers D l E).obj P) n i = 0 := by
  simp only [augmentation, reductionEnd, CompletedStalk.roosSecond, ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v, zero_comp]

private theorem roosMap_first
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T') (n : ℕ) (i : ℤ) :
    (integralOperationsRoosMap f).f i ≫ CompletedStalk.roosFirst T' n i =
      CompletedStalk.roosFirst T n i ≫ (f.app (op n)).f i := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  simp only [CompletedStalk.roosFirst, ← Category.assoc,
    PointQuotientAugmentation.roosMap_fst]
  simp only [Category.assoc]
  have hp := congrArg (fun z ↦ z.f (p + 1)) (Pi.map_π (fun n ↦ f.app (op n)) n)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg ((CochainComplex.mappingCocone.fst
      (PointQuotientAugmentation.boundary T)).f (p + 1) ≫ ·) hp

private theorem roosMap_second
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T') (n : ℕ) (i : ℤ) :
    (integralOperationsRoosMap f).f i ≫ CompletedStalk.roosSecond T' n i =
      CompletedStalk.roosSecond T n i ≫ (f.app (op n)).f (i + -1) := by
  simp only [CompletedStalk.roosSecond, ← Category.assoc,
    PointQuotientAugmentation.roosMap_snd']
  simp only [Category.assoc]
  have hp := congrArg (fun z ↦ z.f (i + -1))
    (Pi.map_π (fun n ↦ f.app (op n)) n)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg ((CochainComplex.mappingCocone.snd
      (PointQuotientAugmentation.boundary T)).v i (i + -1) rfl ≫ ·) hp

private theorem theta_first
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ) :
    (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P).f i ≫
        CompletedStalk.roosFirst
          ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P) n i =
      (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P).f i := by
  simp only [inverseImageRoosComparisonComplex, CompletedStalk.roosFirst,
    integralOperationsPullbackTowerFunctor, Functor.flip_obj_obj,
    ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_fst_f]
  change (inverseImageReductionProduct l E (frobeniusPointIso D).hom P ≫ Pi.π _ n).f i = _
  simp only [inverseImageReductionProduct, Pi.lift_π]

private theorem theta_second
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ) :
    (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P).f i ≫
      CompletedStalk.roosSecond
        ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P) n i = 0 := by
  simp only [inverseImageRoosComparisonComplex, CompletedStalk.roosSecond,
    integralOperationsPullbackTowerFunctor, Functor.flip_obj_obj,
    ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v, zero_comp]

private theorem transport_on_complex (hl : l ≠ D.p)
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) =
      frobeniusPointTransportIntegralComplex D l hl E N P q := by
  have ht := (frobeniusPointTransportIntegral_existsUnique D l hl E
    (DerivedCategory.Q.obj N)).choose_spec.1 N P q (Iso.refl _)
  change frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) =
    (pointFibreIntegralAmbient D l E).map (𝟙 _) ≫
      frobeniusPointTransportIntegralComplex D l hl E N P q ≫
      (pointFibreIntegralAmbient D l E).map
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).map (𝟙 _)) at ht
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using ht

set_option maxHeartbeats 600000 in
-- Compare the two cone coordinates and the canonical resolution presentations.
/-- The strict comparison on both cone components and the two resolution identities.
Source: blueprint clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof (node steps 1--3): the reductions and theta maps are strictly compatible,
so their zero-first-component lifts are chain maps. Strictness of v makes H(v)
the diagonal map on both products. Exact point sections identify both products and
the finite biproduct, so c_C is the identity in these coordinates. On a section z,
the two composites are (0,(Gamma(theta_n)sigma_P z)_n) and
(0,(v_n Gamma(r_n)z)_n), equal by the augmentation equations, including the zero
shifted component. Point-transport naturality gives sigma_N Gamma(q) =
Gamma(g^-1 q) sigma_P. Exact sections and exact inverse image preserve q's
quasi-isomorphism. Under the specified representative comparison, kappa is the
zero-homotopy theta lift preceded by the inverse of g^-1(q). Cancel this inverse
against the sigma square and apply the strict identity. This gives the first
derived formula. Right cancellation of Gamma(q) gives the second; a_P is never inverted. -/
theorem pointTransportConeComparison (hl : l ≠ D.p)
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q]
    (v : (reductionTowers D l E).obj P.obj ⟶ (pullbackTowers D l E).obj P.obj)
    (hv : ∀ n : ℕ,
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫
          v.app (op n)) :
    (frobeniusPointIntegralSigma D l E P.obj ≫
        (sections D l E).map
          (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
        (coneSections D l E P.obj).hom =
      augmentation D l E P.obj ≫ integralOperationsRoosMap v) ∧
    IsIso ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ∧
    ((sections D l E).map q ≫ frobeniusPointIntegralSigma D l E N =
      frobeniusPointIntegralSigma D l E P.obj ≫ (sections D l E).map
        (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
          (.up ℤ)).map q)) ∧
    ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q) ≫
        frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
        (representativeComparison D l E N P q).hom = resolvedArrow D l E P.obj v) ∧
    (frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
        (representativeComparison D l E N P q).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        resolvedArrow D l E P.obj v) := by
  have hstrict : frobeniusPointIntegralSigma D l E P.obj ≫
      (sections D l E).map
        (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
      (coneSections D l E P.obj).hom =
      augmentation D l E P.obj ≫ integralOperationsRoosMap v := by
    apply roos_ext ((pullbackTowers D l E).obj P.obj)
    · intro n i
      simp only [HomologicalComplex.comp_f, sections_map_f,
        Category.assoc]
      rw [show (coneSections D l E P.obj).hom.f i ≫
          CompletedStalk.roosFirst ((pullbackTowers D l E).obj P.obj) n i =
          (pointIntegralSections l E D.k).map
            (CompletedStalk.roosFirst
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) n i) from
        (CompletedStalk.sectionsRoos_existsUnique D l E
          ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
            P.obj)).exists.choose_spec.1 n i]
      rw [← Functor.map_comp, theta_first D l E P.obj n i]
      rw [roosMap_first, ← Category.assoc, augmentation_first]
      exact congrArg (fun z ↦ z.f i) (hv n)
    · intro n i
      simp only [HomologicalComplex.comp_f, sections_map_f,
        Category.assoc]
      rw [show (coneSections D l E P.obj).hom.f i ≫
          CompletedStalk.roosSecond ((pullbackTowers D l E).obj P.obj) n i =
          (pointIntegralSections l E D.k).map
            (CompletedStalk.roosSecond
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) n i) from
        (CompletedStalk.sectionsRoos_existsUnique D l E
          ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
            P.obj)).exists.choose_spec.2 n i]
      rw [← Functor.map_comp, theta_second D l E P.obj n i]
      simp only [CategoryTheory.Functor.map_zero, comp_zero]
      rw [roosMap_second, ← Category.assoc, augmentation_second, zero_comp]
  have hcancel := pointTransportResolutionCancellation D l E hl N P q
  have ht := transport_on_complex D l E hl N P q
  have hd : frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
      (representativeComparison D l E N P q).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        resolvedArrow D l E P.obj v := by
    rw [ht]
    have hd := hcancel.2.2.2
    change frobeniusPointTransportIntegralComplex D l hl E N P q ≫
      (representativeComparison D l E N P q).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        (sectionsFactors D l E).hom.app P.obj ≫ (moduleQ l E).map
          (frobeniusPointIntegralSigma D l E P.obj ≫
            (sections D l E).map
              (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
            (coneSections D l E P.obj).hom) at hd
    simpa only [hstrict, resolvedArrow, coneArrow, Category.assoc] using hd
  refine ⟨hstrict, inferInstance, hcancel.2.2.1, ?_, hd⟩
  rw [hd, IsIso.hom_inv_id_assoc]

private theorem resolution_identity (hl : l ≠ D.p)
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q]
    (v : (reductionTowers D l E).obj P.obj ⟶ (pullbackTowers D l E).obj P.obj)
    (hv : ∀ n : ℕ,
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫ v.app (op n)) :
    frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
        (representativeComparison D l E N P q).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        resolvedArrow D l E P.obj v :=
  (pointTransportConeComparison D l E hl N P q v hv).2.2.2.2

private def sourceComparison :
    integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙
        pointFibreIntegralAmbient D l E ≅
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        sections D l E ⋙ moduleQ l E :=
  Functor.isoWhiskerLeft (integralOperationsGoodComplex l E (Spec (.of D.k))).ι
    (sectionsFactors D l E)

private def targetComparison :
    integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙
        (integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
          pointFibreIntegralAmbient D l E) ≅
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        pullbackTowers D l E ⋙ integralOperationsRoosFunctor ⋙ moduleQ l E :=
  PointPullbackCone.targetComparison D l E

attribute [local irreducible] sourceComparison targetComparison
attribute [local irreducible] PointPullbackCone.sourceComparison
  PointPullbackCone.targetComparison PointPullbackCone.roosComparison

/-- Good quasi-isomorphisms induce invertible maps on the whole sectionwise Roos cone.
Source: blueprint clause (3), node step 4
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: integral-operations well-definedness gives a quasi-isomorphism on the sheaf
Roos complexes. Exact sections preserve it. The natural c_C comparison conjugates
its class to the displayed diagonal Roos map, which is therefore invertible. -/
theorem pullbackRoof_isIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :
    IsIso ((moduleQ l E).map
      (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom))) := by
  let L := integralOperationsGoodLocalization l E (Spec (.of D.k))
  have : IsIso (L.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ a.hom).2 inferInstance
  apply (NatIso.isIso_map_iff (targetComparison D l E) a).mp
  change IsIso ((integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
    pointFibreIntegralAmbient D l E).map (L.map a))
  infer_instance

/-- The isomorphism T(a) for a good quasi-isomorphism, with the actual diagonal map as hom.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def pullbackRoofIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :
    (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj Q.obj)) ≅
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P.obj)) :=
  @asIso _ _ _ _
    ((moduleQ l E).map (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom)))
    (pullbackRoof_isIso D l E P Q a)

attribute [local irreducible] representativeComparison sectionsFactors coneSections
  coneArrow resolvedArrow augmentation frobeniusPointTransportIntegral

private theorem commuting_roof
    {C : Type*} [Category C] {A B C' X Y Z : C}
    (sa : A ⟶ B) (sb : A ⟶ C') (ta : X ⟶ Y) (tb : X ⟶ Z)
    (eP : B ⟶ Y) (eQ : A ⟶ X) (eP' : C' ⟶ Z)
    [IsIso sa] [IsIso ta] (ha : sa ≫ eP = eQ ≫ ta)
    (hb : sb ≫ eP' = eQ ≫ tb) :
    eP ≫ inv ta ≫ tb = inv sa ≫ sb ≫ eP' := by
  apply (cancel_epi sa).1
  calc
    sa ≫ (eP ≫ inv ta ≫ tb) = eQ ≫ tb := by
      rw [← Category.assoc sa, ha]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = sa ≫ (inv sa ≫ sb ≫ eP') := by
      simpa only [IsIso.hom_inv_id_assoc] using hb.symm

private theorem naturality_roof
    {C T : Type*} [Category C] [Category T] {S F : C ⥤ T}
    (e : S ⟶ F) {P Q P' : C} (a : Q ⟶ P) (b : Q ⟶ P')
    [IsIso (S.map a)] [IsIso (F.map a)] :
    e.app P ≫ inv (F.map a) ≫ F.map b =
      inv (S.map a) ≫ S.map b ≫ e.app P' :=
  commuting_roof _ _ _ _ _ _ _ (e.naturality a) (e.naturality b)

private def conjugate
    {C B T : Type*} [Category C] [Category B] [Category T]
    (L : C ⥤ B) {S F : B ⥤ T} {S₀ F₀ : C ⥤ T}
    (a : L ⋙ S ≅ S₀) (b : L ⋙ F ≅ F₀) (η : S ⟶ F) : S₀ ⟶ F₀ :=
  a.inv ≫ Functor.whiskerLeft L η ≫ b.hom

private theorem conjugate_app
    {C B T : Type*} [Category C] [Category B] [Category T]
    (L : C ⥤ B) {S F : B ⥤ T} {S₀ F₀ : C ⥤ T}
    (a : L ⋙ S ≅ S₀) (b : L ⋙ F ≅ F₀) (η : S ⟶ F) (X : C) :
    (conjugate L a b η).app X =
      (a.app X).inv ≫ (η.app (L.obj X) ≫ (b.app X).hom) := rfl

attribute [local irreducible] conjugate

private theorem normalize_component
    {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : f = e.hom ≫ g) : e.inv ≫ f = g := by
  rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem unique_extension
    {C T : Type*} [Category C] [Category T] {F G : C ⥤ T}
    (η : F ⟶ G) (component : ∀ X, F.obj X ⟶ G.obj X)
    (hη : ∀ X, η.app X = component X) (P : (F ⟶ G) → Prop) (hp : P η) :
    ∃! τ : F ⟶ G, (∀ X, τ.app X = component X) ∧ P τ := by
  refine ⟨η, ⟨hη, hp⟩, ?_⟩
  intro τ hτ
  apply NatTrans.ext
  funext X
  exact (hτ.1 X).trans (hη X).symm

private theorem recipe_cancel
    {C : Type*} [Category C] {X Y Z : C} (t : X ⟶ Y) (c : Y ≅ Z)
    (r : X ⟶ Z) (h : t ≫ c.hom = r) : r ≫ c.inv = t := by
  rw [← h, Category.assoc, c.hom_inv_id, Category.comp_id]

-- Its components fix the chosen natural transformation uniquely by NatTrans.ext.
private def transportNatural (hl : l ≠ D.p) :
    pointFibreIntegralAmbient D l E ⟶
      integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointFibreIntegralAmbient D l E :=
  (naturalIntegralTransport D l hl E).choose

private theorem transportNatural_app (hl : l ≠ D.p)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (transportNatural D l E hl).app N = frobeniusPointTransportIntegral D l hl E N :=
  (naturalIntegralTransport D l hl E).choose_spec N

attribute [local irreducible] transportNatural

private theorem source_map
    {P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory}
    (f : P ⟶ Q) :
    ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        sections D l E ⋙ moduleQ l E).map f =
      (moduleQ l E).map ((sections D l E).map f.hom) := rfl

private theorem target_map
    {P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory}
    (f : P ⟶ Q) :
    ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        pullbackTowers D l E ⋙ integralOperationsRoosFunctor ⋙ moduleQ l E).map f =
      (moduleQ l E).map (integralOperationsRoosMap ((pullbackTowers D l E).map f.hom)) := rfl

private theorem pullbackRoofIso_inv
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :
    (pullbackRoofIso D l E P Q a).inv =
      inv (I := pullbackRoof_isIso D l E P Q a) ((moduleQ l E).map
        (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom))) := rfl

private theorem representativeComparison_formula
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    representativeComparison D l E N P q =
      ((integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
        pointFibreIntegralAmbient D l E).mapIso
          (asIso (DerivedCategory.Q.map q)).symm) ≪≫
        (targetComparison D l E).app P := by
  simpa only [representativeComparison, PointPullbackCone.representativeComparison,
    coneSections, sectionsFactors, PointPullbackCone.sectionsFactors, targetComparison] using!
      PointPullbackCone.representativeComparison_eq D l E N P q

private theorem normalized_identity (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (v : (reductionTowers D l E).obj P.obj ⟶ (pullbackTowers D l E).obj P.obj)
    (hv : ∀ n : ℕ,
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫ v.app (op n)) :
    frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
        (targetComparison D l E).hom.app P =
      (sourceComparison D l E).hom.app P ≫ coneArrow D l E P.obj v := by
  have h := resolution_identity D l E hl P.obj P (𝟙 P.obj) v hv
  rw [representativeComparison_formula] at h
  unfold resolvedArrow at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    Iso.app_hom] at h
  simp only [CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp, Functor.comp_obj] at h
  simpa only [resolvedArrow, sourceComparison,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    sectionsFactors, PointPullbackCone.sectionsFactors] using! h

set_option maxHeartbeats 600000 in
-- Reconcile the source and target functor presentations in the roof identity.
/-- Chain-natural tower maps give the specified natural transformation on all derived
objects, independent of good representatives, with its explicit square for every roof.
Source: blueprint clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: the existing naturalIntegralTransport construction supplies a derived natural
transformation whose components are the actual integral transport. The preceding
comparison theorem proves its resolution formula. Equality of components gives
uniqueness; composing either resolution formula with its comparison inverse gives
the same transport, proving independence. Conjugate the derived transformation
by the canonical source and target comparisons on good complexes. The identity-resolution
case identifies its components with coneArrow. Its naturality squares, after cancelling
the denominator, give the explicit roof equation, with inverse target map pullbackRoofIso.inv.
No completeness or inverse augmentation is used. -/
theorem pointTransportConeComparisonDescent (hl : l ≠ D.p)
    (v : (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ reductionTowers D l E ⟶
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ pullbackTowers D l E)
    (hv : ∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫
          (v.app P).app (op n)) :
    (∃! η : pointFibreIntegralAmbient D l E ⟶
        integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointFibreIntegralAmbient D l E,
      (∀ N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
        η.app N = frobeniusPointTransportIntegral D l hl E N) ∧
      (∀ (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ N) [QuasiIso q],
        η.app (DerivedCategory.Q.obj N) ≫ (representativeComparison D l E N P q).hom =
          inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
            resolvedArrow D l E P.obj (v.app P))) ∧
    (∀ (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ N) (q' : P'.obj ⟶ N) [QuasiIso q] [QuasiIso q'],
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
          resolvedArrow D l E P.obj (v.app P) ≫
          (representativeComparison D l E N P q).inv =
        inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q')) ≫
          resolvedArrow D l E P'.obj (v.app P') ≫
          (representativeComparison D l E N P' q').inv) ∧
    (∀ (P Q P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (a : Q ⟶ P) (b : Q ⟶ P') [QuasiIso a.hom],
      IsIso ((moduleQ l E).map
        (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom))) ∧
      (coneArrow D l E P.obj (v.app P) ≫
          (pullbackRoofIso D l E P Q a).inv ≫
          (moduleQ l E).map
            (integralOperationsRoosMap ((pullbackTowers D l E).map b.hom)) =
        inv ((moduleQ l E).map ((sections D l E).map a.hom)) ≫
          (moduleQ l E).map ((sections D l E).map b.hom) ≫
          coneArrow D l E P'.obj (v.app P'))) := by
  let w : ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
      (reductionTowers D l E).obj P.obj ⟶ (pullbackTowers D l E).obj P.obj :=
    fun P ↦ v.app P
  have hw (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) :
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫ (w P).app (op n) := hv P n
  let η := transportNatural D l E hl
  have hηall := transportNatural_app D l E hl
  let L := integralOperationsGoodLocalization l E (Spec (.of D.k))
  let e := conjugate L (sourceComparison D l E)
      (targetComparison D l E) η
  have he (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
      e.app P = coneArrow D l E P.obj (w P) := by
    have hp := (congrArg (fun z ↦ z ≫
        (targetComparison D l E).hom.app P)
      (hηall (DerivedCategory.Q.obj P.obj))).trans
        (normalized_identity D l E hl P (w P) (hw P))
    exact (conjugate_app L (sourceComparison D l E)
      (targetComparison D l E) η P).trans
        (normalize_component ((sourceComparison D l E).app P)
          (η.app (DerivedCategory.Q.obj P.obj) ≫
            (targetComparison D l E).hom.app P)
          (coneArrow D l E P.obj (w P)) hp)
  refine ⟨unique_extension η _ hηall _ ?_, ?_, ?_⟩
  · intro N P q _
    rw [hηall]
    exact resolution_identity D l E hl N P q (w P) (hw P)
  · intro N P P' q q' _ _
    have recipe (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ N) [QuasiIso q] :
        inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
            resolvedArrow D l E P.obj (w P) ≫
            (representativeComparison D l E N P q).inv =
          frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) := by
      simpa only [Category.assoc] using recipe_cancel
        (frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N))
        (representativeComparison D l E N P q) _
        (resolution_identity D l E hl N P q (w P) (hw P))
    exact (recipe P q).trans (recipe P' q').symm
  · intro P Q P' a b _
    have : IsIso (L.map a) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ a.hom).2 inferInstance
    have : IsIso (((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        sections D l E ⋙ moduleQ l E).map a) :=
      by
        apply (NatIso.isIso_map_iff (sourceComparison D l E) a).mp
        change IsIso ((pointFibreIntegralAmbient D l E).map (L.map a))
        infer_instance
    have : IsIso (((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        pullbackTowers D l E ⋙ integralOperationsRoosFunctor ⋙ moduleQ l E).map a) :=
      by
        rw [target_map]
        exact pullbackRoof_isIso D l E P Q a
    refine ⟨pullbackRoof_isIso D l E P Q a, ?_⟩
    simpa only [he, source_map, target_map, pullbackRoofIso_inv] using!
      naturality_roof e a b

end WeilConjectures.PointTransportCone
