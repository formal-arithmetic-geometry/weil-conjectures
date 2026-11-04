/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarBalancingChain
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.AlgebraicGeometry.PulledNormalization.PulledReductionNormalizationComparison
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! # Unbounded coefficient comparison on flat-term K-flat pullback models

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 06YT, 06YY, 0G7D;
sites-modules.tex, Tag 03EL; blueprint thm-exc-explicit-preservation, proof paragraph 2.
(blueprint: lem-exc-unbounded-coefficient-pullback-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

private theorem conjugate_linear
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S)
    {N N' P P' : SheafOfModules.{u + 1} S} (k : N ≅ P) (l : N' ≅ P')
    (h : (SheafOfModules.restrictScalars a).obj P ⟶
      (SheafOfModules.restrictScalars a).obj P')
    (h' : (SheafOfModules.restrictScalars a).obj N ⟶
      (SheafOfModules.restrictScalars a).obj N')
    (hh : h' = (SheafOfModules.restrictScalars a).map k.hom ≫ h ≫
      (SheafOfModules.restrictScalars a).map l.inv)
    (hb : ∀ W (b : S.obj.obj W) (x : P.val.obj W),
      h.val.app W (b • x) = b • (show P'.val.obj W from h.val.app W x)) :
    ∀ W (b : S.obj.obj W) (x : N.val.obj W),
      h'.val.app W (b • x) = b • (show N'.val.obj W from h'.val.app W x) := by
  intro W b x
  rw [hh]
  change l.inv.val.app W (h.val.app W (k.hom.val.app W (b • x))) = _
  rw [map_smul, hb]
  exact (l.inv.val.app W).hom.map_smul b _

/-- Transport `t` to the scalar-extension presentations, retaining the B-action on
both its source and target. This is the displayed `t ∘ beta` in those coordinates.
Source: Stacks 03EL (blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def excScalarBalancingMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (scalarMateRestriction φ X).obj ((proEtaleConstantRingPullback B f).obj
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := Y) φ)).obj M)) ⟶
    (scalarMateRestriction φ X).obj
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj
        ((proEtaleConstantRingPullback A f).obj M)) :=
  (scalarBalancingBeta φ f).hom.app
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := Y) φ)).obj M) ≫
    (proEtaleConstantRingPullback A f).map ((scalarMateOrdinaryTensorIso φ Y).hom.app M) ≫
    t.hom.app M ≫
    (scalarMateOrdinaryTensorIso φ X).inv.app ((proEtaleConstantRingPullback A f).obj M)

/-- The ordinary coefficient/pullback mate for constant rings. -/
private abbrev balancingMate {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :=
  PulledNormalization.ordinaryMate f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing V A) (proEtaleConstantRing V B)
    (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The ordinary tensor comparison obtained by conjugating the inverse mate. -/
private def balancingTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :
    scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V :=
  Functor.isoWhiskerRight (scalarMateOrdinaryTensorIso φ X).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarBalancingBeta φ f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (balancingMate φ f).symm (scalarMateRestriction φ V) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarMateOrdinaryTensorIso φ V)

private theorem balancingTensor_hom_app {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (balancingTensor φ f).hom.app M =
      (proEtaleConstantRingPullback A f).map ((scalarMateOrdinaryTensorIso φ X).inv.app M) ≫
        (scalarBalancingBeta φ f).inv.app
          ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M) ≫
        (scalarMateRestriction φ V).map ((balancingMate φ f).inv.app M) ≫
        (scalarMateOrdinaryTensorIso φ V).hom.app ((proEtaleConstantRingPullback A f).obj M) := by
  simp [balancingTensor]

private theorem balancingTensor_map {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (scalarMateRestriction φ V).map ((balancingMate φ f).symm.hom.app M) =
      excScalarBalancingMap φ f (balancingTensor φ f) M := by
  simp only [Functor.comp_obj, Iso.symm_hom, excScalarBalancingMap, Functor.flip_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj, balancingTensor_hom_app, Category.assoc,
    Iso.hom_inv_id_app, cancelIso, Iso.hom_inv_id_app_assoc]
  exact (Category.comp_id _).symm

private theorem tensorIso_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (b : (proEtaleConstantRing X B).obj.obj U) (x : M.val.obj U) :
    ((scalarMateOrdinaryTensorIso φ X).hom.app M).val.app U
      (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U b x) =
        proEtaleTensorPair X (proEtaleConstantRing X A) M
          (scalarMateCoefficient φ X) U x b := by
  have h := (scalarMateOrdinaryTensorIso_existsUnique φ X).exists.choose_spec M U b x
  with_unfolding_all exact h

private theorem tensorIso_inv_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (b : (proEtaleConstantRing X B).obj.obj U) (x : M.val.obj U) :
    ((scalarMateOrdinaryTensorIso φ X).inv.app M).val.app U
      (proEtaleTensorPair X (proEtaleConstantRing X A) M
          (scalarMateCoefficient φ X) U x b) =
        reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U b x := by
  rw [← tensorIso_section]
  exact congrArg (fun h ↦ h.val.app U
    (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U b x))
    ((scalarMateOrdinaryTensorIso φ X).hom_inv_id_app M)

private theorem reductionTensorSection_smul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    reductionTensorSection T a M U s x = s • reductionTensorSection T a M U 1 x := by
  unfold reductionTensorSection
  simpa only [mul_one] using completedTensor_smul T a M U s 1 x

/-- The inverse ordinary mate on unit sections with arbitrary local scalars. -/
private theorem balancingMate_inv_section {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
    (x : M.val.obj (Opposite.op U)) (b : (proEtaleConstantRing X B).obj.obj (Opposite.op U)) :
    ((balancingMate φ f).inv.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction B f).unit.app
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.app
          (Opposite.op U)
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M (Opposite.op U) b x)) =
      reductionTensorSection V (proEtaleConstantRingMap (T := V) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U))
        ((proEtaleRingDirectImageMap f (proEtaleConstantRing X B)
          (proEtaleConstantRing V B) (proEtaleConstantRingComparison f B)).hom.app
            (Opposite.op U) b)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) := by
  have h1 := PulledNormalization.ordinaryMate_one f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing V A) (proEtaleConstantRing V B)
    (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm M (Opposite.op U) x
  have h4 : ((balancingMate φ f).inv.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction B f).unit.app
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.app
          (Opposite.op U)
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M (Opposite.op U) 1 x)) =
      reductionTensorSection V (proEtaleConstantRingMap (T := V) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U)) 1
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) := by
    refine (congrArg (fun z ↦ ((balancingMate φ f).inv.app M).val.app
      (Opposite.op ((proEtaleBaseChange f).obj U)) z) h1).symm.trans ?_
    exact congrArg (fun h ↦ h.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      (reductionTensorSection V (proEtaleConstantRingMap (T := V) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U)) 1
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x)))
      ((balancingMate φ f).hom_inv_id_app M)
  rw [reductionTensorSection_smul X _ M (Opposite.op U) b x, map_smul]
  change ((balancingMate φ f).inv.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      ((proEtaleRingDirectImageMap f (proEtaleConstantRing X B)
        (proEtaleConstantRing V B) (proEtaleConstantRingComparison f B)).hom.app
          (Opposite.op U) b • _) = _
  rw [map_smul, h4]
  exact (reductionTensorSection_smul V _ _ _ _ _).symm

private theorem balancingTensor_isScalarBalancing {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :
    IsScalarBalancing φ f (balancingTensor φ f) := by
  intro M U x b
  have hn : ((proEtaleConstantRingPullback A f).map
        ((scalarMateOrdinaryTensorIso φ X).inv.app M)).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction A f).unit.app
        ((scalarMateOrdinaryTensor φ X).obj M)).val.app (Opposite.op U)
          (proEtaleTensorPair X (proEtaleConstantRing X A) M
            (scalarMateCoefficient φ X) (Opposite.op U) x b)) =
      ((proEtaleConstantRingAdjunction A f).unit.app ((scalarMateRestriction φ X).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M))).val.app
          (Opposite.op U)
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M
            (Opposite.op U) b x) := by
    rw [← tensorIso_inv_section]
    exact (congrArg (fun h ↦ h.val.app (Opposite.op U)
      (proEtaleTensorPair X (proEtaleConstantRing X A) M
        (scalarMateCoefficient φ X) (Opposite.op U) x b))
      ((proEtaleConstantRingAdjunction A f).unit.naturality
        ((scalarMateOrdinaryTensorIso φ X).inv.app M))).symm
  have hβ : ((scalarBalancingBeta φ f).inv.app
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction A f).unit.app ((scalarMateRestriction φ X).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M))).val.app
          (Opposite.op U)
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M (Opposite.op U) b x)) =
      ((proEtaleConstantRingAdjunction B f).unit.app
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.app
          (Opposite.op U)
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M (Opposite.op U) b x) :=
    OrderedExchange.restrictionPullback_unit f _ _ _ _ _ _ _ _ _ _ (Opposite.op U) _
  rw [balancingTensor_hom_app]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hn, hβ, balancingMate_inv_section]
  exact tensorIso_section φ V _ _ _ _

/-- Compute coefficient extension after exact pullback using a supplied representative.
This is the pullback factorization followed by the existing universal scalar counit.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excPullbackThenCoefficientComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (directImageScalarExtension φ V).map
    ((proEtaleConstantRingDerivedPullback A f).map i.inv ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit V (proEtaleConstantRingMap (T := V) φ)
      (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)

/-- Compute pullback after coefficient extension using the same representative.
This applies exact B-pullback to the existing scalar counit, then its factorization.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excCoefficientThenPullbackComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (proEtaleConstantRingDerivedPullback B f).map
    ((directImageScalarExtension φ X).map i.inv ≫
      reductionScalarComplexCounit X (proEtaleConstantRingMap (T := X) φ) P) ≫
    (proEtaleConstantRingPullback B f).mapDerivedCategoryFactors.hom.app
      (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
        (.up ℤ)).obj P)

/-- The canonical B-linear coefficient comparison, computed on every flat-term K-flat
model, for arbitrary unbounded derived objects and arbitrary finite-ring homomorphisms.
The A-linear normalization uses the published pure-tensor predicate; the equality
with excScalarBalancingMap retains the B-action before passing to complexes.
Source: Stacks 0G7E, 06YT, 06YY, 0G7D, 03EL
(blueprint: lem-exc-unbounded-coefficient-pullback-model).

Proof:
Lift the B-linear map supplied by the scalar balancing chain to a natural isomorphism s.
Its inverse gives T degreewise. The two adjunction bijections and the unit tensor formula
identify this inverse with the ordinary coefficient/pullback mate. The general derived
mate comparison computes the canonical derived mate on every cochain representative,
using the published scalar counits and exact-pullback factorization. Naturality along
the supplied isomorphism [P] ≅ K gives the displayed computation equation.
The ringed-topos K-flat pullback theorem supplies flatness and K-flatness of the pulled
model; exactness preserves quasi-isomorphisms. The scalar counits on these K-flat models
are invertible, so both named computation morphisms are isomorphisms. This proof uses
the supplied model and the existing derived comparison, without a new localization. -/
theorem unboundedCoefficientPullbackModel
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :
    ∃ t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
        proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V,
      IsScalarBalancing φ f t ∧
      ∃ s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
          proEtaleConstantRingPullback B f ≅
        proEtaleConstantRingPullback A f ⋙
          proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ),
        (∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
          (scalarMateRestriction φ V).map (s.hom.app M) = excScalarBalancingMap φ f t M) ∧
        ∃ T : (proEtaleConstantRingPullback A f ⋙
              proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ)).mapHomologicalComplex
                (.up ℤ) ≅
            (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
              proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ),
          (∀ (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
            (n : ℤ), (T.hom.app P).f n = s.inv.app (P.X n) ∧
              (T.inv.app P).f n = s.hom.app (P.X n)) ∧
          (∀ P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing X A) P →
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology X) (R := proEtaleConstantRing X A) (P.X n)) →
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing V A)
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) ∧
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology V) (R := proEtaleConstantRing V A)
              ((((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P).X n)) ∧
            (∀ (G : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
              (q : P ⟶ G), QuasiIso q →
                QuasiIso (((proEtaleConstantRingPullback A f).mapHomologicalComplex
                  (.up ℤ)).map q)) ∧
            ∀ (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K),
              IsIso (excPullbackThenCoefficientComputation φ f P K i) ∧
              IsIso (excCoefficientThenPullbackComputation φ f P K i) ∧
              (directImageScalarPullbackIso φ f).inv.app K ≫
                  excCoefficientThenPullbackComputation φ f P K i =
                excPullbackThenCoefficientComputation φ f P K i ≫
                  DerivedCategory.Q.map (T.hom.app P)) := by
  let T := NatIso.mapHomologicalComplex (balancingMate φ f) (.up ℤ)
  refine ⟨balancingTensor φ f, balancingTensor_isScalarBalancing φ f, (balancingMate φ f).symm,
    balancingTensor_map φ f, T, ?_, ?_⟩
  · intro P n
    exact ⟨rfl, rfl⟩
  · intro P hp hf
    obtain ⟨hpf, hff⟩ := PulledNormalization.pullback_good f
      (proEtaleConstantRing X A) (proEtaleConstantRing V A)
      (proEtaleConstantRingComparison f A) P hp hf
    refine ⟨hpf, hff, ?_, ?_⟩
    · intro G q hq
      have : QuasiIso q := hq
      infer_instance
    · intro K i
      have hcX := scalarCounit_isIso X
        (proEtaleConstantRingMap (T := X) φ) P hp
      have hcV := scalarCounit_isIso V
        (proEtaleConstantRingMap (T := V) φ)
        (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) hpf
      refine ⟨?_, ?_, ?_⟩
      · unfold excPullbackThenCoefficientComputation
        infer_instance
      · unfold excCoefficientThenPullbackComputation
        infer_instance
      · have hm := PulledNormalization.derivedMate_rep f
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRing V A) (proEtaleConstantRing V B)
          (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm P
        simp only [excCoefficientThenPullbackComputation,
          excPullbackThenCoefficientComputation, Functor.map_comp, Category.assoc]
        have hn := ((directImageScalarPullbackIso φ f).inv.naturality i.inv).symm
        change (directImageScalarPullbackIso φ f).inv.app K ≫
            (proEtaleConstantRingDerivedPullback B f).map
              ((directImageScalarExtension φ X).map i.inv) =
          (directImageScalarExtension φ V).map
            ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫
              (directImageScalarPullbackIso φ f).inv.app (DerivedCategory.Q.obj P) at hn
        rw [reassoc_of% hn]
        exact congrArg (fun z ↦ (directImageScalarExtension φ V).map
          ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫ z) hm

end AlgebraicGeometry.ProEtale
