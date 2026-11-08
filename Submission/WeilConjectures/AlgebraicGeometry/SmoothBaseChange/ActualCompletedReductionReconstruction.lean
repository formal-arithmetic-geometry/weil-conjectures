/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Reconstruction in the actual completed coefficient presentation

The canonical quotient transitions are the adjuncts of the quotient units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
private def reconstructionRestrictId (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
  reconstructionRestrictId

private theorem reconstructionUnit_section
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x = pbcTensorSection φ M U 1 x :=
  (pbcScalarAdjunction_exists φ).exists.choose_spec M U x

private theorem reconstructionComp_section
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

attribute [local irreducible] pbcScalarAdjunction pbcRestrictComp

section ScalarComputation
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

private theorem reconstructionTranspose
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (N : CochainComplex (pbcModules T S) ℤ)
    (k : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ N) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
        (pbcComplexCounit φ P ≫ DerivedCategory.Q.map k) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app N =
      DerivedCategory.Q.map (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv
        P N k) := by
  change ((pbcDerivedScalarAdjunction φ).unit.app _ ≫
    (pbcDerivedRestrict φ).map (pbcComplexCounit φ P ≫ DerivedCategory.Q.map k)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality k]
  simp only [Functor.comp_map] at *
  have hu := (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P hP
  change (pbcDerivedScalarAdjunction φ).unit.app _ ≫
    (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫ _ = _ at hu
  try simp only [Category.assoc]
  erw [reassoc_of% hu]
  rw [← DerivedCategory.Q.map_comp]
  rfl

private theorem reconstructionRestrictionFactors
    (N : CochainComplex (pbcModules T B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).hom.app (DerivedCategory.Q.obj N) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app N =
      (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app N) := by
  dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  have hc := Functor.mapDerivedCategoryCompIso_fac (pbcRestrict ψ) (pbcRestrict φ) N
  have hi : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcRestrict ψ ⋙ pbcRestrict φ)) (.up ℤ)).hom.app N = 𝟙 _ := by
    ext i
    rfl
  rw [hi] at hc
  erw [DerivedCategory.Q.map_id, Category.comp_id] at hc
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private def reconstructionOrdinaryTransition (M : pbcModules T R) :
    (pbcExtend φ).obj M ⟶ (pbcRestrict ψ).obj ((pbcExtend χ).obj M) :=
  ((pbcScalarAdjunction φ).homEquiv _ _).symm
    ((pbcScalarAdjunction χ).unit.app M ≫
      (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj M))

private theorem reconstructionOrdinaryTransition_unit (M : pbcModules T R) :
    (pbcScalarAdjunction φ).unit.app M ≫
        (pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h M) ≫
        (pbcRestrictComp φ ψ χ h).hom.app ((pbcExtend χ).obj M) =
      (pbcScalarAdjunction χ).unit.app M := by
  rw [← Category.assoc]
  change ((pbcScalarAdjunction φ).homEquiv _ _
    (reconstructionOrdinaryTransition T φ ψ χ h M)) ≫ _ = _
  rw [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
  simp

private theorem reconstructionRestrictionFactors_inv
    (N : CochainComplex (pbcModules T B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).inv.app (DerivedCategory.Q.obj N) ≫
        (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj N) =
      (pbcRestrict χ).mapDerivedCategoryFactors.hom.app N ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).inv (.up ℤ)).app N) := by
  apply (cancel_epi ((pbcDerivedRestrictComp φ ψ χ h).hom.app
    (DerivedCategory.Q.obj N))).1
  simp only [Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% (reconstructionRestrictionFactors T φ ψ χ h)]
  simp only [← DerivedCategory.Q.map_comp]
  have hi : ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app N) ≫
      ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).inv (.up ℤ)).app N) = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (pbcRestrictComp φ ψ χ h).hom_inv_id_app _
  rw [hi, DerivedCategory.Q.map_id]
  erw [Category.comp_id]

private def reconstructionOrdinaryTransitionNat :
    pbcExtend φ ⟶ pbcExtend χ ⋙ pbcRestrict ψ where
  app := reconstructionOrdinaryTransition T φ ψ χ h
  naturality {M N} f := by
    apply ((pbcScalarAdjunction φ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    simp only [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
    have hn := (pbcRestrictComp φ ψ χ h).inv.naturality ((pbcExtend χ).map f)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [← hn]
    have hu := (pbcScalarAdjunction χ).unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj N)) hu

private theorem reconstructionTransition_computation
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict ψ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict ψ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      pbcComplexCounit φ P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (reconstructionOrdinaryTransitionNat T φ ψ χ h) (.up ℤ)).app P) := by
  apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
  apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app
    (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj
      (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P)))).1
  erw [reconstructionTranspose T φ P hP]
  simp only [Adjunction.homEquiv_naturality_right, pbcReductionTransition,
    Equiv.apply_symm_apply, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ((pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    (pbcComplexCounit χ P))]
  erw [reconstructionRestrictionFactors_inv T φ ψ χ h]
  have hu := (pbcDerivedScalarAdjunction_exists χ).exists.choose_spec P hP
  change (pbcDerivedScalarAdjunction χ).unit.app _ ≫
    (pbcDerivedRestrict χ).map (pbcComplexCounit χ P) ≫ _ = _ at hu
  try simp only [Category.assoc] at hu ⊢
  erw [reassoc_of% hu]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext i
  change _ = ((pbcScalarAdjunction φ).unit.app (P.X i) ≫
    (pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h (P.X i)))
  change _ = (pbcScalarAdjunction φ).homEquiv _ _
    (reconstructionOrdinaryTransition T φ ψ χ h (P.X i))
  rw [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
  rfl

private theorem reconstructionRestrictedTransition_computation
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    ((pbcDerivedRestrict φ).map (pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedRestrictComp φ ψ χ h).hom.app
        ((pbcDerivedExtend χ).obj (DerivedCategory.Q.obj P))) ≫
        (pbcDerivedRestrict χ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (reconstructionOrdinaryTransitionNat T φ ψ χ h) (.up ℤ)).app P) ≫
            (NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app
              (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  simp only [Category.assoc]
  rw [← reassoc_of% ((pbcDerivedRestrictComp φ ψ χ h).hom.naturality
    (pbcComplexCounit χ P))]
  erw [reconstructionRestrictionFactors T φ ψ χ h]
  simp only [← Functor.map_comp_assoc]
  rw [reconstructionTransition_computation T φ ψ χ h P hP]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map, DerivedCategory.Q.map_comp]

end ScalarComputation

private theorem reconstructionOrdinaryTensor
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (((pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h M) ≫
      (pbcRestrictComp φ ψ χ h).hom.app ((pbcExtend χ).obj M)).val.app U)
        (pbcTensorSection φ M U s x) =
      pbcTensorSection χ M U (ψ.hom.app U s) x := by
  let g := reconstructionOrdinaryTransition T φ ψ χ h M
  have hunit := reconstructionOrdinaryTransition_unit T φ ψ χ h M
  have hg : g.val.app U (pbcTensorSection φ M U 1 x) =
      pbcTensorSection χ M U 1 x := by
    have hh := congrArg (fun k ↦ k.val.app U x) hunit
    change ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (((pbcScalarAdjunction φ).unit.app M).val.app U x)) =
      ((pbcScalarAdjunction χ).unit.app M).val.app U x at hh
    rw [show ((pbcScalarAdjunction φ).unit.app M).val.app U x =
        pbcTensorSection φ M U 1 x from
      reconstructionUnit_section T φ M U x,
      show ((pbcScalarAdjunction χ).unit.app M).val.app U x =
        pbcTensorSection χ M U 1 x from
      reconstructionUnit_section T χ M U x] at hh
    erw [show ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
        (g.val.app U (pbcTensorSection φ M U 1 x)) =
        g.val.app U (pbcTensorSection φ M U 1 x) from
      reconstructionComp_section T φ ψ χ h _ U _] at hh
    exact hh
  change ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (pbcTensorSection φ M U s x)) = _
  rw [show ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (pbcTensorSection φ M U s x)) =
      g.val.app U (pbcTensorSection φ M U s x) from
    reconstructionComp_section T φ ψ χ h _ U _]
  rw [show pbcTensorSection φ M U s x = s • pbcTensorSection φ M U 1 x by
    simpa only [pbcTensorSection, reductionTensorSection, pbcExtend, reductionChange,
      mul_one] using (tensorSection_smul T φ M U s 1 x).symm]
  rw [map_smul, hg]
  change ψ.hom.app U s • pbcTensorSection χ M U 1 x = _
  simpa only [pbcTensorSection, reductionTensorSection, pbcExtend, reductionChange,
    mul_one] using tensorSection_smul T χ M U (ψ.hom.app U s) 1 x

private theorem reconstructionOrdinaryStep (b a : ℕ) (hab : a ≤ b)
    (M : pbcModules T (pbcAdicCompletion T d)) :
    (pbcRestrict (pbcAdicProjection T d b)).map
        (reconstructionOrdinaryTransition T (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) M) ≫
        (pbcRestrictComp (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab)).hom.app
            ((pbcExtend (pbcAdicProjection T d a)).obj M) =
      (completedReductionTransition T d b a hab).app M := by
  apply level_hom_ext T (pbcAdicProjection T d b) M
  intro U s x
  exact (reconstructionOrdinaryTensor T (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab) M U s x).trans
      ((completedReductionTransition_exists T d b a hab).exists.choose_spec M U s x).symm

private theorem reconstructionTransition_natural
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules T R)} (f : K ⟶ L) :
    (pbcDerivedExtend φ).map f ≫ pbcReductionTransition φ ψ χ h L =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map f) := by
  let a := pbcDerivedScalarAdjunction φ
  apply (a.homEquiv K _).injective
  dsimp only [pbcReductionTransition]
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    ((pbcDerivedExtend χ).map f)
  dsimp only [Functor.comp_map] at hn
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hn, ← Category.assoc, hu, Category.assoc]

private def reconstructionStep (n : ℕ) :
    pbcCompletedReduction T d (n + 1) ⋙
        pbcDerivedRestrict (pbcAdicProjection T d (n + 1)) ⟶
      pbcCompletedReduction T d n ⋙ pbcDerivedRestrict (pbcAdicProjection T d n) where
  app K := (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
    (pbcReductionTransition (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
        ((pbcCompletedReduction T d n).obj K)
  naturality {K L} f := by
    dsimp only [Functor.comp_map]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [reconstructionTransition_natural T]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.naturality
        ((pbcCompletedReduction T d n).map f)
    dsimp only [Functor.comp_map] at hn
    rw [hn]

private def reconstructionStrictStep (n : ℕ) :
    completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1) ⟶
      completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n :=
  Functor.whiskerLeft (completedReductionTower T d)
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _
      (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1))
      (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n)
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
        (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ))
          DerivedCategory.Q))

private theorem reconstructionStep_comparison (n : ℕ) :
    reconstructionStrictStep T d n ≫ completedReductionEvaluation T d n =
      completedReductionEvaluation T d (n + 1) ≫ reconstructionStep T d n := by
  apply derived_natTrans_ext _ _
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P)
    (fun X ↦ by
      obtain ⟨P, p, hk, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients
          (R := completedReductionCoefficient T d) X
      exact ⟨P, p, hk, hp⟩)
  intro P hP
  let φ := pbcAdicProjection T d n
  let c := (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
    (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
  have : IsIso (pbcComplexCounit φ P) := scalarCounit_isIso T φ P hP
  have : IsIso c := by dsimp [c]; infer_instance
  apply (cancel_mono c).1
  simp only [NatTrans.comp_app, Category.assoc]
  have he (i : ℕ) :=
    (completedReductionEvaluation_exists T d i).choose_spec.1.2 P hP
  have hs := reconstructionRestrictedTransition_computation T
    (pbcAdicProjection T d (n + 1))
    (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
    (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) P hP
  let J := (completedReductionComplexTowerFunctor T d).obj P
  let q := completedReductionTowerComplexCounit T d P
  let E (i : ℕ) := reductionTowerDerivedEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) i
  let F (i : ℕ) := reductionTowerEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) i
  let τ := Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ (E (n + 1)) (E n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
      (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ))
        DerivedCategory.Q)
  let t := (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
    (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ)).app J
  have ht : τ.app (DerivedCategory.Q.obj J) ≫ (F n).mapDerivedCategoryFactors.hom.app J =
      (F (n + 1)).mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map t := by
    dsimp only [τ]
    erw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Functor.whiskerRight_app, Category.assoc]
    dsimp only [F, t]
    simp only [Iso.inv_hom_id_app, Category.comp_id]
  have hj :
      (((pbcRestrict (pbcAdicProjection T d (n + 1))).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (reconstructionOrdinaryTransitionNat T (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))) (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex (pbcRestrictComp (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom (.up ℤ)).app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)) = t := by
    apply HomologicalComplex.Hom.ext
    funext i
    dsimp only [φ, t, J, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, reconstructionOrdinaryTransitionNat,
      Functor.mapHomologicalComplex_obj_X, completedTowerEvaluationStep,
      completedReductionComplexTowerFunctor, completedReductionModuleTowerFunctor,
      completedReductionModuleTower]
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    exact reconstructionOrdinaryStep T d (n + 1) n (Nat.le_succ n) (P.X i)
  rw [hj] at hs
  simp only [Category.assoc] at hs
  dsimp only [reconstructionStrictStep, Functor.whiskerLeft_app]
  change τ.app _ ≫ (completedReductionEvaluation T d n).app _ ≫ c =
    (completedReductionEvaluation T d (n + 1)).app _ ≫
      (reconstructionStep T d n).app _ ≫ c
  dsimp only [c]
  erw [he n]
  change _ = (completedReductionEvaluation T d (n + 1)).app _ ≫
    (((pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map _) ≫ _) ≫ _
  simp only [Category.assoc]
  erw [hs]
  erw [reassoc_of% (he (n + 1))]
  have hn := τ.naturality q
  try dsimp only [Functor.comp_map] at hn
  change τ.app _ ≫ (E n).map q ≫ (F n).mapDerivedCategoryFactors.hom.app J = _
  rw [← Category.assoc, ← hn, Category.assoc, ht]

end AlgebraicGeometry.Scheme
