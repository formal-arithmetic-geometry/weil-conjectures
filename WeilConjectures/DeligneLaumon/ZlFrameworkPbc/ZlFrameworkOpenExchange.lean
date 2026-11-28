/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlCompactificationOpenDiagram
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProetaleStrictTowerRealization
import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlFrameworkQuotientAugmentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralRingedOpenPullSupport
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedPullCompletion
import WeilConjectures.SixFunctors.OpenRestrictionCompleteness.OpenRestrictionCompleteness
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorOrdinaryTransport
import WeilConjectures.SixFunctors.IntegralOpenReduction.NormalizedOpenSections
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientOperationsExistence
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Framework open exchange in its own coefficient presentation

This file constructs the quotient-unit comparison from the ordinary pullback with the framework
completed coefficient sheaf into the Roos realization of the integral pullback, and the
resulting open pullback realization on completed constructible complexes.

## Main statements

- `frameworkPullChain_naturality`: the quotient-unit comparison is natural in the complex.
- `frameworkPullChain_quasiIso`: on good representatives of constructible complexes it is a
  quasi-isomorphism.
- `frameworkOpenPullRealization_existsUnique`: the resulting natural isomorphism on completed
  constructible complexes exists and is unique.

## Implementation details

The quotient coordinates of a chain map out of the framework pullback are compared through the
pullback/direct-image adjunction, which reduces naturality to the naturality of the finite
pullback and reduction units. On a good representative the comparison is the quotient completion
unit of the pulled-back complex followed by an isomorphism of Roos complexes, so it is a
quasi-isomorphism because open restriction preserves completeness. The comparisons on good
representatives form a natural transformation, which descends along the localization of good
complexes to a transformation of derived functors; it is invertible on constructible objects
since every object is isomorphic to the image of a good representative. Uniqueness follows from
the same essential surjectivity.

## References

* Stacks Project, Tags 099N(5), 08TC, 09BQ
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ZlFrameworkPbc

-- `SignedDoubleHomCone.moduleBinaryBiproducts` leaves its universe free and gets stuck
-- against the biproducts of the completed integral sheaf modules.
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts

open PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary pullback with the framework completed coefficient sheaf. -/
abbrev frameworkModulePull {U T : Scheme.{u}} (h : U ⟶ T) :=
  proEtaleRingModulePullback h ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull h)

/-- The canonical quotient-unit/Roos normalization. It specifies every first-coordinate
projection on inverse-image generators and the entire shifted coordinate as zero. -/
def FrameworkPullChainSpec {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P) : Prop :=
  (∀ (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)),
    ((ξ ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
      Pi.π (fun n ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)) n).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
          (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x)) ∧
  (∀ (i j : ℤ) (hij : i + -1 = j), ξ.f i ≫
    (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
        i j hij = 0)

private theorem coconeDegree_ext
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {P K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

/-- Two chain maps from a framework pullback into the Roos realization of an integral pullback
agree once their quotient coordinates agree on inverse-image generators and their shifted
coordinates agree. -/
private theorem frameworkPull_hom_ext {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ}
    (ξ η : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P')
    (h₁ : ∀ (n : ℕ) (i : ℤ),
      (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
        ((completed l E).pull h)).homEquiv _ _ ((ξ ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun n ↦
          ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op n)) n).f i) =
      (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
        ((completed l E).pull h)).homEquiv _ _ ((η ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun n ↦
          ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op n)) n).f i))
    (h₂ : ∀ i : ℤ, ξ.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P'))).v
        i (i - 1) (by omega) =
      η.f i ≫ (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P'))).v
          i (i - 1) (by omega)) : ξ = η := by
  have hf : ξ ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) =
      η ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) := by
    apply Pi.hom_ext
    intro n
    ext i : 1
    exact ((proEtaleRingModuleAdjunction h ((completed l E).ring T)
      ((completed l E).ring U) ((completed l E).pull h)).homEquiv (P.X i) _).injective (h₁ n i)
  ext i : 1
  exact coconeDegree_ext _ ξ η i (congrArg (fun z ↦ z.f i) hf) (h₂ i)

private theorem frameworkPullChain_ext {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ η : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P)
    (hξ : FrameworkPullChainSpec l E h P ξ)
    (hη : FrameworkPullChainSpec l E h P η) : ξ = η :=
  frameworkPull_hom_ext l E h ξ η (fun n i ↦ by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hξ.1 n i V.unop x).trans (hη.1 n i V.unop x).symm)
    (fun i ↦ (hξ.2 i (i - 1) (by omega)).trans (hη.2 i (i - 1) (by omega)).symm)

/-- There is a unique chain map from the framework pullback of `P` to the Roos realization of
the integral pullback satisfying the quotient-unit normalization `FrameworkPullChainSpec`. -/
theorem frameworkPullChain_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃! ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P,
      FrameworkPullChainSpec l E h P ξ := by
  obtain ⟨γ, hγ, hgen⟩ := frameworkQuotientAugmentation_exists l E h P
  let C := (integralOperationsPullbackTowerFunctor l E h).obj P
  let α : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun n : ℕ ↦ C.obj (op n) := Pi.lift γ
  have hα : α ≫ scalarRoosBoundary C = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [α, scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Category.comp_id, Category.assoc, Pi.lift_comp_π,
      Preadditive.sub_comp, zero_comp]
    rw [← Category.assoc, Pi.lift_comp_π]
    exact sub_eq_zero.mpr (hγ n).symm
  let ξ := CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 (by simp [hα])
  have hξ : FrameworkPullChainSpec l E h P ξ := by
    constructor
    · intro n i V x
      have hf : ξ ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
          Pi.π (fun n : ℕ ↦ C.obj (op n)) n = γ n := by
        rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst, Pi.lift_comp_π]
      exact (congrArg (fun f ↦ (f.f i).val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
            (op V) x)) hf).trans (hgen n i V x)
    · intro i j hij
      exact CochainComplex.mappingCocone.lift_f_snd_v (scalarRoosBoundary C) α 0
        (by simp [hα]) i j hij
  exact ⟨ξ, hξ, fun η hη ↦ frameworkPullChain_ext l E h P η ξ hη hξ⟩

/-- The quotient-diagram augmentation into the Roos realization, i.e. the unique chain map
satisfying `FrameworkPullChainSpec`. -/
def frameworkPullChain {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  (frameworkPullChain_existsUnique l E h P).exists.choose

/-- The chosen chain map `frameworkPullChain` satisfies the quotient-unit normalization. -/
theorem frameworkPullChain_spec {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    FrameworkPullChainSpec l E h P (frameworkPullChain l E h P) :=
  (frameworkPullChain_existsUnique l E h P).exists.choose_spec

private theorem frameworkHomEquiv_apply {U T : Scheme.{u}} (h : U ⟶ T)
    {M : integralTowerModules l E T} {N : integralTowerModules l E U}
    (k : (frameworkModulePull l E h).obj M ⟶ N) (V : T.ProEt) (x : M.val.obj (op V)) :
    ((proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ k).val.app (op V) x =
      k.val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app M).val.app (op V) x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

private theorem frameworkPullLevel_naturality {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (n : ℕ) (i : ℤ)
    (ψ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))
    (ψ' : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P' ⟶
      ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op n))
    (hψ : ∀ (V : T.ProEt) (x : (P.X i).val.obj (op V)),
      (ψ.f i).val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
            (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x))
    (hψ' : ∀ (V : T.ProEt) (x : (P'.X i).val.obj (op V)),
      (ψ'.f i).val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P'.X i)).val.app
            (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P').X i) V
        (unrestrictedIntegralTensorSection l E T n (P'.X i) (op V) 1 x)) :
    let adj := proEtaleRingModuleAdjunction h ((completed l E).ring T)
      ((completed l E).ring U) ((completed l E).pull h)
    φ.f i ≫ adj.homEquiv _ _ (ψ'.f i) = adj.homEquiv _ _ (ψ.f i) ≫
      (SheafOfModules.pushforward _).map
        ((((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n)).f i) := by
  intro adj
  let adjn := coefficientProEtaleModuleAdjunction.{u, u} h
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let red := (scalarReductionExtension_adjunction l E T n).choose
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (adj.homEquiv _ _ (ψ'.f i)).val.app V ((φ.f i).val.app V x) =
    ((((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n)).f i).val.app
      (op ((proEtaleBaseChange h).obj V.unop)) ((adj.homEquiv _ _ (ψ.f i)).val.app V x)
  rw [frameworkHomEquiv_apply, frameworkHomEquiv_apply]
  have hred : (((unrestrictedIntegralFiniteComplex l E T n).map φ).f i).val.app V
      (unrestrictedIntegralTensorSection l E T n (P.X i) V 1 x) =
      unrestrictedIntegralTensorSection l E T n (P'.X i) V 1 ((φ.f i).val.app V x) := by
    have h₁ : unrestrictedIntegralTensorSection l E T n (P.X i) V 1 x =
        (red.unit.app (P.X i)).val.app V x :=
      (unrestrictedTowerUnit_condition l E T P n i V x).symm
    have h₂ : unrestrictedIntegralTensorSection l E T n (P'.X i) V 1
        ((φ.f i).val.app V x) =
        (red.unit.app (P'.X i)).val.app V ((φ.f i).val.app V x) :=
      (unrestrictedTowerUnit_condition l E T P' n i V ((φ.f i).val.app V x)).symm
    rw [h₁, h₂]
    exact (congrArg (fun k ↦ k.val.app V x) (red.unit.naturality (φ.f i))).symm
  have hg (y : (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i).val.obj V) :
      ((((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n)).f i).val.app
          (op ((proEtaleBaseChange h).obj V.unop))
        (integralOperationsPullbackGenerator l E h n
          (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V.unop y) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P').X i) V.unop
        ((((unrestrictedIntegralFiniteComplex l E T n).map φ).f i).val.app V y) :=
    (congrArg (fun k ↦ k.val.app V y)
      (adjn.unit.naturality (((unrestrictedIntegralFiniteComplex l E T n).map φ).f i))).symm
  refine (hψ' V.unop _).trans (Eq.trans ?_ (congrArg
    (((((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n)).f i).val.app
      (op ((proEtaleBaseChange h).obj V.unop))) (hψ V.unop x)).symm)
  exact (congrArg _ hred.symm).trans (hg _).symm

private theorem frameworkHomEquiv_naturality_left {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P')
    {K : CochainComplex (integralTowerModules l E U) ℤ} (i : ℤ)
    (ψ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P' ⟶ K) :
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _
        ((((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).map φ ≫ ψ).f i) =
      φ.f i ≫ (proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).homEquiv _ _ (ψ.f i) := by
  rw [HomologicalComplex.comp_f]
  exact Adjunction.homEquiv_naturality_left _ _ _

private theorem frameworkHomEquiv_naturality_right {U T : Scheme.{u}} (h : U ⟶ T)
    {P : CochainComplex (integralTowerModules l E T) ℤ}
    {K K' : CochainComplex (integralTowerModules l E U) ℤ} (i : ℤ)
    (ψ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) (k : K ⟶ K') :
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ ((ψ ≫ k).f i) =
      (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
        ((completed l E).pull h)).homEquiv _ _ (ψ.f i) ≫
        (SheafOfModules.pushforward _).map (k.f i) := by
  rw [HomologicalComplex.comp_f]
  exact Adjunction.homEquiv_naturality_right _ _ _

private theorem roosMap_fst_π
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : V ⟶ W) (n : ℕ) :
    integralOperationsRoosFunctor.map α ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary W) ≫
          Pi.π (fun m ↦ W.obj (op m)) n =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary V) ≫
        Pi.π (fun m ↦ V.obj (op m)) n ≫ α.app (op n) := by
  ext j : 1
  have h₁ := integralOperationsRoosFunctor_map_fst α j
  have h₂ := congrArg (fun f ↦ f.f j) (Limits.Pi.map_π (fun m : ℕ ↦ α.app (op m)) n)
  simp only [HomologicalComplex.comp_f] at h₁ h₂ ⊢
  rw [reassoc_of% h₁, h₂]

private theorem frameworkPullTower_fst {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (n : ℕ) :
    (integralOperationsPullbackComplexFunctor l E h).map φ ≫
      CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op m)) n =
      CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n ≫
            ((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n) :=
  roosMap_fst_π _ n

private theorem frameworkPullTower_snd {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (i : ℤ) :
    ((integralOperationsPullbackComplexFunctor l E h).map φ).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          ((integralOperationsPullbackTowerFunctor l E h).obj P'))).v i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          ((integralOperationsPullbackTowerFunctor l E h).obj P))).v i (i - 1) (by omega) ≫
        (Limits.Pi.map (fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n))).f (i - 1) :=
  integralOperationsRoosFunctor_map_snd _ i

private theorem frameworkPullChain_naturality_left {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (n : ℕ) (i : ℤ) :
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ (((((frameworkModulePull l E h).mapHomologicalComplex
          (.up ℤ)).map φ ≫
        frameworkPullChain l E h P') ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op m)) n).f i) =
      φ.f i ≫ (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ ((frameworkPullChain l E h P' ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
            ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op m)) n).f i)
            := by
  rw [Category.assoc]
  exact frameworkHomEquiv_naturality_left l E h φ i _

private theorem frameworkPullChain_naturality_right {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (n : ℕ) (i : ℤ) :
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ (((frameworkPullChain l E h P ≫
        (integralOperationsPullbackComplexFunctor l E h).map φ) ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
            ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op m)) n).f i) =
      (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).homEquiv _ _ ((frameworkPullChain l E h P ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
            ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n).f i) ≫
        (SheafOfModules.pushforward _).map
          ((((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n)).f i) := by
  have e : (frameworkPullChain l E h P ≫
      (integralOperationsPullbackComplexFunctor l E h).map φ) ≫
      CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P')) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P').obj (op m)) n =
      (frameworkPullChain l E h P ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
            ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n) ≫
            ((integralOperationsPullbackTowerFunctor l E h).map φ).app (op n) := by
    rw [Category.assoc, frameworkPullTower_fst]
    simp only [Category.assoc]
  rw [e]
  exact frameworkHomEquiv_naturality_right l E h i _ _

private theorem frameworkPullChain_naturality_snd_left {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (i : ℤ) :
    (((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).map φ ≫
        frameworkPullChain l E h P').f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          ((integralOperationsPullbackTowerFunctor l E h).obj P'))).v i (i - 1) (by omega) =
      0 := by
  rw [HomologicalComplex.comp_f, Category.assoc,
    (frameworkPullChain_spec l E h P').2 i (i - 1) (by omega), comp_zero]

private theorem frameworkPullChain_naturality_snd_right {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') (i : ℤ) :
    (frameworkPullChain l E h P ≫ (integralOperationsPullbackComplexFunctor l E h).map φ).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          ((integralOperationsPullbackTowerFunctor l E h).obj P'))).v i (i - 1) (by omega) =
      0 := by
  rw [HomologicalComplex.comp_f, Category.assoc, frameworkPullTower_snd,
    reassoc_of% ((frameworkPullChain_spec l E h P).2 i (i - 1) (by omega)), zero_comp]

/-- The quotient-unit comparison `frameworkPullChain` is natural in the complex. -/
theorem frameworkPullChain_naturality {U T : Scheme.{u}} (h : U ⟶ T)
    {P P' : CochainComplex (integralTowerModules l E T) ℤ} (φ : P ⟶ P') :
    ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).map φ ≫
        frameworkPullChain l E h P' =
      frameworkPullChain l E h P ≫ (integralOperationsPullbackComplexFunctor l E h).map φ :=
  frameworkPull_hom_ext l E h _ _
    (fun n i ↦ (frameworkPullChain_naturality_left l E h φ n i).trans
      ((frameworkPullLevel_naturality l E h φ n i _ _
        ((frameworkPullChain_spec l E h P).1 n i)
        ((frameworkPullChain_spec l E h P').1 n i)).trans
      (frameworkPullChain_naturality_right l E h φ n i).symm))
    (fun i ↦ (frameworkPullChain_naturality_snd_left l E h φ i).trans
      (frameworkPullChain_naturality_snd_right l E h φ i).symm)

/-- Ordinary pullback along `h`, on complexes. -/
private abbrev frameworkPullComplex {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    CochainComplex (integralTowerModules l E U) ℤ :=
  ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P

/-- The quotient-unit comparison is the quotient completion unit of the pulled-back complex,
followed by the strict tower comparison of a pullback realization. -/
private theorem frameworkPullChain_eq_roosUnit {U T : Scheme.{u}} (h : U ⟶ T)
    (p : OpenFactorCoherence.Pull l E h) (P : CochainComplex (integralTowerModules l E T) ℤ) :
    frameworkPullChain l E h P =
      IntegralOnSlice.roosUnit l E U none (frameworkPullComplex l E h P) ≫
        integralOperationsRoosFunctor.map (p.tower.hom.app P) := by
  let Q := frameworkPullComplex l E h P
  let C := (integralOperationsPullbackTowerFunctor l E h).obj P
  have hu : IntegralOnSlice.roosUnit l E U none Q ≫
      CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((IntegralOnSlice.tower l E U none).obj Q)) =
      IntegralOnSlice.productAugmentation l E U none Q :=
    IntegralAmbient.roosUnit_fst l E U Q
  have hfst (n : ℕ) : (IntegralOnSlice.roosUnit l E U none Q ≫
      integralOperationsRoosFunctor.map (p.tower.hom.app P)) ≫
      CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
        Pi.π (fun m ↦ C.obj (op m)) n =
      ((IntegralOnSlice.augmentation l E U none).app Q).app (op n) ≫
        (p.tower.hom.app P).app (op n) := by
    rw [Category.assoc, roosMap_fst_π]
    erw [reassoc_of% hu]
    rw [IntegralOnSlice.productAugmentation, Pi.lift_comp_π_assoc]
  refine (frameworkPullChain_existsUnique l E h P).unique (frameworkPullChain_spec l E h P)
    ⟨fun n i V x ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [hfst n]
    have ha := (IntegralOnSlice.augmentation_existsUnique l E U none).exists.choose_spec Q n i
      (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
        ((completed l E).pull h)).unit.app (P.X i)).val.app (op V) x)
    exact (congrArg (fun y ↦ (((p.tower.hom.app P).app (op n)).f i).val.app _ y) ha).trans
      (p.generators P n i V x)
  · obtain rfl : j = i - 1 := by omega
    rw [HomologicalComplex.comp_f, Category.assoc, integralOperationsRoosFunctor_map_snd,
      ← Category.assoc]
    erw [IntegralAmbient.roosUnit_snd l E U Q i (i - 1) (by omega)]
    exact zero_comp

private theorem exists_finiteFieldDatum_ne (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  exact ⟨D, by change l ≠ p; omega⟩

/-- On a flat-term K-flat representative of a constructible complex, the quotient-unit
comparison `frameworkPullChain` along an open immersion is a quasi-isomorphism. -/
theorem frameworkPullChain_quasiIso {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)]
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P)
    (hc : sfIntegralConstructible l E T (DerivedCategory.Q.obj P)) :
    QuasiIso (frameworkPullChain l E h P) := by
  classical
  obtain ⟨p⟩ := IntegralSystemRealization.integralRingedPullCompletion l E h
  let Q := frameworkPullComplex l E h P
  obtain ⟨D, hl⟩ := exists_finiteFieldDatum_ne l
  have hcomplete : IsDerivedCompleteUnrestricted l E T (DerivedCategory.Q.obj P) :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E T D hl _).mp hc.1⟩
  obtain ⟨sections, -⟩ := IntegralOpenReduction.normalizedOpenSections l E h
  obtain ⟨o, -, -⟩ := OpenSemilinearTensor.openCoefficientOperationsExistence l E h sections
  have hη := (OpenRestrictionCompleteness.openRestrictionComplete l E h o _ hcomplete).2
  obtain ⟨-, ⟨eP₀⟩⟩ := OpenFactorCoherence.openFactorOrdinaryTransport l E h o
  let F := frameworkModulePull l E h
  let := proEtaleRingModulePullback_additive h
    ((completed l E).ring T) ((completed l E).ring U) ((completed l E).pull h)
  let := proEtaleRingModulePullback_preservesFiniteLimits h
    ((completed l E).ring T) ((completed l E).ring U) ((completed l E).pull h)
  let := proEtaleRingModulePullback_preservesFiniteColimits h
    ((completed l E).ring T) ((completed l E).ring U) ((completed l E).pull h)
  let eP : IntegralOpenReduction.star l E h o ≅ F.mapDerivedCategory :=
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
      (Functor.additive_of_iso eP₀.symm) inferInstance
      (preservesFiniteLimits_of_natIso eP₀.symm)
      (preservesFiniteColimits_of_natIso eP₀.symm) inferInstance inferInstance eP₀
  have h₁ : IsIso ((IntegralOnSlice.completionUnit l E U none).app
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) :=
    (NatTrans.isIso_app_iff_of_iso _ (eP.app _)).mp hη
  have h₂ : IsIso ((IntegralOnSlice.completionUnit l E U none).app (DerivedCategory.Q.obj Q)) :=
    (NatTrans.isIso_app_iff_of_iso _ (F.mapDerivedCategoryFactors.app P)).mp h₁
  have hspec :=
    Classical.choose_spec (IntegralOnSlice.completionUnit_existsUnique l E U none).exists
    ⟨Q, p.good P hP⟩
  have h₃ : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E U none Q)) := by
    rw [← hspec]
    exact IsIso.comp_isIso' h₂ inferInstance
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, frameworkPullChain_eq_roosUnit l E h p P,
    Functor.map_comp]
  infer_instance

/-- Open inverse image preserves the completed constructible realization, with the
quotient-unit normalization: there is a unique natural isomorphism between the two pullbacks of
completed constructible complexes along `h` compatible with `frameworkPullChain` on good
representatives. -/
theorem frameworkOpenPullRealization_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃! a : (sfIntegralConstructible l E T).ι ⋙ pull (completed l E) h ≅
      constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E U).ι,
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (hP : sfIntegralConstructible l E T (DerivedCategory.Q.obj P.obj)),
        a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
          (integralDerivedPullbackComparison l E h).hom.app P =
        (frameworkModulePull l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (frameworkPullChain l E h P.obj) := by
  let L := integralOperationsGoodLocalization l E T
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E T).ι
  have : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E T
  have : L.EssSurj := Localization.essSurj L W
  let F : DerivedCategory (integralTowerModules l E T) ⥤
      DerivedCategory (integralTowerModules l E U) := pull (completed l E) h
  let G := integralDerivedPullback l E h
  let c := integralDerivedPullbackComparison l E h
  let m := (frameworkModulePull l E h).mapDerivedCategoryFactors
  let τ₀ : L ⋙ F ⟶ L ⋙ G :=
    { app := fun P ↦ m.hom.app P.obj ≫
        DerivedCategory.Q.map (frameworkPullChain l E h P.obj) ≫ c.inv.app P
      naturality := by
        intro P P' f
        have hm := m.hom.naturality f.hom
        have hc := c.inv.naturality f
        have hξ := congrArg DerivedCategory.Q.map (frameworkPullChain_naturality l E h f.hom)
        simp only [Functor.map_comp] at hξ
        simp only [Category.assoc]
        erw [reassoc_of% hm]
        exact congrArg (m.hom.app P.obj ≫ ·) (((reassoc_of% hξ) (c.inv.app P')).trans
          (congrArg (DerivedCategory.Q.map (frameworkPullChain l E h P.obj) ≫ ·) hc)) }
  let τ := Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G τ₀
  have hτ (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      τ.app (L.obj P) = τ₀.app P := by
    simp [τ, Localization.liftNatTrans_app]
  have hiso (K : (sfIntegralConstructible l E T).FullSubcategory) : IsIso (τ.app K.obj) := by
    let e := L.objObjPreimageIso K.obj
    have hP := (sfIntegralConstructible l E T).prop_of_iso e.symm K.property
    have hq := frameworkPullChain_quasiIso l E h (L.objPreimage K.obj).obj
      (L.objPreimage K.obj).property hP
    have : IsIso (τ.app (L.obj (L.objPreimage K.obj))) := by
      rw [hτ]
      dsimp [τ₀]
      infer_instance
    have hn := τ.naturality e.hom
    have : IsIso (F.map e.hom ≫ τ.app K.obj) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map e.hom) (τ.app K.obj)
  let α : (sfIntegralConstructible l E T).ι ⋙ F ⟶
      constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E U).ι :=
    Functor.whiskerLeft (sfIntegralConstructible l E T).ι τ
  have : IsIso α := by
    have (K : (sfIntegralConstructible l E T).FullSubcategory) : IsIso (α.app K) := hiso K
    exact NatIso.isIso_of_isIso_app α
  refine ⟨asIso α, fun P hP ↦ ?_, fun a ha ↦ ?_⟩
  · change τ.app (L.obj P) ≫ _ = _
    rw [hτ]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
      NatIso.cancel_natIso_hom_left, m, c, τ₀]
    exact Category.comp_id _
  · apply Iso.ext
    ext K
    let e := L.objObjPreimageIso K.obj
    let P := L.objPreimage K.obj
    have hP := (sfIntegralConstructible l E T).prop_of_iso e.symm K.property
    let e' : (⟨L.obj P, hP⟩ : (sfIntegralConstructible l E T).FullSubcategory) ≅ K :=
      (sfIntegralConstructible l E T).fullyFaithfulι.preimageIso e
    have h₀ : a.hom.app ⟨L.obj P, hP⟩ = α.app ⟨L.obj P, hP⟩ := by
      rw [← cancel_mono (c.hom.app P)]
      refine (ha P hP).trans ?_
      change _ = τ.app (L.obj P) ≫ _
      rw [hτ]
      simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
        NatIso.cancel_natIso_hom_left, m, c, τ₀]
      exact (Category.comp_id _).symm
    have hna := a.hom.naturality e'.hom
    have hnα := α.naturality e'.hom
    rw [← cancel_epi (((sfIntegralConstructible l E T).ι ⋙ F).map e'.hom), hna, h₀]
    exact hnα.symm

/-- The framework pullback realization fixed by quotient and shifted Roos coordinates. -/
def frameworkOpenPullRealization {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :=
  (frameworkOpenPullRealization_existsUnique l E h).exists.choose

end WeilConjectures.ZlFrameworkPbc
