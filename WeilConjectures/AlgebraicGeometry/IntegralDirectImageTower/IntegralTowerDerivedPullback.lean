/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullbackNormalizations
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.NormalizedDerivedComparisonDescent
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Normalized IntegralTowerDerivedPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem kflat_iso {T : Scheme.{u}}
    {P Q : CochainComplex (spIntegralSectionModules l E T) ℤ}
    (e : P ≅ Q) (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := spIntegralSectionRing l E T) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) Q := by
  let := isMonoidal_W_independentCoefficients (spIntegralSectionRing l E T)
  let := monoidalCategory (spIntegralSectionRing l E T)
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients
    (spIntegralSectionRing l E T)
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (spIntegralSectionRing l E T)
  intro F hF
  let e' := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e
  have hh := hP F hF
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hh ⊢
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient _ _).mapIso e') hh

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem flat_iso {T : Scheme.{u}} {M N : spIntegralSectionModules l E T}
    (e : M ≅ N) (hM : IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) M) :
    IsFlatOnSite (J := Scheme.ProEt.topology T) (R := spIntegralSectionRing l E T) N := by
  let := isMonoidal_W_independentCoefficients (spIntegralSectionRing l E T)
  let := monoidalCategory (spIntegralSectionRing l E T)
  have hM' := (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (spIntegralSectionRing l E T) M) hM
  have hN := (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.tensoringRight (spIntegralSectionModules l E T)).mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (spIntegralSectionRing l E T) N).symm hN

private theorem internal_resolving_ext {T : Scheme.{u}}
    {D : Type*} [Category D] (F G : Integral l E T ⥤ D) (a b : F ⟶ G)
    (h : ∀ (P : CochainComplex (Modules l E T) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
      (∀ i : ℤ, IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := spIntegralSectionRing l E T)
        ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))) →
      a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
  let eqv := spIntegralModuleEquivalence l E T
  let : eqv.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : eqv.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ec := eqv.mapHomologicalComplex (.up ℤ)
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules l E T) (.up ℤ))
  intro K
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := spIntegralSectionRing l E T) (ec.functor.obj K)
  let L := ec.inverse.obj P
  let q : L ⟶ K := ec.inverse.map p ≫ ec.unitIso.inv.app K
  have hp' : QuasiIso (ec.inverse.map p) := by
    have := hp
    change QuasiIso ((eqv.inverse.mapHomologicalComplex (.up ℤ)).map p)
    infer_instance
  have : QuasiIso q := by
    dsimp only [q]
    infer_instance
  have hL : CochainComplex.IsKFlatIndependentCoefficients
      (R := spIntegralSectionRing l E T) (ec.functor.obj L) :=
    kflat_iso l E (ec.counitIso.symm.app P) hP
  have hLf (i : ℤ) : IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) (eqv.functor.obj (L.X i)) := by
    apply flat_iso l E ((HomologicalComplex.eval _ _ i).mapIso
      (ec.counitIso.symm.app P))
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso (spIntegralSectionRing l E T) (P.X i)).symm (hf i)
  apply (cancel_epi (F.map (DerivedCategory.Q.map q))).1
  rw [a.naturality, b.naturality]
  rw [h L hL hLf]

/-- Component form of the normalized pullback composition identity.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
(blueprint: lem-dla1-native-reduction-proper-composition-component).
Proof: first use `Localization.natTrans_ext` to reduce equality of the two natural
transformations to complexes in the internal module category. Pass such a complex to
the section-module category through `spIntegralModuleEquivalence`, and apply
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`
(blueprint node `lem-pc-kflat-resolution`). Carry its flat-term K-flat replacement and
quasi-isomorphism back through the equivalence. K-flatness and termwise flatness are
invariant under the counit isomorphism, so the hypothesis applies to this replacement.
Its augmentation becomes an isomorphism in the derived category. Naturality of both
transformations, followed by cancellation of the image of this isomorphism, gives their
equality on the original complex. Localization then gives equality on all derived
objects, and evaluation gives the requested component.
-/
theorem nativeReductionPullbackComposition_component (s : Presentation l E)
    (q : ReductionGeometry l E s)
    (hrep : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (P : CochainComplex (Modules l E Z) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := spIntegralSectionRing l E Z)
        (((spIntegralModuleEquivalence l E Z).functor.mapHomologicalComplex (.up ℤ)).obj P) →
      (∀ i : ℤ, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology Z)
        (R := spIntegralSectionRing l E Z)
        ((spIntegralModuleEquivalence l E Z).functor.obj (P.X i))) →
      (((((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
          (s.operations.comp f g).inv).whiskerLeft
            (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv).natTrans.app
              (DerivedCategory.Q.obj P)) =
        ((TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv).natTrans.app
          (DerivedCategory.Q.obj P))) :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : Integral l E Z),
      (((((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
          (s.operations.comp f g).inv).whiskerLeft
            (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv).natTrans.app
              K) = ((TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv).natTrans.app K) := by
  intro X Y Z f g K
  have h := internal_resolving_ext l E _ _
    (((((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
      (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
        (s.operations.comp f g).inv).whiskerLeft
          (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv).natTrans)
    ((TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv).natTrans)
    (hrep f g)
  exact congrArg (fun t ↦ t.app K) h

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private def reductionCounit (s : Presentation l E) (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ derivedReduction l E s T ⟶
      (ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let := (s.towers T).hasDerived
  let E₀ := (spIntegralModuleEquivalence l E T).functor
  let V := (s.base.realization T).functor
  let R := (s.reduction T).red
  let a := Functor.whiskerRight
    (Functor.whiskerRight E₀.mapDerivedCategoryFactors.hom R) (realization l E s T).functor
  let b := Functor.whiskerRight
    (Functor.whiskerLeft (E₀.mapHomologicalComplex (.up ℤ)) (s.reduction T).counit)
    (realization l E s T).functor
  let c := Functor.whiskerLeft
    ((E₀ ⋙ (s.reduction T).ordinary).mapHomologicalComplex (.up ℤ))
    V.mapDerivedCategoryFactors.hom
  exact a ≫ b ≫ c

private theorem reductionCounit_app (s : Presentation l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ) :
    (reductionCounit l E s T).app P = reductionComplexComparison l E s T P := by
  simp only [reductionCounit, reductionComplexComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem reduction_comparison_isIso (s : Presentation l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
      (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (reductionComplexComparison l E s T P) := by
  let := (s.towers T).hasDerived
  let := s.base.realizationAdditive T
  have := (s.reduction T).computes _ hP
  unfold reductionComplexComparison
  infer_instance

private theorem internal_kflat_iff (T : Scheme.{u}) (P : CochainComplex (Modules l E T) ℤ) :
    (HomologicalComplex.quasiIso (Modules l E T) (.up ℤ)).kFlat P ↔
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨_, e, e₀, _, _, _, _, _, _, _, _, _, _, hk⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology T) (condensedRingObj (spIntegralCondensed l E) T)
  rw [← hk P, ← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h A hA
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic A).2 hA)).2
  · intro h A hA
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hA
    have ht := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      (h A hA)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (β_ _ _) ht, ht⟩

private theorem pullback_kflat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E Y)
      (((spIntegralModuleEquivalence l E Y).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E X)
      (((spIntegralModuleEquivalence l E X).functor.mapHomologicalComplex (.up ℤ)).obj
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P)) := by
  apply (internal_kflat_iff l E X _).1
  exact CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
    (spIntegralCondensed l E) f ((internal_kflat_iff l E Y P).2 hP)

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private def good (T : Scheme.{u}) : ObjectProperty (CochainComplex (Modules l E T) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
    (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T)
      ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- The descent comparison elaborates the internal and section presentations together.
set_option synthInstance.maxHeartbeats 200000 in
end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
