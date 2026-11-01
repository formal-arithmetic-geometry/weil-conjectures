/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
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
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerOrdinaryPullback
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerDerivedPullback
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients

/-! # Unique normalized scalar/pullback comparison -/

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

private theorem geometric_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules l E Y) (N : spIntegralSectionModules l E X)
    (a b : (spIntegralModuleEquivalence l E X).functor.obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) : a = b := by
  classical
  let F := (spIntegralModuleEquivalence l E X).functor
  let N' := F.objPreimage N
  let e := F.objObjPreimageIso N
  let a' := F.preimage (a ≫ e.inv)
  let b' := F.preimage (b ≫ e.inv)
  have ha : F.map a' = a ≫ e.inv := F.map_preimage _
  have hb : F.map b' = b ≫ e.inv := F.map_preimage _
  have he : a' = b' := by
    apply ((CondensedRing.upperStarLowerStarAdjunction
      (spIntegralCondensed l E) f).homEquiv M N').injective
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have haV := congrArg (fun z ↦ z.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app V x)) ha
    have hbV := congrArg (fun z ↦ z.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app V x)) hb
    change a'.hom.hom.app _ _ = b'.hom.hom.app _ _
    exact haV.trans ((congrArg (e.inv.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))) (h V.unop x)).trans hbV.symm)
  apply (cancel_mono e.inv).mp
  exact ha.symm.trans ((congrArg F.map he).trans hb)

private theorem scalar_geometric_hom_ext (s : Presentation l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y) (n : ℕ)
    (N : Scheme.proEtaleRingModules X (SpTowerShriek.B l E X n))
    (a b : (ordinaryLevel l E s X n).obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x))) : a = b := by
  let A := (s.towers X).scalar
    (spIntegralReductionScalar l E X (s.reduction X).coefficient n)
  apply (A.ordinaryAdj.homEquiv _ N).injective
  apply geometric_hom_ext l E f M
  intro V x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _) =
    b.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _)
  rw [A.unit_normalized]
  exact h V x

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
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

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
