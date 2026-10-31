/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

import WeilConjectures.AlgebraicGeometry.Proper.ProperExceptionalOpenBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Open restriction of the higher direct image

Source: the proof plan of `isZero_higherDirectImage_open_injective_of_proper`
in `WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclic`.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-open-restriction)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- Vanishing on the open part of the base open-closed decomposition.

Source: the recorded compactification-independence proof plan in
`WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclic`, steps
1--3. Stacks Tag 0F7B is its etale analogue only.

Proof: Use the actual pullback V = B ×_D E. The induced map t : C → V is
open and proper, hence closed; extension by zero along t is therefore direct
image and sends J to an injective object. Restrict k_!J to V: the open unit and
composition of open extensions identify it with t_!J. Derived open restriction
identifies i^*Rp_*(k_!J[0]) with Rs_*(t_!J[0]). A single injective complex
computes this right derived functor, so its positive homology is zero. Exactness
of i^* lets it commute with homology, proving the displayed vanishing.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-open-restriction)
-/
theorem isZero_openRestriction_higherDirectImage_open_injective_of_proper
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    IsZero ((proEtaleConstantRingPullback A i).obj
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules D (proEtaleConstantRing D A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
            ((sfIntrinsicExtensionByZero k A).obj J))))) := by
  let V := pullback p i
  let b : V ⟶ B := pullback.fst p i
  let s : V ⟶ E := pullback.snd p i
  let t : C ⟶ V := pullback.lift k r hcomm
  have ht : t ≫ b = k := pullback.lift_fst _ _ _
  have hts : t ≫ s = r := pullback.lift_snd _ _ _
  have : IsOpenImmersion b := inferInstance
  have : IsOpenImmersion (t ≫ b) := ht.symm ▸ inferInstance
  have : IsOpenImmersion t := IsOpenImmersion.of_comp t b
  have : IsProper s := inferInstance
  have : IsProper (t ≫ s) := hts.symm ▸ inferInstance
  have : IsProper t := IsProper.of_comp t s
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let J₀ := (sfIntrinsicModuleEquivalence C A).inverse.obj J
  have : Injective J₀ := inferInstance
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range Λ t
    t.isClosedMap.isClosed_range
  have : (ProEtale.lowerStar Λ t).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.upperStarLowerStarAdjunction Λ t)
  have hJ₀ : Injective ((ProEtale.openImmersionLowerShriek Λ t).obj J₀) :=
    Injective.of_iso
      (asIso ((ProEtale.openImmersionLowerShriekToLowerStar Λ t).app J₀)).symm
      inferInstance
  let Jv := (sfIntrinsicExtensionByZero t A).obj J
  have : Injective Jv :=
    (sfIntrinsicModuleEquivalence V A).functor.injective_obj_of_injective hJ₀
  let F := (sfIntrinsicExtensionByZero k A).obj J
  have eF : (sfIntrinsicPullback A b).obj F ≅ Jv := by
    have e : F ≅ (sfIntrinsicExtensionByZero b A).obj Jv := by
      simpa only [ht, Functor.comp_obj] using (sfIntrinsicOpenComp A t b).app J
    have : (sfIntrinsicExtensionByZero b A).Full := by
      unfold sfIntrinsicExtensionByZero
      infer_instance
    have : (sfIntrinsicExtensionByZero b A).Faithful := by
      unfold sfIntrinsicExtensionByZero
      infer_instance
    exact (sfIntrinsicPullback A b).mapIso e ≪≫
      (asIso ((sfIntrinsicOpenAdjunction A b).unit.app Jv)).symm
  let M := (proEtaleConstantDerivedDirectImage p A).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  let eD : (sfIntrinsicDerivedPullback A i).obj M ≅
      (proEtaleConstantDerivedDirectImage s A).obj
        ((DerivedCategory.singleFunctor _ 0).obj Jv) :=
    (sfProperOpenDerivedRestriction A s b i p (IsPullback.of_hasPullback p i).flip).app
        ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
      (proEtaleConstantDerivedDirectImage s A).mapIso
        (((sfIntrinsicPullback A b).mapDerivedCategorySingleFunctor 0).app F ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso eF)
  let : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules V (proEtaleConstantRing V A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
       (ProEt.topology V) (proEtaleConstantRing V A)).1
  have hz : IsZero ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
      ((proEtaleConstantDerivedDirectImage s A).obj
        ((DerivedCategory.singleFunctor _ 0).obj Jv))) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact (Functor.isZero_rightDerived_obj_injective_succ
      (proEtaleConstantModuleDirectImage s A) n Jv).of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (proEtaleConstantModuleDirectImage s A) Jv (n + 1))
  exact hz.of_iso
    ((openSquarePullbackModel A i).app _ ≪≫
      ((sfIntrinsicPullback A i).mapDerivedCategoryHomologyFunctorIso (q : ℤ)).app M ≪≫
      (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso eD)

end AlgebraicGeometry.Scheme
