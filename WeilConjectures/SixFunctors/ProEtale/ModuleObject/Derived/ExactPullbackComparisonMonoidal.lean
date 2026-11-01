/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-! # Monoidality of the canonical exact pullback comparison

Source: latest blueprint, sec-six-functors/sk-thm-sf-identification/def-sf-cup.md,
final associativity and unit sentence, via the open factor of the compactification
projection; Stacks Tags 015F (dual) and 03EL
(blueprint: lem-sf-exact-pullback-comparison-monoidal).

The derived categories are unbounded categories of internal modules over the pulled-back
commutative condensed ring. All tensor products are the existing relative derived tensors.

## Main definitions and statements

* `supportPullbackExactComparison`: the canonical exact comparison followed by the
  localized inverse-coefficient identification.
* `supportPullbackDerivedUnitIso`: exact factorization followed by the ordinary unit
  comparison in degree zero.
* `exact_pullback_comparison_monoidal`: tensor and unit compatibility, and the resulting
  strong monoidal structure with the specified tensorator and unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical exact comparison with inverse-coefficient termwise pullback. The second
factor localizes the inverse of the recorded identification `supportPullback ≅ upperStar`.
Source: Stacks Tag 015F (dual), and Tag 03EL for coefficient transport
(blueprint: lem-sf-exact-pullback-comparison-monoidal). -/
def supportPullbackExactComparison :
    moduleObjectDerivedPullback Λ f ≅ (supportPullback Λ f).mapDerivedCategory :=
  modulePullbackExactComparison Λ f ≪≫
    (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f)).symm

/-- The specified unit isomorphism of exact termwise pullback: the exact factorization
on the degree-zero unit complex, followed by localization of the ordinary unit map.
The ordinary map uses the canonical inverse-coefficient identification with upper star
and its published unit comparison. No derived monoidal structure is selected here.
Source: Stacks Tag 03EL and the exact-functor clause of the latest blueprint
`det-def-sfb-derived-categories.md`
(blueprint: lem-sf-exact-pullback-comparison-monoidal). -/
def supportPullbackDerivedUnitIso :
    (supportPullback Λ f).mapDerivedCategory.obj
      (𝟙_ (DerivedCategory (supportModules Λ Y))) ≅
        𝟙_ (DerivedCategory (supportModules Λ X)) :=
  (supportPullback Λ f).mapDerivedCategoryFactors.app (𝟙_ _) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (supportPullback Λ f)
          (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
        (HomologicalComplex.single _ _ 0).mapIso
          ((supportPullbackIsoUpperStar Λ f).app (𝟙_ _) ≪≫
            (Functor.Monoidal.εIso (upperStar Λ f)).symm))

set_option maxHeartbeats 1600000 in
-- The unit calculation compares the native complex, homotopy and derived localizations.
/-- The canonical exact comparison respects the specified derived tensor and unit maps.
The inverse comparison family and inverse unit give a strong monoidal structure on the
termwise derived functor, and the canonical comparison is a monoidal natural isomorphism.
No boundedness, flatness or finiteness assumption is made.
Source: latest blueprint `def-sf-cup.md`, final associativity and unit sentence,
via Step 2 of `lem-sf-compact-projection-right-tensor-action`; Stacks Tags 015F and 03EL
(blueprint: lem-sf-exact-pullback-comparison-monoidal).

Proof:
1. By the universal left-derived property (`def-sfb-left-derived-functor`) and exact
factorization (`lem-weil-pbc-exact-functor-derived-factorization`), the specified exact
comparison is the unique counit-compatible isomorphism
(`lem-sfb-right-kan-extension-unique-iso`, `def-sfb-left-derived-exact`). Thus fac c = gamma.
2. The coefficient identification is monoidal: the ordinary structure is transported from
inverse-coefficient restriction (`new-integral-residue-ordinary-monoidal`), whose balanced
presentation determines the ordinary comparison in
`def-sfb-condensed-pullback-tensor-comparison`. The localization universal property
(`lem-weil-pbc-localization-universal-property`) makes its localization compatible with the
exact factorizations, so fac c = gamma still holds after this identification.
3. The summand normalization of `lem-sfb-termwise-strong-monoidal` identifies the ordinary
complex comparison with the inverse total tensorator. Pass to homotopy classes using
`lem-sfb-total-tensor-homotopy`. The two-counit equation of
`new-proetale-derived-module-pullback-monoidal`, postcomposed with that inverse, reads
mu (gamma tensor gamma) delta = Q(d) gamma E(mu).
4. Conjugate delta by c. Using fac c = gamma and naturality of c for mu, the conjugate
satisfies precisely the representative normalization of
`def-sfb-condensed-pullback-tensor-comparison`. Its uniqueness identifies it with the
specified derived comparison. Rearrangement gives the tensor equation on every pair.
5. The derived unit of `lem-sfb-derived-pullback-strong-monoidal` is Q(j) gamma on the
unit complex, while the specified termwise unit is Q(j) fac. The counit equation therefore
gives unit compatibility, with the actual degree-zero ordinary unit j.
6. Substitute the tensor and unit equations into the associativity and two unit laws
of `lem-sfb-derived-pullback-strong-monoidal`. Naturality of c, associators and unitors
cancels the inverse c pairs. This yields `def-sfb-strong-monoidal-functor` for the
prescribed inverse comparisons. The same equations give monoidality of c. All arguments
use arbitrary complexes and arbitrary scheme morphisms and condensed coefficients. -/
theorem exact_pullback_comparison_monoidal :
    (∀ M N : DerivedCategory (supportModules Λ Y),
      (supportPullbackExactComparison Λ f).hom.app (M ⊗ N) ≫
          (supportDerivedTensorComparison Λ f M N).hom =
        (((leftDerivedUpperStarTensorIso Λ f).app M).app N).hom ≫
          ((supportPullbackExactComparison Λ f).hom.app M ⊗ₘ
            (supportPullbackExactComparison Λ f).hom.app N)) ∧
    ((supportPullbackExactComparison Λ f).hom.app
        (𝟙_ (DerivedCategory (supportModules Λ Y))) ≫
      (supportPullbackDerivedUnitIso Λ f).hom = (leftDerivedUpperStarUnitIso Λ f).hom) ∧
    ∃ m : (supportPullback Λ f).mapDerivedCategory.CoreMonoidal,
      (∀ M N : DerivedCategory (supportModules Λ Y),
        m.μIso M N = (supportDerivedTensorComparison Λ f M N).symm) ∧
      m.εIso = (supportPullbackDerivedUnitIso Λ f).symm ∧
      @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
        (supportPullbackExactComparison Λ f).hom
        (monoidal_leftDerivedUpperStar Λ f).toLaxMonoidal m.toLaxMonoidal := by
  let := supportPullbackMonoidal Λ f
  let := supportPullbackIsLeftAdjoint Λ f
  let := supportPullback_preservesFlat Λ f
  have he : NatTrans.IsMonoidal (supportPullbackIsoUpperStar Λ f).hom := by
    let a := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
    let ha : NatTrans.IsMonoidal a.inv :=
      Functor.Monoidal.natTransIsMonoidal_of_transport a.symm
    change NatTrans.IsMonoidal (Functor.whiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)) a.inv)
    exact NatTrans.IsMonoidal.whiskerLeft
      (F₁ := (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)) a.inv
  let := he
  let : NatTrans.IsMonoidal (supportPullbackIsoUpperStar Λ f).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (supportPullbackIsoUpperStar Λ f).inv)
  have ht : supportDerivedTensorComparison Λ f =
      exactDerivedTensorCandidate (supportPullback Λ f) := by
    apply exactDerivedTensorCandidate_unique
    · intro K K' M M' a b
      have h := (Classical.choose_spec (ExistsUnique.exists
        (existsUnique_supportDerivedTensorComparison Λ f))).1 K K' M M' a b
      simpa only [supportDerivedTensorComparison, curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, Functor.comp_obj, MonoidalCategory.tensorHom_def,
        Category.assoc] using h
    · intro A B
      have h := (Classical.choose_spec (ExistsUnique.exists
        (existsUnique_supportDerivedTensorComparison Λ f))).2 A B
      simpa only [supportDerivedTensorComparison, supportComplexTensorComparison_eq_δ,
        curriedTensor_map_app,
        curriedTensor_obj_map, curriedTensor_obj_obj, Functor.comp_obj,
        MonoidalCategory.tensorHom_def, Category.assoc] using h.symm
  have hTensor (M N : DerivedCategory (supportModules Λ Y)) :
      (supportPullbackExactComparison Λ f).hom.app (M ⊗ N) ≫
          (supportDerivedTensorComparison Λ f M N).hom =
        (((leftDerivedUpperStarTensorIso Λ f).app M).app N).hom ≫
          ((supportPullbackExactComparison Λ f).hom.app M ⊗ₘ
            (supportPullbackExactComparison Λ f).hom.app N) := by
    rw [ht]
    have hn := Functor.leftDerivedTensorComparison_naturality_app
      (supportPullbackIsoUpperStar Λ f).symm M N
    simp only [Functor.leftDerivedFunctorNatIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app] at hn
    have hh := congrArg (fun z ↦ z ≫
      (((supportPullback Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.app M) ⊗ₘ
        ((supportPullback Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.app N))) hn
    simpa only [exactDerivedTensorCandidate, supportPullbackExactComparison,
      modulePullbackExactComparison, Functor.leftDerivedExactComparison,
      Functor.leftDerivedFunctorIsoMapDerivedCategory, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, tensorIso_hom,
      NatTrans.comp_app, Category.assoc,
      tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Category.comp_id,
      Iso.inv_hom_id_app_assoc, leftDerivedUpperStarTensorIso, asIso_hom,
      leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison] using hh
  have hUnit :
      (supportPullbackExactComparison Λ f).hom.app (𝟙_ _) ≫
        (supportPullbackDerivedUnitIso Λ f).hom =
          (leftDerivedUpperStarUnitIso Λ f).hom := by
    have hn := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor
      (supportPullbackIsoUpperStar Λ f).symm (𝟙_ _)
    rw [Functor.mapDerivedCategoryNatIso_symm] at hn
    have hh := congrArg (fun z ↦ z ≫
      (DerivedCategory.singleFunctor (supportModules Λ X) 0).map
        ((supportPullbackIsoUpperStar Λ f).hom.app (𝟙_ _) ≫
          (Functor.Monoidal.εIso (upperStar Λ f)).inv)) hn
    simp only [Category.assoc, ← Functor.map_comp, Iso.symm_hom,
      Iso.inv_hom_id_app_assoc] at hh
    have hfac := modulePullbackResolutionCounit_eq Λ f
      ((HomologicalComplex.single (supportModules Λ Y) (.up ℤ) 0).obj (𝟙_ _))
    dsimp only [modulePullbackComplexComparison, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
    have hNative :
        (modulePullbackExactComparison Λ f).hom.app (𝟙_ _) ≫
          ((upperStar Λ f).mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
            (DerivedCategory.singleFunctor (supportModules Λ X) 0).map
              (Functor.Monoidal.εIso (upperStar Λ f)).inv =
                (leftDerivedUpperStarUnitIso Λ f).hom := by
      rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
      simp only [Category.assoc]
      erw [← reassoc_of% hfac]
      simp only [modulePullbackResolutionCounit, leftDerivedUpperStarUnitIso,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
        Functor.map_comp]
      dsimp only [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
        NatIso.ofComponents, Iso.refl]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      simp only [Category.assoc]
      rfl
    calc
      _ = (modulePullbackExactComparison Λ f).hom.app (𝟙_ _) ≫
          ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f)).inv.app
              ((DerivedCategory.singleFunctor (supportModules Λ Y) 0).obj (𝟙_ _)) ≫
            ((supportPullback Λ f).mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
              (DerivedCategory.singleFunctor (supportModules Λ X) 0).map
                ((supportPullbackIsoUpperStar Λ f).hom.app (𝟙_ _) ≫
                  (Functor.Monoidal.εIso (upperStar Λ f)).inv)) := by
        simp only [supportPullbackExactComparison, supportPullbackDerivedUnitIso,
          Functor.mapDerivedCategorySingleFunctor_hom_app_eq,
          Functor.mapCochainComplexSingleFunctor, Iso.trans_hom, Iso.app_hom,
          Iso.symm_hom, NatTrans.comp_app, Functor.mapIso_hom, Functor.map_comp,
          Category.assoc]
        rfl
      _ = _ := (congrArg ((modulePullbackExactComparison Λ f).hom.app (𝟙_ _) ≫ ·) hh).trans
        hNative
  let : (moduleObjectDerivedPullback Λ f).Monoidal := monoidal_leftDerivedUpperStar Λ f
  refine ⟨hTensor, hUnit,
    Functor.Monoidal.coreMonoidalTransport (supportPullbackExactComparison Λ f), ?_, ?_, ?_⟩
  · intro M N
    apply Iso.ext_inv
    dsimp only [Functor.Monoidal.coreMonoidalTransport, Iso.trans_inv,
      tensorIso_inv, Iso.app_inv, Iso.symm_inv]
    simp only [Category.assoc]
    change (supportPullbackExactComparison Λ f).inv.app (M ⊗ N) ≫
        (((leftDerivedUpperStarTensorIso Λ f).app M).app N).hom ≫
          ((supportPullbackExactComparison Λ f).hom.app M ⊗ₘ
            (supportPullbackExactComparison Λ f).hom.app N) = _
    rw [← hTensor, Iso.inv_hom_id_app_assoc]
  · apply Iso.ext_inv
    change (supportPullbackExactComparison Λ f).inv.app (𝟙_ _) ≫
      (leftDerivedUpperStarUnitIso Λ f).hom = _
    rw [← hUnit, Iso.inv_hom_id_app_assoc]
    rfl
  · exact Functor.Monoidal.natTransIsMonoidal_of_transport
      (supportPullbackExactComparison Λ f)

end AlgebraicGeometry.ProEtale.CondensedRing
