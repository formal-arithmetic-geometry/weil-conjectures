/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.CochainComplexOpposite
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopyColimit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import all WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation.TowerRightDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.RingedSiteGlobalRHom.RingedSiteGlobalRHomModel
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# O-module valued simultaneous sections and mapping systems

Source: Stacks Project, Tags 0B6E, 08J7 and 08J9; the coherent Hom construction
in sentence 2 of the current blueprint proof
`blueprint/part-six-operations/sec-coefficients-constructible/sec-n-brown/sk-thm-existence/`
`lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.proof.md`.
(blueprint: def-sfb-derived-system-mapping-hom).

Restriction is sectionwise restriction along the coefficient algebra. Currying
the sequence-site presheaf and taking its vertical limits gives the actual
ordinary tower of O-module sections. Its total right derived functor, applied
to the published closed internal Hom, defines the mapping system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option linter.checkUnivs false
set_option linter.style.haveILetI false

universe c v r k

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C) [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The coefficient algebra on the sequence site. Source: Stacks 03D7 and 0B6E
(blueprint: def-sfb-derived-system-mapping-hom). -/
abbrev SystemAlgebra (O : Type r) [CommRing O] :=
  O →+* RingedSiteGlobalRHom.Scalars (systemRing J B τ)

/-- Evaluation of a compatible coefficient scalar at a sequence-site object.
Source: Stacks 03D7 (blueprint: def-sfb-derived-system-mapping-hom). -/
def algebraAt (O : Type r) [CommRing O] (α : SystemAlgebra J B τ O)
    (U : (ℕ × C)ᵒᵖ) : O →+* (systemRing J B τ).obj.obj U where
  toFun a := (α a).val U
  map_one' := by change (α 1).val U = 1; rw [map_one]; rfl
  map_mul' a b := by change (α (a * b)).val U = _; rw [map_mul]; rfl
  map_zero' := by change (α 0).val U = 0; rw [map_zero]; rfl
  map_add' a b := by change (α (a + b)).val U = _; rw [map_add]; rfl

/-- Restriction to O on all sections, retaining both horizontal and vertical maps.
Source: Stacks 03D7 (blueprint: def-sfb-derived-system-mapping-hom). -/
def systemRestrictionObj (O : Type r) [CommRing O] (α : SystemAlgebra J B τ O)
    (M : Systems.{c, v, max c v r} J B τ) :
    (ℕ × C)ᵒᵖ ⥤ ModuleCat.{max c v r} O where
  obj U := (ModuleCat.restrictScalars (algebraAt J B τ O α U)).obj (M.val.obj U)
  map {U V} f := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraAt J B τ O α U)).obj (M.val.obj U))
    (Y := (ModuleCat.restrictScalars (algebraAt J B τ O α V)).obj (M.val.obj V))
    { toFun := M.val.map f
      map_add' := map_add _
      map_smul' := fun a x ↦ by
        change M.val.map f ((α a).val U • x) = (α a).val V • M.val.map f x
        rw [M.val.map_smul]
        exact congrArg (fun s ↦ s • M.val.map f x) ((α a).property f) }
  map_id U := by
    ext x
    change M.val.map (𝟙 U) x = x
    rw [M.val.map_id]
    rfl
  map_comp f g := by
    ext x
    exact M.val.map_comp_apply f g x

/-- The abelian category of genuine inverse towers of O-modules.
Source: Stacks 0941 (blueprint: def-sfb-derived-system-mapping-hom). -/
abbrev ScalarTowers (O : Type r) [CommRing O] := ℕᵒᵖ ⥤ ModuleCat.{max c v r} O

/-- D(Tow(O-Mod)), with the localization universe matching the system category.
Source: Stacks 05RU (blueprint: def-sfb-derived-system-mapping-hom). -/
abbrev DScalarTowers (O : Type r) [CommRing O] :=
  DerivedCategory (ScalarTowers.{c, v, r} O)

set_option maxHeartbeats 1000000 in
-- Natural-isomorphism assembly unfolds large module-sheaf limits.
set_option maxHeartbeats 1600000 in
-- Resolving adjunctions and localized unit cancellations expand substantial category data.
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 1600000 in
-- Comparing concrete and localized tensor structures expands substantial derived-category data.
section MappingSectionsProof

set_option maxHeartbeats 800000 in
-- Comparing the independently sized derived-section carriers requires extra reduction.
set_option maxHeartbeats 1200000 in
-- The representative comparison retains the full independent-universe instances.
set_option maxHeartbeats 1200000 in
-- The representative comparison retains the full independent-universe instances.
end MappingSectionsProof

end WeilConjectures.SemilinearSections
