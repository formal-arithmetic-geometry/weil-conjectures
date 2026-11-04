/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit

/-! # Forgetting scalars and derived restriction kernels

Source: Stacks Project, sites-cohomology.tex, Tags 093X and 03FD; injectives.tex,
Tag 01DU; derived.tex, Tags 013K, 070J, 070I, 05TI and 05TH; homology.tex, Tags 0117
and 05QB (blueprint: lem-pur-module-restriction-kernel-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w uB vB uD vD
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ModuleRestrictionKernel

open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation

/-- The actual kernel of module restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [Ring A] [HasWeakSheafify J RingCat.{u}]
    {W T : C} (m : W ⟶ T) : ConstantLeftModuleInverseImage.Modules J A ⥤ ModuleCat.{u} A := by
  let r := LeftModuleDerivedEvaluation.restriction J A m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G J A T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

/-- The actual kernel of abelian restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S₀
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {W T : C} (m : W ⟶ T) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} := by
  let r := LeftModuleDerivedEvaluation.restriction₀ J m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G₀ J T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] [HasWeakSheafify J RingCat.{u}]
  {W T : C} (m : W ⟶ T)

omit [HasWeakSheafify J RingCat.{u}] in
/-- The canonical scalar-forgetting kernel isomorphism on each object.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentityObj (M : Modules J A) :
    (v A).obj ((S J A m).obj M) ≅ (S₀ J m).obj ((V J A).obj M) :=
  PreservesKernel.iso (v A) ((restriction J A m).app M)

/-- Naturality of the kernel-preservation comparison.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: compose both maps with the monic target kernel inclusion. Both composites
are the underlying section map followed by the source inclusion; kernel
uniqueness gives the equation. -/
theorem kernelIdentity_naturality {M N : Modules J A} (f : M ⟶ N) :
    (S J A m ⋙ v A).map f ≫ (kernelIdentityObj J A m N).hom =
      (kernelIdentityObj J A m M).hom ≫ (V J A ⋙ S₀ J m).map f := by
  apply (cancel_mono (kernel.ι ((v A).map ((restriction J A m).app N)))).1
  dsimp only [Functor.comp_map, kernelIdentityObj]
  simp only [PreservesKernel.iso_hom, Category.assoc, kernelComparison_comp_ι]
  change (v A).map (kernel.lift _ _ _) ≫ _ =
    kernelComparison _ (v A) ≫ kernel.lift _ _ _ ≫ _
  erw [kernel.lift_ι, ← Functor.map_comp, kernel.lift_ι]
  erw [← Category.assoc, kernelComparison_comp_ι]
  rfl

/-- The underived identity, expressed by canonical kernel preservation rather than
an equality between chosen categorical limit objects.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentity : S J A m ⋙ v A ≅ V J A ⋙ S₀ J m :=
  NatIso.ofComponents (kernelIdentityObj J A m) (kernelIdentity_naturality J A m)

/-- The restriction-kernel functor on modules is additive.
Source: Stacks, 093X (blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance sAdditive : (S J A m).Additive where
  map_add {M N f g} := by
    apply (cancel_mono (kernel.ι _)).1
    simp [S]

/-- The restriction-kernel functor on abelian sheaves is additive.
Source: Stacks, 093X (blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance s₀Additive : (S₀ J m).Additive where
  map_add {M N f g} := by
    apply (cancel_mono (kernel.ι _)).1
    simp [S₀]

private def inclusion : S₀ J m ⟶ G₀ J T where
  app M := kernel.ι ((restriction₀ J m).app M)
  naturality _ _ _ := kernel.lift_ι _ _ _

variable [HasDerivedCategory.{w} (Modules J A)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J A)] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]

/-- The canonical derived comparison induced by the identity on restriction kernels.
Source: Stacks, 03FD/05TI/05TH, restriction-kernel refinement
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def comparison :
    (S J A m).rightDerivedFunctorPlus ⋙ (v A).mapDerivedCategoryPlus ⟶
      (V J A).mapDerivedCategoryPlus ⋙ (S₀ J m).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (kernelIdentity J A m).hom
end CategoryTheory.ModuleRestrictionKernel
