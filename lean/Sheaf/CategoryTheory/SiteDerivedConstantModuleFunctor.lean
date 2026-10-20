/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The constant realization on unbounded derived categories

Source: Stacks Project, Cohomology on Sites, paragraph immediately before Tag 09BD
(blueprint: def-sfb-site-derived-constant-module-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v wR wS

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The chosen localization size of the existing module-sheaf category.
Source: Stacks 05RU (blueprint: def-sfb-site-derived-constant-module-functor).
The explicit category fixes its module universe before instance inference. -/
abbrev siteModuleHasDerivedCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) :=
  HasDerivedCategory.{wS} (SheafOfModules.{max u v} S)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

/-- The existing constant-module functor is additive and exact.
Source: Stacks Project, Sites, Tag 00WJ; Modules on Sites, Tag 03CY; Cohomology on
Sites, paragraph before Tag 09BD
(blueprint: def-sfb-site-derived-constant-module-functor).
Proof: the constant presheaf functor takes a sequence to the identical sequence
at every object, and therefore preserves kernels and cokernels sectionwise.
Module sheafification is exact. Composing these functors is additive and exact;
the abelian exactness criterion gives finite-limit and finite-colimit preservation.
The module action is the unique extension of the constant-presheaf action. -/
theorem siteConstantModuleFunctorGeneral_exact :
    (siteConstantModuleFunctorGeneral J R).Additive ∧
      PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R) ∧
      PreservesFiniteColimits (siteConstantModuleFunctorGeneral J R) := by
  let P := siteConstantModulePresheafGeneral (C := C) R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  let S := PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))
  change (P ⋙ S).Additive ∧ PreservesFiniteLimits (P ⋙ S) ∧
    PreservesFiniteColimits (P ⋙ S)
  have : PreservesFiniteLimits (P ⋙ S) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (P ⋙ S) := comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

/-- Apply the existing constant-module functor degreewise and descend at
quasi-isomorphisms by Mathlib's canonical exact-functor localization.
Source: Stacks Project, Cohomology on Sites, paragraph before Tag 09BD
(blueprint: def-sfb-site-derived-constant-module-functor).
This is the exact constant realization, with no replacement or arbitrary functor choice. -/
def siteDerivedConstantModuleFunctor
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)))] :
    DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (SheafOfModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R))) :=
  haveI := (siteConstantModuleFunctorGeneral_exact J R).1
  haveI := (siteConstantModuleFunctorGeneral_exact J R).2.1
  haveI := (siteConstantModuleFunctorGeneral_exact J R).2.2
  (siteConstantModuleFunctorGeneral J R).mapDerivedCategory

end CategoryTheory
