/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Global-sections acyclicity of injective pushforwards on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 072Z and 0731(3)
(blueprint: lem-sfb-ringed-topos-injective-pushforward-global-acyclic).

Global sections is the existing abelian global-sections functor after forgetting module
scalars. Its right derived functors use injective resolutions in the module category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

-- The intrinsic Grothendieck structure supplies injective resolutions of module sheaves.
attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace CategoryTheory.RingedToposMorphism

/-- The direct image of an injective module is acyclic for module global sections.
Source: Stacks Project, Cohomology on Sites, Tags 072Z and 0731(3)
(blueprint: lem-sfb-ringed-topos-injective-pushforward-global-acyclic).

Proof: apply lem-sfb-injective-pushforward-totally-acyclic to the terminal sheaf of sets
on the target topos. Its generalized sections are precisely global sections, with
pointwise addition: the sum of two maps from the terminal sheaf is their product map
followed by the addition map. Mathlib's global-sections functor has this abelian group
as its value, canonically, by its limit description. Both right derived functors are
computed by injective resolutions in target module sheaves (def-sp-left-exact-additive),
so total acyclicity gives the displayed vanishing in every positive degree. No flatness
of the structural ring map or presentation of the geometric morphism by a site functor
is needed. -/
theorem isZero_rightDerived_globalSections_obj_injective
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (I : ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.toSheaf
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) ⋙
        Sheaf.Γ K AddCommGrpCat.{u}).rightDerived p).obj (f.modules.obj I)) := by
  sorry

end CategoryTheory.RingedToposMorphism
