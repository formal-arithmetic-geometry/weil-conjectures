/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.RingedToposMorphism
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-! # The ringed site of a site automorphism

Source: Stacks, Sites, Tag 00W0 is motivation for the agent-formulated twisted
construction (auxiliary; not a blueprint node).

The presentation below characterizes the integer-labelled arrows, the topology,
the coefficient ring, the two restriction functors, and the orbit-sum adjunction.
No object is selected from the existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

/-- Forget commutativity only for the existing module-sheaf interface.
Source: Stacks 03CV (auxiliary; not a blueprint node). -/
abbrev ring {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- The existing category of sheaves of modules, with the compatible size convention.
Source: Stacks 03CV (auxiliary; not a blueprint node). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := ringedSiteModules.{u} (ring R)

/-- The image of a local pure tensor under ordinary module sheafification.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def pureTensor {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} (M N : Modules R) (X : Cᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) : (M ⊗ N).val.obj X :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app X
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring R).obj)).unit.app
      (M.val ⊗ N.val)).app X (x ⊗ₜ[R.obj.obj X] y))

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

end CategoryTheory.TwistedActionRingedSite
