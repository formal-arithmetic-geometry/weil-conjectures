/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# RingedSiteLocalization

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(blueprint: def-weil-pbc-ringed-site-section-localization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- Compatibility of the restrictions of a section to all objects of the slice site.

Source: Stacks Project, Modules on Sites, restriction to a slice (Tag 03DH),
as used in algebraization.tex, Tag 0997
(blueprint: def-weil-pbc-ringed-site-section-localization).

Proof: for an arrow a in the opposite slice, Over.w says that its underlying
arrow followed by the structural arrow of its target equals the structural
arrow of its source. Apply the opposite functor, then R.obj.map, and evaluate
at f. Functor.map_comp identifies the result with successive restriction. -/
theorem ringedSiteSectionLocalization_compatible
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (V W : (Over U)ᵒᵖ) (a : V ⟶ W) :
    R.obj.map a.unop.left.op (R.obj.map V.unop.hom.op f) =
      R.obj.map W.unop.hom.op f := by
  sorry

/-- The module O_U[1/f] on the slice site. It is the colimit of the sequence
O_U --f--> O_U --f--> ..., hence the sheafification of the sectionwise
localizations: filtered colimits of presheaves are sectionwise and colimits
of module sheaves are obtained by sheafifying presheaf colimits.
The rank-one endomorphism comes from the compatible family f restricted to
all objects over U, using Mathlib's unitHomEquiv, not a new module structure.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(blueprint: def-weil-pbc-ringed-site-section-localization). -/
noncomputable def ringedSiteSectionLocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    SheafOfModules.{u} (R.over U) :=
  colimit (Functor.ofSequence (X := fun _ : ℕ => SheafOfModules.unit (R.over U))
    (fun _ => (SheafOfModules.unit (R.over U)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun V => R.obj.map V.unop.hom.op f)
        (fun {V W} a => ringedSiteSectionLocalization_compatible R U f V W a))))

end CategoryTheory
