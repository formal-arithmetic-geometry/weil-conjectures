/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# RingedSiteLocalization

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- Compatibility of the restrictions of a section to all objects of the slice site.

Source: Stacks Project, Modules on Sites, restriction to a slice (Tag 03DH),
as used in algebraization.tex, Tag 0997. -/
theorem ringedSiteSectionLocalization_compatible
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (V W : (Over U)ᵒᵖ) (a : V ⟶ W) :
    R.obj.map a.unop.left.op (R.obj.map V.unop.hom.op f) =
      R.obj.map W.unop.hom.op f := by
  rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]

/-- The module O_U[1/f] on the slice site. It is the colimit of the sequence
O_U --f--> O_U --f--> ..., hence the sheafification of the sectionwise
localizations.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998. -/
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
