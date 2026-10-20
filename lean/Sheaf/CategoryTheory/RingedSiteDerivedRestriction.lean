/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# RingedSiteDerivedRestriction

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(blueprint: def-weil-pbc-ringed-site-derived-restriction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- Restriction of a derived object K to the slice site C/U, computed by
restricting the canonical representative DerivedCategory.Q.objPreimage K
and applying Q on the slice. This represents K|U: slice restriction is exact,
as expressed by localizedModule_restriction_quasiIso. No boundedness is used.
The existing module_overFunctor_preservesZero supplies the complex functor.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(blueprint: def-weil-pbc-ringed-site-derived-restriction). -/
noncomputable def ringedSiteDerivedRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    (K : DerivedCategory (SheafOfModules.{u} R)) :
    DerivedCategory (SheafOfModules.{u} (R.over U)) :=
  letI := module_overFunctor_preservesZero R U
  DerivedCategory.Q.obj
    (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage K))

end CategoryTheory
