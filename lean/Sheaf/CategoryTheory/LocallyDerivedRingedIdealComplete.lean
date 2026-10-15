/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedIdealGenerators
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Sheaf.CategoryTheory.RingedSectionLocalization

/-!
# Local derived completeness for an ideal sheaf

Source: Stacks Project, algebraization.tex, Tags 0999 and 099F
(blueprint: def-weil-pbc-locally-derived-ringed-ideal-complete).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Local derived completeness means vanishing of derived internal Hom from localization
at every section of the ideal, on every slice, with no boundedness hypothesis.
Source: Stacks Project, algebraization.tex, Tags 0999 and 099F
(blueprint: def-weil-pbc-locally-derived-ringed-ideal-complete). -/
def IsLocallyDerivedRingedIdealComplete
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (E : ringedSiteDerived O) : Prop :=
  ∀ (U : C) (f : O.obj.obj (op U)),
    (∃ y : I.val.obj (op U), ι.val.app (op U) y = f) →
      IsZero ((derivedInternalHom (J.over U) (O.over U)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))),
          (ringedDerivedRestriction O U).obj E))

end CategoryTheory
