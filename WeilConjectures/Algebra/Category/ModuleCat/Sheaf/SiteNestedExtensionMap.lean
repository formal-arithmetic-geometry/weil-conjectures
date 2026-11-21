/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems

/-! # Canonical maps between extensions of localized restrictions

`nested` is the adjunction transpose of the restriction of the extension unit,
using the canonical `overFunctorMap` comparison for relocalization.

## References

* Stacks Project, Modules on Sites, Tags 03DH, 03DI, 03DJ and 04IY
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SubterminalLocal

/-- The coefficient ring sheaf used by the recorded module-sheaf category. -/
abbrev coefficients {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) : Sheaf J RingCat.{max c v r} :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- Modules on the ambient ringed site. -/
abbrev Modules {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) :=
  ringedSiteModules.{max c v r} (coefficients.{c, v, r} R)

/-- Modules on a slice ringed site. -/
abbrev SliceModules {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) (Z : C) :=
  ringedSiteModules.{max c v r} ((coefficients.{c, v, r} R).over Z)

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The exact extension-by-zero functor supplied by the localized-site framework. -/
abbrev jbang (Z : C) : SliceModules.{c, v, r} R Z ⥤ Modules.{c, v, r} R :=
  localizedSystemExtension.{c, v, r} R Z

/-- Restriction to a slice, supplied by the localized-site framework. -/
abbrev jstar (Z : C) : Modules.{c, v, r} R ⥤ SliceModules.{c, v, r} R Z :=
  localizedSystemRestriction.{c, v, r} R Z

/-- The recorded extension/restriction adjunction. -/
abbrev adj (Z : C) : jbang.{c, v, r} R Z ⊣ jstar.{c, v, r} R Z :=
  localizedSystemAdjunction.{c, v, r} R Z

/-- The canonical nested-open map, obtained by transposing restriction of the unit. -/
def nested {A B : C} (f : A ⟶ B) (M : Modules.{c, v, r} R) :
    (jbang.{c, v, r} R A).obj ((jstar.{c, v, r} R A).obj M) ⟶
      (jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj M) :=
  ((adj.{c, v, r} R A).homEquiv _ _).symm
    ((overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv.app M ≫
      (overMap.{max c v r} (coefficients.{c, v, r} R) f).map
        ((adj.{c, v, r} R B).unit.app ((jstar.{c, v, r} R B).obj M)) ≫
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).hom.app
        ((jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj M)))

end SheafOfModules.SubterminalLocal
