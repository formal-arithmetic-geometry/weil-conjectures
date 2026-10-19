/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint

/-! # Localized module adjunction for independent site universes

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
The construction retains the actual direct-sum presheaf and its sheafification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : C)

/-- Actual direct-sum extension followed by sheafification, at independent site universes.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
abbrev localizedSystemExtension :
    SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U) ⥤
    SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) :=
  extensionByZeroPresheaf.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U ⋙
      PresheafOfModules.sheafification (𝟙 _)

/-- Actual restriction to the slice, retaining the same section modules and maps.
Source: Stacks 03DJ (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
abbrev localizedSystemRestriction :
    SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
    SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U) :=
  overFunctor.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U

/-- Exactness of both actual localized module functors.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof: restriction retains sectionwise groups, and thus kernels and sheafified cokernels.
The direct-sum extension has the standard summand Hom correspondence with restriction.
After module sheafification this is the extension/restriction adjunction. Forgetting
module actions identifies extension with the exact abelian-sheaf extension. Reflect
exactness through the faithful exact forgetful functor. Addition is componentwise.
All constructions remain in max c v r; no equality of the site universes is imposed. -/
theorem localizedSystemExact :
    (localizedSystemExtension.{c, v, r} R U).Additive ∧
    PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) ∧
    PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) ∧
    (localizedSystemRestriction.{c, v, r} R U).Additive ∧
    PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) ∧
    PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) := by
  sorry

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemExtensionAdditive : (localizedSystemExtension.{c, v, r} R U).Additive :=
  (localizedSystemExact.{c, v, r} R U).1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemExtensionLimits :
    PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemExtensionColimits :
    PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemRestrictionAdditive : (localizedSystemRestriction.{c, v, r} R U).Additive :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemRestrictionLimits :
    PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedSystemRestrictionColimits :
    PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.2.2

open Classical in
/-- The normalized localized adjunction, uniquely fixed by the summand injection unit.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof: direct-sum elimination sends a map from the extension to a compatible map on each
slice object. Its inverse includes each section in the summand of its structure arrow.
Sheafification extends this natural bijection uniquely to sheaves. The summands generate
locally, so the displayed unit determines the adjunction uniquely. -/
theorem localizedSystemAdjunction_existsUnique :
    ∃! adj : localizedSystemExtension.{c, v, r} R U ⊣
      localizedSystemRestriction.{c, v, r} R U,
      ∀ (M : SheafOfModules.{max c v r}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
        (W : (Over U)ᵒᵖ) (x : M.val.obj W),
        (adj.unit.app M).val.app W x =
          ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
            (𝟙 ((sheafCompose J
              (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).unit.app
                ((extensionByZeroPresheaf.{max c v r}
                  ((sheafCompose J
                    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U).obj M)).app
            (op W.unop.left)
              (DirectSum.lof (R.obj.obj (op W.unop.left)) (W.unop.left ⟶ U)
                (fun a ↦ M.val.obj (op (Over.mk a))) W.unop.hom x) := by
  sorry

/-- The actual adjunction selected by the unique prescribed unit.
Source: Stacks 03DI--03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedSystemAdjunction : localizedSystemExtension.{c, v, r} R U ⊣
    localizedSystemRestriction.{c, v, r} R U :=
  (localizedSystemAdjunction_existsUnique.{c, v, r} R U).exists.choose


end SheafOfModules
