/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Exact restriction and extension by zero on a localized ringed site

Source: Stacks Project, Modules on Sites, Section 03DH and Lemmas 03DI, 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restriction to the localized ringed site is exact. The sheafification of the
extension-by-zero presheaf is exact and left adjoint to restriction. The adjunction
contains the Hom equivalence, natural in both module sheaves.

Source: Stacks Project, Modules on Sites, Section 03DH and Lemmas 03DI, 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).

Proof:
1. Restriction keeps the section modules and their restriction maps, by
   `def-pur-localized-ringed-site`. Compose `def-weil-extension-by-zero-presheaf`
   with `def-weil-presheaf-modules-sheafification` to obtain the extension functor.
2. By `lem-pc-sites-module-sheafification-interface`, its underlying abelian sheaf
   is the sheafified direct-sum extension. Apply the natural Hom bijection of
   `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`. Its sectionwise formula
   respects multiplication by sections of the ring sheaf in both directions,
   so it restricts to the natural bijection of module Hom sets.
3. Forget a short exact sequence to abelian sheaves using
   `lem-weil-pbc-module-sheaves-colimits-forgetful`. Apply
   `lem-weil-pbc-site-restriction-exact` and reflect exactness through the faithful
   exact forgetful functor. This proves exactness of module restriction.
4. The underlying abelian extension is isomorphic to the left adjoint of
   `lem-weil-pbc-site-restriction-adjunction`, by uniqueness of left adjoints and
   `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`. Its exactness follows
   from `lem-weil-pbc-site-extension-by-zero-exact`. Reflect exactness through
   the module forgetful functor, using the sheafification interface again. -/
theorem localizedModule_adjunction_exact
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (O : Sheaf J.toGrothendieck CommRingCat.{u}) (U : C) :
    PreservesFiniteLimits
        (overFunctor.{u} ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U) ∧
      PreservesFiniteColimits
        (overFunctor.{u} ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U) ∧
      PreservesFiniteLimits
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj)) ∧
      PreservesFiniteColimits
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj)) ∧
      Nonempty (Adjunction
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj))
        (overFunctor.{u}
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U)) := by
  sorry

end SheafOfModules
