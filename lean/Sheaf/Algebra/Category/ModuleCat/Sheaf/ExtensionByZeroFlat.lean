/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Flatness of the localized unit extended by zero

Source: Stacks Project, Modules on Sites, Lemma 18.28.7, Tag 03EV, clause (2)
(blueprint: lem-pc-sites-modules-j-shriek-flat).
-/

universe u

open CategoryTheory

namespace SheafOfModules

/-- The sheafification of the extension-by-zero presheaf of the unit module on `C/U`
is flat over `R`. Before sheafification, the extension-by-zero presheaf at `V` is the
direct sum of copies of `R(V)` indexed by morphisms `V ⟶ U`.

Source: Stacks Project, Modules on Sites, Lemma 18.28.7, Tag 03EV, clause (2)
(blueprint: lem-pc-sites-modules-j-shriek-flat).

Proof:
1. By `def-weil-extension-by-zero-presheaf`, the unit on the localized ringed site
   has extension-by-zero presheaf `P(V) = ⨁ (φ : V ⟶ U), R(V)`. Each section module
   is free and therefore flat, including an empty direct sum. Presheaf tensor products
   and finite limits are computed sectionwise, so tensoring with `P` preserves finite
   limits (Stacks Tag 03ES).
2. By `def-weil-presheaf-modules-sheafification`, the extension-by-zero sheaf is `P^#`.
   Since `R` is already a sheaf, apply `lem-pc-sites-modules-sheafification-flat`
   (Stacks Tag 03ET) to the finite-limit-preserving tensor functor from step 1.
   Tensoring with `P^#` preserves finite limits; tensor is right exact, so this is
   exactness, namely `def-pc-flat-sheaf-modules`. -/
theorem isFlat_extensionByZero_unit
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C) :
    IsFlat ((PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).obj
        ((extensionByZeroPresheaf.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj
            (unit (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U)))) := by
  sorry

end SheafOfModules
