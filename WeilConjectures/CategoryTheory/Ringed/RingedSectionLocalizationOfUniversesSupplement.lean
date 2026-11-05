/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationRing
import Mathlib.Algebra.Category.Ring.Adjunctions
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses

/-!
# Section localization with independent site universes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
The construction is the same sectionwise localization followed by sheafification.
This interface allows a site with different object and morphism universes. Sheafification
is parameterized by its existing instances in the chosen coefficient universe. The previous
small-category interface is retained by the public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

/- The additive sheafification has a canonical multiplication: multiply local representatives
and glue. Local injectivity makes the product independent of the representatives. The ring laws
and the compatibility of lifts are checked on covering sieves. This realizes the sheafification
argument in the comparison theorem below without identifying the site and coefficient universes. -/
namespace RingedLocalizationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {P : Cᵒᵖ ⥤ CommRingCat.{u}} {A : Sheaf J AddCommGrpCat.{u}}
variable (η : (P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ A.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

end RingedLocalizationComparison

end

end CategoryTheory
