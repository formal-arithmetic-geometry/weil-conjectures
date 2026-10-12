/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.QuotientJShriek

/-!
# Sheaves of modules on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 07A5; Modules on Sites,
Lemmas 03DA, 03DB and 03EW (blueprint: lem-pur-ringed-site-grothendieck-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{u})

local notation "R" => Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) O

set_option synthInstance.maxHeartbeats 100000 in
-- Inferring the coproduct reduces the repeated sheaf-compose expression in the summands.
/-- Sheaves of modules over a sheaf of commutative rings on a small site form a
Grothendieck abelian category. A specific generator is the coproduct, over all
objects `U`, of the sheafifications of the extension-by-zero presheaves of
the rank-one module on the localized ringed site.

Source: Stacks Project, Section 07A5 and Lemmas 03DA, 03DB, 03EW
(blueprint: lem-pur-ringed-site-grothendieck-abelian).

Proof:
1. The category is abelian by `lem-pur-ringed-site-module-category-abelian`.
2. By `lem-weil-pbc-module-sheaves-colimits-forgetful`, small colimits are
   obtained by sheafifying sectionwise colimits; forgetting to abelian sheaves
   is faithful and exact and commutes with colimits.
3. For a filtered diagram of short exact sequences, that forgetful functor
   reduces exactness to `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`.
4. `lem-pc-sites-modules-quotient-j-shriek` gives an epimorphism onto every
   module sheaf from a sum of the localized rank-one extensions indexed by
   sections. A nonzero quotient is nonzero on some summand. Extend the
   corresponding map by zero on the other summands of the coproduct indexed
   by objects. Thus this fixed coproduct is a generator.
5. These properties give `def-sp-grothendieck-abelian`. The summands use
   `def-pur-localized-ringed-site`, `def-weil-presheaf-modules-sheafification`
   and `def-weil-extension-by-zero-presheaf` exactly as in the statement. -/
theorem grothendieckAbelian_with_localized_generator :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) ∧
      IsSeparator (∐ fun U : C ↦
        (PresheafOfModules.sheafification.{u} (𝟙 (R).obj)).obj
          ((extensionByZeroPresheaf.{u} R U).obj (unit ((R).over U)))) := by
  sorry

end SheafOfModules
