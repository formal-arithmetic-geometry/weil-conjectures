/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Bounded-below injective resolutions on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 21.19 (Tag 07A5), using
Injectives, Theorem 19.12.6 (Tag 079P)
(blueprint: lem-sc-bounded-below-injective-resolution).
-/

universe u

open CategoryTheory

namespace SheafOfModules

/-- Every bounded-below complex of modules on a small ringed site admits a quasi-isomorphism
into a bounded-below complex with injective terms which is also K-injective.

Source: Stacks Project, Tags 07A5 and 079P, with the bounded-below replacement furnished by
`CochainComplex.Plus.exists_quasiIso_injective`
(blueprint: lem-sc-bounded-below-injective-resolution).

Proof:
1. The category of module sheaves on a small ringed site is Grothendieck abelian by the
first clause of `prop-pur-kinjective-resolutions-exist`. By
`lem-sp-grothendieck-enough-injectives` it has enough injectives.
2. Choose a lower bound for `G`. Apply `lem-sc-bounded-below-injective-resolution-existence`
(`CochainComplex.Plus.exists_quasiIso_injective`) in this abelian category. Forgetting the
packaging in the category of injective objects gives a complex `I`, bounded below, with
injective terms and a quasi-isomorphism `G ⟶ I`.
3. Apply `lem-weil-pbc-bounded-below-injectives-kinjective`
(`CochainComplex.isKInjective_of_injective`) to conclude that `I` is K-injective. -/
theorem exists_boundedBelow_injective_resolution
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hG : ∃ n : ℤ, G.IsStrictlyGE n) :
    ∃ (I : CochainComplex
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (i : G ⟶ I),
      QuasiIso i ∧ (∃ n : ℤ, I.IsStrictlyGE n) ∧
        (∀ n : ℤ, Injective (I.X n)) ∧ I.IsKInjective := by
  sorry

end SheafOfModules
