/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Local cohomological bounds for module sheaves

Source: Stacks Project, Cohomology on Sites, Tag 0D6R,
`situation-olsson-laszlo` (blueprint: def-sfb-ringed-local-bound-property).
-/

@[expose] public section

set_option autoImplicit false

universe u e

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The local bound property of Stacks Tag 0D6R, `situation-olsson-laszlo`
(blueprint: def-sfb-ringed-local-bound-property).

Coverings are actual covering presieves of the given site. The second clause says
that the covers on whose domains the uniform bound holds are cofinal: each covering
has one of them as a refinement, with factorization through a member of the original
cover. Taking all such good covers gives the collection in the source. Cohomology is
that of the underlying abelian sheaf, equivalently right derived module sections. -/
def HasRingedLocalBoundProperty
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (O : Sheaf J.toGrothendieck RingCat.{u})
    [HasExt.{e} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    (P : ObjectProperty (ringedSiteModules.{u, u, u, u} O)) : Prop :=
  ∃ V : Set C,
    (∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (W : C) (a : W ⟶ U), S a → W ∈ V) ∧
    ∀ U ∈ V, ∃ d : ℤ, ∀ S : Presieve U, S ∈ J U →
      ∃ T : Presieve U, T ∈ J U ∧
        (∀ (W : C) (a : W ⟶ U), T a →
          ∃ (Z : C) (b : Z ⟶ U) (c : W ⟶ Z), S b ∧ c ≫ b = a) ∧
        ∀ (W : C) (a : W ⟶ U), T a →
          ∀ F : ringedSiteModules.{u, u, u, u} O, P F →
            ∀ p : ℕ, d < (p : ℤ) →
              IsZero (((SheafOfModules.toSheaf O).obj F).H' p W)

end CategoryTheory
