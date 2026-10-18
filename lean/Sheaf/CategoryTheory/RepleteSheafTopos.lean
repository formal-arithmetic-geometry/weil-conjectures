/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Replete topoi of set-valued sheaves

Source: the Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-def-pe-replete`, node `det-pe-replete-definition`
(blueprint: det-pe-replete-definition).

For a site presented by a precoverage `K` satisfying `K.IsSiteForCoverings`, use the
associated topology `K.toGrothendieck`, as in `def-weil-pbc-sites-and-cohomology`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology

/-- Source: the Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-def-pe-replete`, node `det-pe-replete-definition`
(blueprint: det-pe-replete-definition).

The topos of set-valued sheaves on `J` is replete when every inverse sequence of
epimorphisms has epimorphic projections from its limit, at every natural-number index.
An inverse sequence is `F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))`; its adjacent transition
is `F.map (homOfLE (Nat.le_succ n)).op`.

The existing sectionwise-limit construction (`Sheaf.createsLimitsOfShape`, Stacks 00W2)
identifies `limit F` at `V` with the tuples `x n ∈ (F.obj (op n))(V)` satisfying
`t_n (x (n + 1)) = x n`; `limit.π F (op m)` is the coordinate projection `x ↦ x m`.
By `Sheaf.isLocallySurjective_iff_epi` (Stacks 00WM and 00WN), epimorphism here means
that each target section admits lifts after passing to a covering. Thus neither the
transition hypothesis nor the projection conclusion asserts surjectivity on all sections.
The extra universe `w` allows section sets larger than the site. -/
def IsReplete {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) : Prop :=
  ∀ (F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))),
    (∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) →
      ∀ m : ℕ, Epi (limit.π F (op m))

end CategoryTheory.GrothendieckTopology
