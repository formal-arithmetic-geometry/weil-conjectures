/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# H-projective permanence under a separated factor

Source: Stacks Project, Morphisms of Schemes, Tag 0C4Q, lemma-projective-permanence
(blueprint: lem-per-h-projective-permanence).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `g` is separated and `f ≫ g` embeds in `ℙⁿ_B`, then `f` embeds in `ℙⁿ_T`.

Source: Stacks Project, Morphisms of Schemes, Tag 0C4Q, lemma-projective-permanence;
Tag 01WF, lemma-H-projective-base-change (blueprint: lem-per-h-projective-permanence).

Proof plan: use separatedness of `g` to make the graph of `f` a closed immersion into
`Z ×_B T`; base change the given closed immersion into `ℙⁿ_B`; compose the two closed
immersions; and identify the resulting projective space with `ℙⁿ_T` by projective-space
base change. The graph and base-change identifications use the fibre-product universal
property, and the same finite coordinate set `Fin (n + 1)` is retained throughout.
-/
theorem isHProjective_of_comp_of_isSeparated
    {Z T B : Scheme.{u}} (f : Z ⟶ T) (g : T ⟶ B) [IsSeparated g]
    (n : ℕ) (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); B)) (hi : IsClosedImmersion i)
    (hif : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B) = f ≫ g) :
    ∃ j : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T),
      IsClosedImmersion j ∧ j ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T) = f := by
  sorry

end AlgebraicGeometry
