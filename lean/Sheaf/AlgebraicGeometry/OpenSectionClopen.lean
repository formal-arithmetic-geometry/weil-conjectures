/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# An open section of a separated morphism is clopen

Source: blueprint, sec-smooth-purity, sk-def-sf-operations,
lem-weil-pbc-open-section-clopen; Stacks Project, Tag 01KT,
lemma-section-immersion (blueprint: lem-weil-pbc-open-section-clopen).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An open section of a separated morphism has clopen image, and the source together
with the complementary open subscheme is a coproduct decomposition of the target.

Source: blueprint, sec-smooth-purity, sk-def-sf-operations,
lem-weil-pbc-open-section-clopen; Stacks Project, Tag 01KT, lemma-section-immersion.

Proof: The identity of `S` is a closed immersion. Since `s ≫ p` is that identity and
`p` is separated, `IsClosedImmersion.of_comp`
(lem-weil-pbc-closed-immersion-from-composite) makes `s` a closed immersion.
Its image is therefore closed, and is open by the open immersion hypothesis
(def-weil-closed-immersion, def-weil-open-immersion, def-weil-proper-morphism).
The complement is open. These two open subschemes are disjoint and cover `V`.
The sheaf axiom on this disjoint cover identifies sections with the product of
sections on the two pieces, compatibly with restrictions. Thus the two inclusions
exhibit `V` as their scheme coproduct.
(blueprint: lem-weil-pbc-open-section-clopen) -/
theorem open_section_clopen {V S : Scheme.{u}} (p : V ⟶ S) (s : S ⟶ V)
    [IsSeparated p] [IsOpenImmersion s] (hs : s ≫ p = 𝟙 S) :
    IsClopen (Set.range s) ∧
      ∃ W : V.Opens, (W : Set V) = (Set.range s)ᶜ ∧
        Nonempty (IsColimit (BinaryCofan.mk s W.ι)) := by
  sorry

end AlgebraicGeometry
