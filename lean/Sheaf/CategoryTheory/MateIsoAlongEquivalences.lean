/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Invertibility of mates along an equivalence and a fully faithful functor

Source: the abstract transport argument used for Deligne, La conjecture de Weil II,
(1.1.7), p. 151, and (1.1.14), p. 153
(blueprint: lem-weil-mate-iso-along-equivalences).
The abstract lemma is agent-written; those passages motivate its use but do not state it.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory

/-- The right mate of a natural isomorphism is invertible when `G` is an equivalence
and `G'` is fully faithful. Its component at `d` is
`adj'.unit.app (G.obj (R.obj d)) ≫ R'.map (θ.hom.app (R.obj d)) ≫
R'.map (G'.map (adj.counit.app d))`.

Source: agent-written abstract transport lemma for Deligne, La conjecture de Weil II,
(1.1.7), p. 151, and (1.1.14), p. 153
(blueprint: lem-weil-mate-iso-along-equivalences).

Proof:
1. For `c : C` and `d : D`, full faithfulness of `G` and `G'`, the two adjunction
bijections, and precomposition with `θ.hom.app c` give a bijection from
`Hom(G c, G (R d))` to `Hom(G c, R' (G' d))`.
2. Write a morphism in the first Hom set as `G.map t`. The adjunction formulas
send it to
`adj'.unit.app (G.obj c) ≫
R'.map (θ.hom.app c ≫ G'.map (L.map t) ≫ G'.map (adj.counit.app d))`.
3. Naturality of `θ` at `t` and of `adj'.unit` at `G.map t` identify this
bijection with postcomposition by the displayed mate component.
4. Essential surjectivity of `G` transports the same bijectivity from sources
`G.obj c` to every object of `C'`, by precomposition with an isomorphism.
5. Surjectivity at the target of the mate supplies a right inverse. Injectivity
at its source then gives the left inverse equation. Every component is invertible.
6. Counit naturality, naturality of `θ`, and unit naturality give naturality of
the mate. Multiplying this equation by the component inverses proves their
naturality, so they form a natural inverse. -/
theorem isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (G : C ⥤ C') (G' : D ⥤ D') [G.IsEquivalence] [G'.Full] [G'.Faithful]
    (θ : G ⋙ L' ≅ L ⋙ G') :
    IsIso (mateEquiv adj adj' θ.hom).natTrans := by
  sorry

end CategoryTheory
