/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Descent of sections along finite surjective morphisms

Let `r : Y' ⟶ Y` be finite and surjective and `G` an abelian étale sheaf on `Y`. A global
section `σ'` of `r^* G` whose two pullbacks to `Y' ×_Y Y'` agree descends to a global section
of `G`: the sequence `Γ(Y, G) ⟶ Γ(Y', r^* G) ⇉ Γ(Y' ×_Y Y', (r ∘ pr)^* G)` is an equalizer.
At a geometric point `ȳ` of `Y` with algebraically closed field, the stalk of `r_* r^* G` is
the product of copies of `G_ȳ` indexed by the geometric points of `Y'` over `ȳ`, and the two
maps to the stalk of the pushforward from `Y' ×_Y Y'` compare the components at the two
members of a pair of such points; since the fibre is nonempty, the equalizer is `G_ȳ`.

## References

- Stacks Project, Lemma 59.55.5, <https://stacks.math.columbia.edu/tag/09Z2>
- Stacks Project, Remark 59.55.6, <https://stacks.math.columbia.edu/tag/09Z3>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- **Descent along a finite surjective morphism.** Let `r : Y' ⟶ Y` be finite and surjective,
`G` an abelian étale sheaf on `Y` and `σ'` a global section of `r^* G` (a section over the
terminal étale `Y'`-scheme `Y'`) whose two restrictions along the projections
`Y' ×_Y Y' ⟶ Y'` agree. Then `σ'` is the pullback of a global section of `G`. -/
@[stacks 09Z3]
theorem exists_pullSection_eq_of_isFinite_of_surjective {Y Y' : Scheme.{u}} (r : Y' ⟶ Y)
    [IsFinite r] [Surjective r] (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (σ' : ((r)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y'))))
    (h : restrictAlong r G (pullback.fst r r) (pullback.fst r r ≫ r) rfl
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.fst r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ' =
      restrictAlong r G (pullback.snd r r) (pullback.fst r r ≫ r) pullback.condition
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.snd r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ') :
    ∃ σ : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
      pullSection r G (V := Scheme.Etale.mk (𝟙 Y')) (U := Scheme.Etale.mk (𝟙 Y)) r
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ = σ' :=
  sorry

end AlgebraicGeometry.Etale
