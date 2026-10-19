/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Sheaf.CategoryTheory.NaturalTransportInduction
import Sheaf.CategoryTheory.SimplicialOperatorsReconstruction

/-! # The augmented simplicial object of a comonad

Source: literature/stacks-project/simplicial.tex, Example 0G5M (example-godement)
and Lemma 0G5N (lemma-godement) (blueprint: lem-trf-comonad-simplicial-object).

The powers are `NaturalTransport.power`, with zero power the identity functor.
Heterogeneous equality records the specified operators without introducing arbitrary
comparison isomorphisms between the different parenthesizations of these powers.
The final functor records evaluation, including its naturality in the evaluated object.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

/-- The powers of a counital coassociative endofunctor, with the prescribed face and
 degeneracy transformations, form an augmented simplicial object, natural upon evaluation.

Source: literature/stacks-project/simplicial.tex, Example 0G5M and Lemma 0G5N
(blueprint: lem-trf-comonad-simplicial-object).

Proof plan:
1. Whiskering gives natural transformations. Expand horizontal composition at an object;
   naturality gives the interchange identity and the associativity of horizontal composition.
2. For `i < j`, interchange reduces both face--face composites to the word with counits in
   positions `i` and `j`. Adjacent positions use the identity on the zero power.
3. For the mixed identities away from the duplicated factor, interchange moves the counit
   past the comultiplication. The cases before and after that factor give the two mixed laws.
4. At the duplicated factor the two mixed composites reduce to the two counit equations,
   including the two faces after the degree-zero degeneracy.
5. Distinct degeneracy positions commute by interchange. Equal positions give the two
   iterated comultiplications, which agree by coassociativity, also in degree zero.
6. Apply `lem-trf-simplicial-operators-reconstruction` in the category of endofunctors to
   obtain the simplicial object with exactly these objects, faces and degeneracies.
7. In degree `n`, horizontally compose `n + 1` copies of the counit. These maps commute
   with faces by interchange, and with degeneracies by the counit equations.
8. The morphism clause of `lem-trf-simplicial-operators-reconstruction` assembles them
   into the augmentation, whose degree-zero component is the given counit.
9. Evaluate the endofunctors and transformations at `x`. Evaluation preserves identities
   and composition. Naturality of each transformation makes the degree maps on `x ⟶ y`
   commute with every operator and augmentation component; functoriality of the powers
   proves the functor laws in `x`. No limits, colimits or smallness assumptions are needed. -/
theorem comonad_simplicial_object
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) (e : T ⟶ 𝟭 C) (c : T ⟶ T ⋙ T)
    (h₁ : c ≫ Functor.whiskerRight e T ≫ (Functor.leftUnitor T).hom = 𝟙 T)
    (h₂ : c ≫ Functor.whiskerLeft T e ≫ (Functor.rightUnitor T).hom = 𝟙 T)
    (h₃ : c ≫ Functor.whiskerRight c T ≫ (Functor.associator T T T).hom =
      c ≫ Functor.whiskerLeft T c) :
    ∃ (B : SimplicialObject (C ⥤ C))
      (α : B ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)),
      (∀ n : ℕ, B.obj (Opposite.op (SimplexCategory.mk n)) =
        NaturalTransport.power T (n + 1)) ∧
      (∀ (n : ℕ) (i : Fin (n + 2)), HEq (B.δ i)
        (Functor.whiskerLeft (NaturalTransport.power T (n + 1 - i.val))
          (Functor.whiskerRight e (NaturalTransport.power T i.val)))) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)), HEq (B.σ i)
        (Functor.whiskerLeft (NaturalTransport.power T (n - i.val))
          (Functor.whiskerRight c (NaturalTransport.power T i.val)))) ∧
      HEq (α.app (Opposite.op (SimplexCategory.mk 0))) e ∧
      ∃ E : C ⥤ SimplicialObject.Augmented C,
        E ⋙ SimplicialObject.Augmented.drop = B.flip ∧
        E ⋙ SimplicialObject.Augmented.point = 𝟭 C ∧
        ∀ (x : C) (n : SimplexCategoryᵒᵖ),
          HEq ((E.obj x).hom.app n) ((α.app n).app x) := by
  sorry

end CategoryTheory
