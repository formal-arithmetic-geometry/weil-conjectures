module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom

import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Quasi-inverse with prescribed objects and comparison isomorphisms

Source: Stacks Project, Tag 05SG, `lemma-construct-quasi-inverse`, including the final
fully faithful cancellation in its proof (blueprint: lem-sfb-chosen-object-quasi-inverse).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-- A fully faithful functor has a unique quasi-inverse extending the prescribed objects
and comparison isomorphisms. The equalities `h` identify the functor's object values with
`j`; the `eqToHom` factors only transport along these equalities.

Source: Stacks Project, Tag 05SG, `lemma-construct-quasi-inverse`
(blueprint: lem-sfb-chosen-object-quasi-inverse).

Proof: Invert each bijection on Hom sets and send `f : X ⟶ Y` to the preimage of
`(iX X).inv ≫ f ≫ (iX Y).hom`. The category laws cancel the adjacent inverse comparisons,
and injectivity of `F.map` proves preservation of identities and composition
(`def-nagata-category`). These arrow equations make the specified comparisons natural;
the inverse comparisons are natural by the same equations, giving the natural isomorphism
`i`. Any other functor extending the same objects with the same natural comparisons has
this arrow formula by naturality, so faithfulness gives equality of functors.
Finally, evaluate the inverse comparison at `F.obj A`. Its naturality gives a natural
isomorphism after postcomposition with `F`; cancel `F` by
`Functor.fullyFaithfulCancelRight` (`lem-sfb-fully-faithful-cancel-iso-components`) to obtain
`e : F ⋙ J ≅ 𝟭 A`. The component formula follows from `map_preimage`, and faithfulness
makes it unique. The two natural isomorphisms exhibit `F` and `J` as quasi-inverses. -/
theorem exists_quasiInverse_with_objIso
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) [F.Full] [F.Faithful] (j : B → A)
    (iX : ∀ X : B, X ≅ F.obj (j X)) :
    ∃ (J : B ⥤ A) (h : ∀ X : B, J.obj X = j X) (i : 𝟭 B ≅ J ⋙ F),
      (∀ X : B, i.hom.app X ≫ eqToHom (congrArg F.obj (h X)) = (iX X).hom) ∧
      (∀ (X Y : B) (f : X ⟶ Y),
        F.map (J.map f) = eqToHom (congrArg F.obj (h X)) ≫
          (iX X).inv ≫ f ≫ (iX Y).hom ≫ eqToHom (congrArg F.obj (h Y).symm)) ∧
      (∃ e : F ⋙ J ≅ 𝟭 A, ∀ a : A,
        F.map (e.hom.app a) =
          eqToHom (congrArg F.obj (h (F.obj a))) ≫ (iX (F.obj a)).inv) ∧
      (∀ (J' : B ⥤ A) (h' : ∀ X : B, J'.obj X = j X) (i' : 𝟭 B ≅ J' ⋙ F),
        (∀ X : B, i'.hom.app X ≫ eqToHom (congrArg F.obj (h' X)) = (iX X).hom) →
          J' = J) ∧
      F.IsEquivalence ∧ J.IsEquivalence := by
  sorry

end CategoryTheory.Functor
