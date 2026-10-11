/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory

/-!
# Consequences of the Stacks Galois category axioms

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0 and the paragraph
following it (blueprint: lem-galois-axioms).
-/

universe wI wJ w v u

open CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- (blueprint: lem-galois-axioms) Stacks, paragraph after Lemma 0BN0.
A Galois object of a Stacks Galois category is a connected object whose
automorphism group has the same cardinality as its fibre. -/
def IsStacksGaloisObject {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) (X : C) : Prop :=
  IsConnected X ∧ Nat.card (Aut X) = Nat.card (F.obj X)

/-- (blueprint: lem-galois-axioms) Stacks, Lemma 0BN0 and the paragraph after it.
For a Galois category with fibre functor `F`, the seven conjuncts give faithfulness;
detection of monos and epis; detection of initial and terminal objects; epis between
connected objects; determination of a map on a connected source by one fibre element;
the automorphism bound and its transitivity criterion; and the component description
of maps between finite coproducts of connected objects.

For faithfulness, apply `F` to an equalizer and reflect its resulting isomorphism.
For mono and epi detection, apply `F` to the diagonal into a pullback and the fold
map out of a pushout, respectively, then reflect isomorphisms. An initial or terminal
object has empty or singleton fibre; conversely, compare an object with such a fibre
to an initial or terminal object and reflect the resulting bijection. For a map between
connected objects, the equalizer of its cokernel-pair maps is noninitial and hence
isomorphic to the target, giving epi. If two maps agree on one fibre element, their
equalizer is noninitial and hence isomorphic to the connected source. Evaluation at
one element is therefore injective on automorphisms; finiteness gives the cardinal
bound, with equality exactly when its orbit is the whole fibre. Finally, the
component description of maps between finite coproducts of connected objects is
`CategoryTheory.morphism_coproduct_connected_components`
(blueprint: lem-galois-coproduct-morphism-components). -/
theorem stacksGaloisCategory_axioms
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F) :
    Functor.Faithful F ∧
    (∀ {X Y : C} (f : X ⟶ Y),
      (Mono f ↔ Function.Injective (F.map f)) ∧
      (Epi f ↔ Function.Surjective (F.map f))) ∧
    (∀ X : C,
      (Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)) ∧
      (Nonempty (IsTerminal X) ↔
        ∃ s : F.obj X, ∀ t : F.obj X, t = s)) ∧
    (∀ {X Y : C}, IsConnected X → IsConnected Y →
      ∀ f : X ⟶ Y, Epi f) ∧
    (∀ {X Y : C}, IsConnected X →
      ∀ (a b : X ⟶ Y) (s : F.obj X), F.map a s = F.map b s → a = b) ∧
    (∀ X : C, IsConnected X → ∀ s : F.obj X,
      Function.Injective (fun g : Aut X => F.map g.hom s) ∧
      Nat.card (Aut X) ≤ Nat.card (F.obj X) ∧
      (IsStacksGaloisObject F X ↔ Nat.card (Aut X) = Nat.card (F.obj X)) ∧
      (IsStacksGaloisObject F X ↔
        ∀ t : F.obj X, ∃ g : Aut X, F.map g.hom s = t)) ∧
    (∀ (I : Type wI) (J : Type wJ) [Finite I] [Finite J]
      (Xi : I → C) (Yj : J → C) (X Y : C)
      (ιX : ∀ i, Xi i ⟶ X) (ιY : ∀ j, Yj j ⟶ Y),
      Nonempty (IsColimit (Cofan.mk X ιX)) →
      Nonempty (IsColimit (Cofan.mk Y ιY)) →
      (∀ i, IsConnected (Xi i)) → (∀ j, IsConnected (Yj j)) →
      ∀ f : X ⟶ Y,
        ∃ (α : I → J) (component : ∀ i, Xi i ⟶ Yj (α i)),
          ∀ i, ιX i ≫ f = component i ≫ ιY (α i)) := by
  sorry

end CategoryTheory
