/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Sheaf.CategoryTheory.NaturalTransportInduction
import Sheaf.CategoryTheory.SimplicialOperatorsReconstruction

/-! # Counit words augment a supplied simplicial resolution

Source: Stacks Project, Tag 0G5N, `lemma-godement`, final augmentation paragraph;
Tag 016B(3), `lemma-characterize-simplicial-object`; and `example-godement-functorial`
following Tag 0G5N (blueprint: lem-trf-comonad-counit-augmentation).

## Main definitions

* `CategoryTheory.NaturalTransport.counitWord`: the horizontal word of counits,
  including the empty word.

## Main statements

* `CategoryTheory.NaturalTransport.counit_word_augmentation`: the face and degeneracy
  identities, augmentation, and functorial evaluation, assuming only one counit identity
  and an already supplied simplicial object.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.NaturalTransport

/-- The horizontal composite of `k` copies of `e`, with the identity at `k = 0`.
The argument order of Mathlib's `NatTrans.hcomp` is inner functor, then outer functor.
The unitor identifies the composite of two identity functors with the identity.
Thus the source's `A_n` is `counitWord T e (n + 1)`.

Source: Stacks Project, Tag 0G5N, `lemma-godement`, final augmentation paragraph,
expanded to all degrees using Tag 016B(3)
(blueprint: lem-trf-comonad-counit-augmentation). -/
def counitWord {C : Type u} [Category.{v} C] (T : C ⥤ C) (e : T ⟶ 𝟭 C) :
    (k : ℕ) → (power T k ⟶ 𝟭 C)
  | 0 => 𝟙 (𝟭 C)
  | k + 1 => NatTrans.hcomp (counitWord T e k) e ≫ (Functor.rightUnitor (𝟭 C)).hom

/-- Counit words commute with the prescribed faces and degeneracies of a supplied
simplicial object of endofunctors, form an augmentation, and evaluate functorially.
`hB` identifies the degree functors, and heterogeneous equalities identify the operators
without introducing arbitrary comparison isomorphisms for parenthesized powers.
The equality with `B.flip` specifies every evaluated term, simplicial operator, and
map on the variable object; the equality with the identity functor specifies the
augmentation targets and their maps.

Source: Stacks Project, Tag 0G5N, `lemma-godement`, final augmentation paragraph;
Tag 016B(3), `lemma-characterize-simplicial-object`; `example-godement-functorial`
following Tag 0G5N (blueprint: lem-trf-comonad-counit-augmentation).

Proof plan:
1. Set `R_k = counitWord T e k`. Horizontal composition gives
   `R_(k+1) = e star R_k`, hence `R_(n+1) = A_n` and `A_0 = e`.
   Naturality follows from horizontal composition; naturality of `e` also gives
   `R_(k+1),x = R_k,x` after `e_(T^k x)`.
2. Induct on `p` to obtain `R_(p+q+1),x = R_(p+q),x` after
   `T^p(e_(T^q x))`. At `p = 0` use the last equality of Step 1.
   For the successor apply `T`, then compose with `e_x` and use the recursion.
   Substituting `p = i`, `q = n-i` proves every face compatibility.
3. The given counit identity gives `d_i^(n+1)` after `s_i^n` equal to the identity:
   evaluate the identity at `T^(n-i) x` and apply `T^i`.
   Combine this with Step 2 to prove every degeneracy compatibility, including `n = 0`.
4. Apply the morphism clause of `simplicialObject_reconstruction` to `B` and the
   constant simplicial object at the identity functor. Steps 2 and 3 give precisely
   its two compatibility requirements, producing the augmentation with components `A_n`.
5. Evaluate `B` and this augmentation at `x`. Functoriality and naturality give an
   augmented simplicial object with target `x` and augmentation components `(A_n)_x`.
6. For `f : x ⟶ y`, use degree maps `B_n.map f` and target map `f`. Naturality of
   every operator and of `A_n` gives their compatibility. Functoriality of each `B_n`
   and of the identity target assignment proves the functor laws. This constructs `E`.
   No second counit identity or coassociativity is used. -/
theorem counit_word_augmentation
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) (e : T ⟶ 𝟭 C) (c : T ⟶ T ⋙ T)
    (hc : c ≫ Functor.whiskerLeft T e ≫ (Functor.rightUnitor T).hom = 𝟙 T)
    (B : SimplicialObject (C ⥤ C))
    (hB : ∀ n : ℕ, B.obj (Opposite.op (SimplexCategory.mk n)) = power T (n + 1))
    (hd : ∀ (n : ℕ) (i : Fin (n + 2)), HEq (B.δ i)
      (Functor.whiskerLeft (power T (n + 1 - i.val))
        (Functor.whiskerRight e (power T i.val))))
    (hs : ∀ (n : ℕ) (i : Fin (n + 1)), HEq (B.σ i)
      (Functor.whiskerLeft (power T (n - i.val))
        (Functor.whiskerRight c (power T i.val)))) :
    HEq (counitWord T e 1) e ∧
    (∀ (n : ℕ) (i : Fin (n + 2)),
      B.δ i ≫ eqToHom (hB n) ≫ counitWord T e (n + 1) =
        eqToHom (hB (n + 1)) ≫ counitWord T e (n + 2)) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)),
      B.σ i ≫ eqToHom (hB (n + 1)) ≫ counitWord T e (n + 2) =
        eqToHom (hB n) ≫ counitWord T e (n + 1)) ∧
    ∃ α : B ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C),
      (∀ n : ℕ, α.app (Opposite.op (SimplexCategory.mk n)) =
        eqToHom (hB n) ≫ counitWord T e (n + 1)) ∧
      ∃ E : C ⥤ SimplicialObject.Augmented C,
        E ⋙ SimplicialObject.Augmented.drop = B.flip ∧
        E ⋙ SimplicialObject.Augmented.point = 𝟭 C ∧
        ∀ (x : C) (n : ℕ),
          HEq ((E.obj x).hom.app (Opposite.op (SimplexCategory.mk n)))
            ((counitWord T e (n + 1)).app x) := by
  sorry

end CategoryTheory.NaturalTransport
