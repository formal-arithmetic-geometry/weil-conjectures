module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Relative squares and closed maps under open base restriction

Source: Stacks Project, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective`,
first sentence of the proof and its base change of the diagonal; Tags 001V and 01JR.
(blueprint: lem-sfb-open-base-relative-square-closed)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Relative self-products and their diagonals commute with base change. Over an open in the
base, they identify with the inverse-image opens; ordinary closedness of the two structure
maps survives this restriction. Further base change through the open gives the same morphism
and diagonal. All existential maps and isomorphisms below are characterized uniquely by their
projection equations: they are the canonical universal-property maps, not chosen extra data.

Source: Stacks Project, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective`, first proof sentence and
base change of the diagonal; Tags 001V and 01JR.
(blueprint: lem-sfb-open-base-relative-square-closed)

Proof:
1. For a base change `T → B`, project the relative self-product to its two copies of `A`
and to `T`. Equality in the base-changed `C` makes the two `T` maps equal and gives a map
to `A ×_C A`. This constructs the comparison with `(A ×_C A) ×_B T` using the universal
property of fibre products (`def-pc-fibre-product`).
2. Conversely, its two `A` maps together with its `T` map define two maps to `A ×_B T`.
Their images in `C ×_B T` agree, giving the inverse comparison. Both composites have the
identity projections and hence are identities by the same universal property.
3. The diagonal has both projections equal to the identity. Its comparison therefore has
`A ×_C A` projection equal to the original diagonal after the `A` projection and has the
original `T` projection. These equations identify it with the base-changed diagonal.
4. Apply `lem-weil-pbc-open-preimage-fibre-product` to `p`, `q` and the first relative-square
projection followed by `p`. Its specified projection equations identify their pullbacks
with inverse-image opens and their second projections with the restricted structure maps.
Combine with steps 1--2 for the relative square. Uniqueness also identifies the induced map.
5. For either closed structure map `r`, a closed subset of its inverse-image open has the
form `F ∩ r⁻¹(W)` with `F` closed in the whole source. Its image is `r(F) ∩ W`, closed in
`W`. Thus the two restrictions are closed; universal closedness is not needed.
6. For `k : T → W`, the iterated pullback comparison sends `((x,w),t)` to `(x,t)` and its
inverse sends `(x,t)` to `((x,k(t)),t)`, where these are universal-property morphisms.
Their composites have identity projections. The induced morphisms commute with these
comparisons because their two projections agree. The relative-square comparisons and
diagonals agree for the same reason (`def-pc-fibre-product`). -/
theorem openBaseRelativeSquareClosed {A B C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p) :
    (∀ (T : Scheme.{u}) (h : T ⟶ B),
      ∃ fT : pullback p h ⟶ pullback q h,
        fT ≫ pullback.fst q h = pullback.fst p h ≫ f ∧
        fT ≫ pullback.snd q h = pullback.snd p h ∧
        ∃ e : pullback fT fT ≅ pullback (pullback.fst f f ≫ p) h,
          e.hom ≫ pullback.fst (pullback.fst f f ≫ p) h ≫ pullback.fst f f =
            pullback.fst fT fT ≫ pullback.fst p h ∧
          e.hom ≫ pullback.fst (pullback.fst f f ≫ p) h ≫ pullback.snd f f =
            pullback.snd fT fT ≫ pullback.fst p h ∧
          e.hom ≫ pullback.snd (pullback.fst f f ≫ p) h =
            pullback.fst fT fT ≫ pullback.snd p h ∧
          pullback.diagonal fT ≫ e.hom ≫ pullback.fst (pullback.fst f f ≫ p) h =
            pullback.fst p h ≫ pullback.diagonal f ∧
          pullback.diagonal fT ≫ e.hom ≫ pullback.snd (pullback.fst f f ≫ p) h =
            pullback.snd p h) ∧
    (∀ W : B.Opens,
      ∃ fW : pullback p W.ι ⟶ pullback q W.ι,
        fW ≫ pullback.fst q W.ι = pullback.fst p W.ι ≫ f ∧
        fW ≫ pullback.snd q W.ι = pullback.snd p W.ι ∧
        (pullbackRestrictIsoRestrict p W).hom ≫ (p ⁻¹ᵁ W).ι =
          pullback.fst p W.ι ∧
        (pullbackRestrictIsoRestrict q W).hom ≫ (q ⁻¹ᵁ W).ι =
          pullback.fst q W.ι ∧
        (pullbackRestrictIsoRestrict p W).hom ≫ morphismRestrict p W =
          pullback.snd p W.ι ∧
        ∃ dW : pullback fW fW ≅ ((pullback.fst f f ≫ p) ⁻¹ᵁ W).toScheme,
          dW.hom ≫ ((pullback.fst f f ≫ p) ⁻¹ᵁ W).ι ≫ pullback.fst f f =
            pullback.fst fW fW ≫ pullback.fst p W.ι ∧
          dW.hom ≫ ((pullback.fst f f ≫ p) ⁻¹ᵁ W).ι ≫ pullback.snd f f =
            pullback.snd fW fW ≫ pullback.fst p W.ι ∧
          dW.hom ≫ morphismRestrict (pullback.fst f f ≫ p) W =
            pullback.fst fW fW ≫ pullback.snd p W.ι ∧
          (IsClosedMap p.base ∧ IsClosedMap (pullback.fst f f ≫ p).base →
            IsClosedMap (morphismRestrict p W).base ∧
            IsClosedMap (morphismRestrict (pullback.fst f f ≫ p) W).base) ∧
          ∀ (T : Scheme.{u}) (k : T ⟶ W.toScheme),
            ∃ (a : pullback (pullback.snd p W.ι) k ≅ pullback p (k ≫ W.ι))
              (c : pullback (pullback.snd q W.ι) k ≅ pullback q (k ≫ W.ι))
              (F : pullback p (k ≫ W.ι) ⟶ pullback q (k ≫ W.ι))
              (g : pullback (pullback.snd p W.ι) k ⟶ pullback (pullback.snd q W.ι) k),
              a.hom ≫ pullback.fst p (k ≫ W.ι) =
                pullback.fst (pullback.snd p W.ι) k ≫ pullback.fst p W.ι ∧
              a.hom ≫ pullback.snd p (k ≫ W.ι) = pullback.snd (pullback.snd p W.ι) k ∧
              c.hom ≫ pullback.fst q (k ≫ W.ι) =
                pullback.fst (pullback.snd q W.ι) k ≫ pullback.fst q W.ι ∧
              c.hom ≫ pullback.snd q (k ≫ W.ι) = pullback.snd (pullback.snd q W.ι) k ∧
              F ≫ pullback.fst q (k ≫ W.ι) = pullback.fst p (k ≫ W.ι) ≫ f ∧
              F ≫ pullback.snd q (k ≫ W.ι) = pullback.snd p (k ≫ W.ι) ∧
              g ≫ pullback.fst (pullback.snd q W.ι) k =
                pullback.fst (pullback.snd p W.ι) k ≫ fW ∧
              g ≫ pullback.snd (pullback.snd q W.ι) k =
                pullback.snd (pullback.snd p W.ι) k ∧
              g ≫ c.hom = a.hom ≫ F ∧
              ∃ d : pullback g g ≅ pullback F F,
                d.hom ≫ pullback.fst F F = pullback.fst g g ≫ a.hom ∧
                d.hom ≫ pullback.snd F F = pullback.snd g g ≫ a.hom ∧
                pullback.diagonal g ≫ d.hom = a.hom ≫ pullback.diagonal F) := by
  sorry

end AlgebraicGeometry
