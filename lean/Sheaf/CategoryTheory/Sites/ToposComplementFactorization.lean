/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal

/-!
# Open and closed complements of a subterminal object

Source: Stacks Project, Sites, Tags 08LW, 08LY, 08LZ and 08M0
(blueprint: lem-trf-topos-complement-factorization).

Full faithfulness on geometric-morphism categories is expressed as bijectivity of right
whiskering on all direct-image natural transformations. The essential image is expressed by
existence of a factor and a direct-image natural isomorphism. Together these are exactly an
equivalence onto the indicated full subcategory, including unique compatible isomorphisms.
-/

@[expose] public section

universe w u v uH vH

namespace CategoryTheory

open Limits

/-- The objects of the complementary closed subtopos: the projection `u × A → u` is an
isomorphism. The symmetry of binary products identifies this with `A × u → u`.
Source: Stacks Project, Sites, Tag 08LY
(blueprint: lem-trf-topos-complement-factorization). -/
def closedComplementObjects {E : Type u} [Category.{v} E] [HasBinaryProducts E]
    (u : E) : ObjectProperty E :=
  fun A ↦ IsIso (prod.fst : u ⨯ A ⟶ u)

/-- A subterminal object determines complementary open and closed embeddings, with the
universal factorization properties on objects and all direct-image 2-morphisms.
Source: Stacks Project, Sites, Tags 08LW, 08LY, 08LZ and 08M0
(blueprint: lem-trf-topos-complement-factorization).

Proof plan:
1. Use `lem-trf-topos-localization-site-presentation` to present the topos on a small
   subcanonical finite-limit site, with `u` represented by a mono `U → X`, and the slice by
   the slice site. Transport back after the following constructions.
2. `lem-trf-slice-subtopos-site-presentation` gives the restriction/direct-image adjunction.
   Subterminality identifies `W → W × U` with an isomorphism over `U`, so its graph counit
   is invertible. Thus the slice direct image is fully faithful (Tag 08LW).
3. `lem-trf-closed-complement-site-construction` gives a fully faithful geometric direct
   image whose essential image is precisely `closedComplementObjects u`. Replace its source
   by this full subcategory to obtain the geometric morphism `k` with inclusion direct image.
   Tags 08LZ and 08M0 identify this as the complementary closed subtopos.
4. In a sheaf topos the initial sheaf has singleton sections on empty-covered objects and
   empty sections elsewhere. The empty-family sheaf condition and coordinatewise products
   show `0 × B ≅ 0`, also after transport along equivalences.
5. For a closed object `C`, invertibility of `u × C → u` gives exactly one map `u → C`.
   Adjunction makes `k.inverse.obj u` initial. Subterminality makes `j.inverse.obj u` terminal.
6. If `a.inverse.obj u` is initial, adjunction gives a unique map `u → a.direct.obj B`.
   Its graph inverts the projection: the other composite is checked after transposition,
   where the source is `a.inverse(u × a.direct B) ≅ 0 × a.inverse(a.direct B) ≅ 0`.
   Hence `a.direct` lands in the closed full subcategory.
7. Define the closed factor's direct image by this restriction, and inverse image by
   `inclusion ⋙ a.inverse`. The original Hom adjunction and full-subcategory identification
   give natural bijections; `lem-weil-pbc-adjunction-of-natural-bijection` gives the adjunction.
   The inclusion is right adjoint to `k.inverse`, so it preserves finite limits by
   `lem-weil-pbc-right-adjoint-preserves-limits`; the new inverse image is left exact.
   `lem-weil-pbc-conjugate-iso-unit-equation` constructs the compatible composite comparison
   from equality of direct images.
8. Conversely a closed factor sends `u` to an initial object, since left adjoints preserve
   initial objects. Full faithfulness of the inclusion lifts every direct-image natural
   transformation uniquely; naturality is checked after the faithful inclusion. This gives
   the closed equivalence and unique compatible isomorphisms.
9. If `a.inverse.obj u` is terminal, define the open factor's inverse image on `(V → u)`
   by `a.inverse.obj V`, and direct image by `(u × a.direct.obj B → u)`. Pairing with the
   structure map and the original adjunction give natural Hom bijections. The same
   natural-bijection lemma supplies its adjunction. It preserves terminal objects by the
   hypothesis and pullbacks by the underlying slice pullback calculation; hence finite limits.
10. The open composite comparison is `a.inverse(A × u) ≅ a.inverse A`. Apply the conjugate
    isomorphism lemma to opposite adjunctions to obtain the direct-image comparison and unit
    compatibility. Conversely an open factor sends `u` to a terminal object by left exactness.
11. Full faithfulness of `j.direct` lifts all direct-image transformations uniquely,
    including their naturality, identities and compositions. This proves the open equivalence
    and unique compatible isomorphisms. Transport everything to the original presentation.
-/
theorem topos_complement_factorization {E : Type u} [Category.{v} E]
    (hE : IsGrothendieckTopos.{w} E) (u : E) (hu : IsSubterminal u) :
    ∃ (products : HasBinaryProducts E),
      IsGrothendieckTopos.{w} (@closedComplementObjects E _ products u).FullSubcategory ∧
      IsGrothendieckTopos.{w} (Over u) ∧
      ∃ (j : GeometricMorphism (Over u) E)
        (k : GeometricMorphism (@closedComplementObjects E _ products u).FullSubcategory E),
        Nonempty (j.inverse ≅ @Over.star E _ u products) ∧
        Nonempty (k.direct ≅ (@closedComplementObjects E _ products u).ι) ∧
        Nonempty j.direct.FullyFaithful ∧ Nonempty k.direct.FullyFaithful ∧
        ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
          ((∀ (a : GeometricMorphism H E),
              (∃ (b : GeometricMorphism H
                (@closedComplementObjects E _ products u).FullSubcategory),
                Nonempty ((b.comp k).direct ≅ a.direct)) ↔
              Nonempty (IsInitial (a.inverse.obj u))) ∧
            (∀ (b d : GeometricMorphism H
                (@closedComplementObjects E _ products u).FullSubcategory),
              Function.Bijective
                (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ k.direct))) ∧
          ((∀ (a : GeometricMorphism H E),
              (∃ (b : GeometricMorphism H (Over u)),
                Nonempty ((b.comp j).direct ≅ a.direct)) ↔
              Nonempty (IsTerminal (a.inverse.obj u))) ∧
            (∀ (b d : GeometricMorphism H (Over u)),
              Function.Bijective
                (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ j.direct))) := by
  sorry

end CategoryTheory
