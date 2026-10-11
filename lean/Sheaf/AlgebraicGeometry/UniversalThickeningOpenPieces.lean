/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# Open pieces of universal first order thickenings

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
the general remarks preceding the affine case
(blueprint: lem-weil-pbc-universal-thickening-open-pieces).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restriction of a first order thickening, restriction of a universal thickening to
opens of source and base, and enlargement of an open base containing the image.
In the first clause, for any structure morphism `b : T' ⟶ X`, the restricted structure
morphism is `W'.ι ≫ b`; the source is over `X` by composition. The equality on affine
opens expresses restriction of the defining ideal sheaf, in Mathlib's ideal-sheaf data.

Source: Stacks Project, proof of Lemma 37.7.1 (Tag 04F3), general remarks
(blueprint: lem-weil-pbc-universal-thickening-open-pieces).

Proof:
1. Apply lem-weil-pbc-thickening-open-restriction to `iT` and `W'`, with the whole
   base as its open. The restricted immersion is closed, its ideal is the restricted
   ideal, and this ideal still has square zero. This proves the first clause over any
   base, using def-sbc-first-order-thickening.
2. A first order thickening is a homeomorphism on underlying spaces. The image of
   each open `W` is open and is its unique inverse under preimage. This also supplies
   the unique open `V'` corresponding to `V` in the second clause.
3. Every point of `V'` is `i(v)` with `v` in `V`. Since `i ≫ h' = h`, its image
   under `h'` lies in `U`. Factor the restricted maps through the opens by
   lem-weil-pbc-morphism-factors-through-open-subscheme; restriction of the thickening
   gives a first order thickening of `V` over `U`, compatible with the restricted `h`.
4. Given a test thickening over `U` and a map to `V`, compose with the inclusions to
   obtain a test over `X`. Apply def-weil-pbc-universal-first-order-thickening to get
   the unique extension into `Z'`. Surjectivity on points of the test thickening
   places its image in `V'`, so it factors uniquely through `V'`. Cancel the open
   inclusions to verify its two required compatibilities over `U`.
5. Two such extensions into `V'` become extensions into `Z'`; universal uniqueness
   makes them equal after inclusion, and cancellation of that inclusion proves
   uniqueness into `V'`. This proves universality of the restricted thickening.
6. For enlargement of the base, the immersion and its square-zero ideal are unchanged;
   composing the structure morphism with `U.ι` makes a thickening over `X` for `h`.
7. In any test over `X` mapping to `Z`, surjectivity on points of its immersion and
   the containment of `h(Z)` in `U` force the structure map of the test to factor
   through `U`. Cancel `U.ι` to verify the compatibility, then apply universality
   over `U` to obtain the required extension over `X`.
8. Any other extension over `X` is over `U` after cancelling `U.ι`, and uniqueness
   over `U` identifies the two. This proves the third clause. -/
theorem universalFirstOrderThickening_open_pieces {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (∀ {T T' : Scheme.{u}} (iT : T ⟶ T') (_b : T' ⟶ X),
      IsFirstOrderThickening iT →
      (∀ W' : T'.Opens,
        IsFirstOrderThickening (iT ∣_ W') ∧
          ∀ Q : W'.toScheme.affineOpens,
            (iT ∣_ W').ker.ideal Q =
              iT.ker.ideal ⟨W'.ι ''ᵁ Q, Q.2.image_of_isOpenImmersion W'.ι⟩) ∧
      (∀ W : T.Opens, ∃! W' : T'.Opens, iT ⁻¹ᵁ W' = W)) ∧
    (∀ {Z' : Scheme.{u}} (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h' →
      ∀ (V : Z.Opens) (U : X.Opens), V ≤ h ⁻¹ᵁ U →
        ∃ V' : Z'.Opens, i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          ∃ (iV : V.toScheme ⟶ V'.toScheme) (hV : V.toScheme ⟶ U.toScheme)
            (hV' : V'.toScheme ⟶ U.toScheme),
            iV ≫ V'.ι = V.ι ≫ i ∧ hV ≫ U.ι = V.ι ≫ h ∧
              hV' ≫ U.ι = V'.ι ≫ h' ∧ IsUniversalFirstOrderThickening hV iV hV') ∧
    (∀ (U : X.Opens) (hU : Z ⟶ U.toScheme), hU ≫ U.ι = h →
      ∀ {Z' : Scheme.{u}} (i : Z ⟶ Z') (hU' : Z' ⟶ U.toScheme),
        IsUniversalFirstOrderThickening hU i hU' →
          IsUniversalFirstOrderThickening h i (hU' ≫ U.ι)) := by
  sorry

end AlgebraicGeometry
