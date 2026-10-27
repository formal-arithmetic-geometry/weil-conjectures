/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTheoreticUnion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Closed unions are pushouts

Source: Stacks Project, Morphisms, Tag 0C4J, `lemma-scheme-theoretic-union`
(blueprint: lem-trf-closed-union-pushout).

The first statement is the pushout property in all schemes. The second states the
corresponding affine ring identity using the canonical quotient maps: a pullback
square identifies its upper left ring with the fibre product, compatibly with both
projections. No reducedness, Noetherianity, separatedness or nonemptiness is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The scheme cut out by the intersection of the two kernel ideals is the pushout
of the two closed subschemes along their scheme-theoretic intersection.
The factorization equations specify the inclusions uniquely, since `subschemeι`
is a monomorphism. `IsPushout` includes commutativity and the colimit universal
property: for every scheme T, maps to T agreeing on the pullback extend uniquely.

Source: Stacks Project, Morphisms, Tag 0C4J, `lemma-scheme-theoretic-union`
(blueprint: lem-trf-closed-union-pushout).

Proof:
1. On an affine open U = Spec R, the closed immersions have ideals I and J.
   By lem-weil-pbc-scheme-theoretic-union, the union has ring R/(I intersect J).
   By def-pc-fibre-product and lem-weil-pbc-fibre-product-affine-spectra, the
   intersection has ring (R/I) tensor_R (R/J), identified with R/(I+J) by
   [a] tensor [b] mapping to [ab], with inverse [r] mapping to [r] tensor 1.
   The maps of all four affine schemes are induced by the canonical quotients.
2. The diagonal map from R/(I intersect J) to the matching-pairs ring is injective:
   an element mapping to zero lies in both ideals. For a matching pair ([a],[b]),
   write a-b = i+j with i in I and j in J; c = a-i = b+j lifts the pair.
3. Apply lem-sfb-affine-closed-pinching-pushout to R/I -> R/(I+J) <- R/J.
   Its first arrow is surjective. Step 2 identifies its pushout scheme with the
   union over U. Thus any compatible maps to any target T extend uniquely there.
4. These inverse images of affine opens cover the union. Cover an overlap U cap V
   by affine opens B; the inverse images of B cover the corresponding overlap in
   the union. Step 3 gives agreement on each such chart, without assuming U cap V
   affine. Lem-weil-pbc-scheme-morphism-gluing gives a global extension.
5. The inclusions exist by lem-weil-pbc-scheme-theoretic-union. Commutativity holds
   on the affine cover of the intersection by the quotient formulas. The extension
   restricts to the prescribed maps on covers of both closed subschemes. Any other
   extension agrees on every affine chart by step 3, hence globally by gluing.
   This is the colimit property of def-weil-pbc-category-colimit. Zero rings and
   empty covers are allowed throughout. -/
theorem isPushout_scheme_theoretic_union
    {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ (a : Y ⟶ (i.ker ⊓ j.ker).subscheme) (b : Z ⟶ (i.ker ⊓ j.ker).subscheme),
      a ≫ (i.ker ⊓ j.ker).subschemeι = i ∧
      b ≫ (i.ker ⊓ j.ker).subschemeι = j ∧
      IsPushout (pullback.fst i j) (pullback.snd i j) a b := by
  sorry

end AlgebraicGeometry

namespace CommRingCat

/-- The affine ring identity in the closed-union pushout: R/(I intersect J) is
(R/I) times_{R/(I+J)} (R/J), with the canonical quotient maps as projections.
Here the join of ideals is their sum. A pullback square states the ring isomorphism
and compatibility with both projections, rather than just an abstract isomorphism.
Every affine chart of the scheme statement is an instance; conversely arbitrary
R, I and J occur as the chart Spec R with its quotient closed subschemes.

Source: Stacks Project, Morphisms, Tag 0C4J, `lemma-scheme-theoretic-union`,
the affine exact sequence and the cocartesian-square proof
(blueprint: lem-trf-closed-union-pushout).

Proof: The canonical map sends [r] to ([r],[r]). Its kernel is zero because r
lies in both I and J if both components vanish. For any matching pair ([a],[b]),
write a-b = i+j with i in I and j in J. Then c = a-i = b+j has those two residue
classes. Thus the map is bijective, is a ring isomorphism, and commutes with the
projections by its formula. This is step 2 of the node's proof and applies to zero
rings as well. -/
theorem isPullback_quotient_inf_sup
    (R : Type u) [CommRing R] (I J : Ideal R) :
    IsPullback
      (CommRingCat.ofHom (Ideal.Quotient.factor (inf_le_left : I ⊓ J ≤ I)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (inf_le_right : I ⊓ J ≤ J)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J))) := by
  sorry

end CommRingCat
