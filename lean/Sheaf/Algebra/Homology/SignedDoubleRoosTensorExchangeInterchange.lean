/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions

/-! Signed double Roos interchange and tensor augmentation coherence. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.SignedDoubleRoos

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r})

/-- The strict signed interchange of two Roos directions, with both evaluation squares.

Source: Stacks Tags 014E and 0941; steps 1--4 of the coordinate calculation in
`lem-sp-signed-double-roos-tensor-exchange`
(blueprint: lem-sp-signed-double-roos-interchange-core).

Proof: identify the two orders of countable products by their projections. The
product universal property also identifies a product of binary biproducts with
the binary biproduct of the products. Let A = 1 - s_n and B = 1 - s_j on the
common product; the strict double tower has AB = BA. In Roos coordinate order
(0,0), (0,1), (1,0), (1,1), the differential is
(da, -db - Ba, -dc - Aa, dh + Bc - Ab). Send (a,b,c,h) to (a,c,b,-h), after
interchanging the product indices. Applying the target differential, with A and B
exchanged, gives (da,-dc-Aa,-db-Ba,-dh-Bc+Ab), which is also the image of the
source differential. Thus this is a chain map. The reversed prescription is its
inverse. Projection tests prove naturality, since component maps commute with
permutation and negation. The coordinate formula has a minus sign precisely
when both Boolean degrees are true. Evaluation in the n direction keeps the
coordinates with n degree zero, and evaluation in the j direction keeps those
with j degree zero. Neither sees the negated doubly shifted coordinate, so the
same projection tests prove the two strict evaluation equalities. -/
theorem signed_double_roos_interchange_core :
    ∃ β : rows R ≅ columns R,
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ),
        (β.hom.app X).f k ≫ columnCoordinate R X p q k n j =
          if p && q then -rowCoordinate R X p q k n j
          else rowCoordinate R X p q k n j) ∧
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (n : ℕ),
        β.hom.app X ≫ (roos R).map (innerEvaluation R X.flip n) =
          evaluation R (X ⋙ roos R) n) ∧
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (j : ℕ),
        β.hom.app X ≫ evaluation R (X.flip ⋙ roos R) j =
          (roos R).map (innerEvaluation R X j)) := by
  sorry

end CategoryTheory.SignedDoubleRoos
