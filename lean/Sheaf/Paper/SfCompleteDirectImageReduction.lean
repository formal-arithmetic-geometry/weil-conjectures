/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfDerivedDirectImage

/-! # Complete direct images and their canonical finite reductions

Source: Stacks Project, Tags 099N and 0944; Bhatt--Scholze, Lemmas 6.5.9(2)
and 6.5.11(3). (blueprint: lem-sf-complete-direct-image-reduction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Ordinary pushforward of a complete complex is represented by the prescribed finite
image tower, and its canonical projection adjuncts identify all finite reductions.
No constructibility, finite cohomological dimension, or geometric base is needed.

Source: Stacks Project, Tags 099N(3),(4) and 0944; Bhatt--Scholze,
Lemmas 6.5.9(2) and 6.5.11(3).
(blueprint: lem-sf-complete-direct-image-reduction).

Proof: Put A = O_E, I = (uniformizer). The DVR coefficient theorem gives the free
resolution [A --uniformizer^(n+1)--> A] of A/I^(n+1), so every positive quotient is
perfect. The normalized integral coefficient presentation comparison identifies its
finite quotient sheaves, completed ring, quotient maps, scalar adjunction units and
Roos product maps with the detailed coefficient presentation used here.
Apply the completed direct-image/limit comparison to the reduction tower of K.
Restriction of scalars commutes with direct image by ringed-topos composition;
the structural maps agree after every finite projection and hence agree. Its derived
comparison is the specified sfDerivedRestrictionComparison, by its K-injective
normalization. Thus pushing the augmented Roos triangle for K gives a Roos triangle
for sfDirectImageTerm, with projections F(unit_n) followed by that comparison.
The perfect-quotient projection formula makes the adjuncts of these projections
invertible. The tower projection compatibility identifies the completion unit of F(K)
with F of the completion unit of K followed by the direct-image/limit isomorphism.
Consequently F(K) is complete. Rotate its Roos triangle and the prescribed triangle
of L; the identity on the two product terms extends to a triangle morphism.
The triangle five lemma makes the resulting L -> F(K) an isomorphism, commuting
with every projection. Completeness transports across this isomorphism. Naturality
of the scalar adjunction identifies each comparison for L with scalar extension of
this isomorphism followed by the perfect-quotient comparison for F(K). Hence it is
invertible. This proves the claims for every chosen Roos triangle, including zero
complexes and empty schemes, without choosing a functorial cone. -/
theorem sfCompleteDirectImage_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) :
    IsSfDerivedComplete l E Y L.obj ∧
      ∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n) := by
  sorry

end WeilConjectures
