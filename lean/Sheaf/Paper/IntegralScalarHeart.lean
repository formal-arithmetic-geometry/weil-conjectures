/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.IntegralTStructure

/-! # Integral finite scalar extension preserves the standard heart

Source: Bhatt--Scholze, Lemma 6.8.2(1) and Proposition 6.8.14.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Integral scalar extension takes an integral heart object into the integral heart.
Source: Bhatt--Scholze 6.8.2(1), 6.8.14; step 2 of
`lem-per-adic-common-stage-truncations` (blueprint: lem-per-adic-integral-scalar-heart).

Proof: choose an integral basis of the target valuation ring over the source valuation
ring. The coefficient inclusions on every finite quotient respect this basis and the
cofinal uniformizer filtrations. Taking their inverse limits makes the completed target
coefficient sheaf finite free over the source with its specified completed scalar map.
Ordinary extension of scalars is consequently exact: after restriction it is a finite
sum of copies of the source module, so kernels and cokernels are computed coordinatewise.
The universal K-flat derived extension is naturally isomorphic to termwise derivation
of this exact ordinary extension. Its cohomology is thus ordinary scalar extension of
source cohomology. An integral heart object has zero cohomology in every nonzero degree,
so its image has the same vanishing. The functor already restricts to the actual
constructible complete integral category by `pbcEmbeddingAmbientTensor_preserves`.
The induced integral t-structure detects this same ambient cohomology vanishing;
hence the image belongs to its heart. No levelwise truncation or Tor hypothesis is used.
The argument includes the zero object and the empty scheme. -/
theorem pbcIntegralScalarHeart
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
    (hK : (pbcIntegralTStructure X l E).heart K) :
    (pbcIntegralTStructure X l L).heart
      ((pbcEmbeddingIntegralTensor l E L i X hDim.out hInv.out).obj K) := by sorry

end AlgebraicGeometry.Scheme
