/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.Paper.EtaleHypercover
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Products of étale hypercovers

Source: Stacks Project, Hypercoverings, Lemma 01GI (lemma-product-hypercoverings),
with the covering argument of Lemma 01GH (lemma-funny-gamma).
(blueprint: lem-weil-pbc-hypercover-product)
-/

universe uP

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The product in simplicial étale `X`-schemes is again a hypercover.
This product is computed termwise; products in `X.Etale` are scheme-theoretic fibre
products over `X`. Its projections `prod.fst U V` and `prod.snd U V` are natural
transformations, hence morphisms of augmented simplicial `X`-schemes.
Source: Stacks Project, Hypercoverings, Lemmas 01GI and 01GH.

Proof: (1) Fibre products in the small étale site exist. The termwise product has
induced faces and degeneracies; their identities and the naturality of its projections
follow from the universal property of fibre products [def-pc-fibre-product].
(2) By [lem-weil-pbc-matching-object-fibre-product], its matching scheme is the product
of the matching schemes, and its matching arrow is the product of their matching arrows.
At degree zero this is the augmentation to `X`.
(3) Factor that arrow as the product of the first matching arrow with the identity,
followed by the product of the identity with the second matching arrow. Each factor
is a base change of a surjective étale arrow, so is surjective étale by
[lem-weil-pbc-etale-covering-base-change].
(4) Apply [lem-weil-pbc-etale-covering-composition] to these two factors, then compose
with the matching-scheme isomorphism of step (2). This gives the covering condition
in every degree. The simplicial object and its two projections were supplied in step (1).
(blueprint: lem-weil-pbc-hypercover-product) -/
theorem isEtaleHypercover_prod (X : Scheme.{uP}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : SimplicialObject X.Etale) (hU : IsEtaleHypercover U)
    (hV : IsEtaleHypercover V) : IsEtaleHypercover (U ⨯ V) := sorry

end AlgebraicGeometry
