/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.CategoryTheory.Sites.ContractedProductPresentation
import WeilConjectures.CategoryTheory.Sites.Torsor

/-! # Existence of contracted products of étale torsors

Source: Stacks Project, Tags 03AH and 03AJ, contracted-product construction in
lem-sc-etale-torsor-pushout-extension
(blueprint: lem-sc-etale-contracted-product-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- The sheafified orbit quotient of a torsor and the new coefficient group is a torsor.
Source: Stacks Project, Tags 03AH and 03AJ; the contracted-product construction of
lem-sc-etale-torsor-pushout-extension.
(blueprint: lem-sc-etale-contracted-product-exists)

Proof: Form the orbit presheaf of T × G' under (g,t,h) ↦ (g +ᵥ t,h - φ(g)) and sheafify.
The quotient maps are natural and invariant. Translation in the second factor commutes
with the antidiagonal action, hence descends and then extends to sheafification. On any
cover trivializing T by a section t₀, each orbit has the unique representative (t₀,h);
thus the quotient sheaf is locally G', with its translation action. This proves local
nonemptiness and simple transitivity, so the quotient is a G'-torsor. An invariant natural
map to any sheaf factors uniquely through the orbit presheaf and then uniquely through
sheafification; these two universal properties give ContractedProductPresentation. -/
theorem etale_contracted_product_exists (S : Scheme.{u})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') (T : Torsor G) :
    ∃ T' : Torsor G', Nonempty (ContractedProductPresentation.{u, u} S φ T T') := by sorry

end CategoryTheory.Sheaf.Torsor
