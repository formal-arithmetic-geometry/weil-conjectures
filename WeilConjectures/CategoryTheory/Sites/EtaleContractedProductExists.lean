/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import WeilConjectures.CategoryTheory.Sites.EtaleContractedProductUniversal

/-! # Existence of contracted products of étale torsors

## References

* Stacks Project, Tags 03AH and 03AJ, contracted-product construction in.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- The sheafified orbit quotient of a torsor and the new coefficient group is a torsor.
Source: Stacks Project, Tags 03AH and 03AJ. -/
theorem etale_contracted_product_exists (S : Scheme.{u})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') (T : Torsor G) :
    ∃ T' : Torsor G', Nonempty (ContractedProductPresentation.{u, u} S φ T T') := by
  obtain ⟨vadd, ⟨hz, ha, hn, hb, hq⟩, _⟩ := exists_contracted_product_action S φ T
  let T' : Torsor G' :=
    { sheaf := contractedOrbitSheaf S φ T
      vadd := vadd
      zero_vadd := hz
      add_vadd := ha
      map_vadd := fun f g t ↦ hn f g t
      bijective_vadd := hb
      nonemptySieve_mem := contractedOrbitSheaf_nonemptySieve_mem S φ T }
  refine ⟨T', ⟨?_⟩⟩
  exact
    { quotient := contractedOrbitQuotient S φ T
      quotient_natural := fun f t h ↦ contractedOrbitQuotient_natural S φ T f t h
      quotient_invariant := contractedOrbitQuotient_invariant S φ T
      quotient_vadd := hq
      universal := contracted_product_universal S φ T }

end CategoryTheory.Sheaf.Torsor
