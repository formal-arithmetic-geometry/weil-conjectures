/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayerIntegral
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessPadicAlgCl
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Deligne's induction for the finiteness of nearby cycles

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, and let `Ψ` be the
geometric nearby cycles of the standard model of `𝔸ⁿ⁺¹_S` (`NearbyCyclesModel.affineSpaceModel`).
Deligne proves that `Ψ` preserves bounded constructible complexes by induction on the relative
dimension (SGA 4½, [Th. finitude], proof of Thm. 3.2), using the coordinate generic slices
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`, `K = k'(x)^alg` (`AlgebraicGeometry.affineSpaceSlice`), with
special fibres `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` (`AlgebraicGeometry.affineSpaceSliceSpecial`), the
geometric generic fibres of the coordinate projections of the special fibre. The two steps are:

* **slices** (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`):
  the pullback exchange `α : Lhᵢ,ₛ^* Ψ B ⟶ Ψ_K (Lhᵢ^* B)` of the morphism of geometric models
  over the slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism, so `Lhᵢ,ₛ^* Ψ B`
  is a retract of the nearby cycles over the trait `Spec K⟦t⟧`
  (`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`).
  The slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` is (up to a purely inseparable extension of the residue field) the
  completion of the strict localization `S'` of `𝔸¹_S` at the generic point of
  its special fibre. The nearby cycles over `S` of the base change to `S'` are the invariants
  `(Ψ_{S'})^P` of the nearby cycles over `S'` under the kernel `P` of the surjection of inertia
  groups `I_{S'} ⟶ I_S`, a pro-`p` group (SGA 4½, [Th. finitude], Lemme 3.3), and the nearby
  cycles do not change under the extension of traits `S' ⟶ Spec K⟦t⟧` (loc. cit., 3.7). Since
  `P` is pro-`p` and `p ≠ ℓ`, the averaging over `P` splits the inclusion of the invariants.
* **criterion**
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`): if the
  restrictions `Lhᵢ,ₛ^* Ψ B` to all the coordinate slices are bounded constructible, then so is
  `Ψ B`. It is stated, and needed, only for the extensions by zero `v_! L` of lisse sheaves on
  the generic fibre to which the dévissage reduces, in the case not covered by the proper
  exchange (the support meets the special fibre and is not quasi-finite over `S`). The points of
  `𝔸ⁿ⁺¹_{k'}` outside the images of all the slices `hᵢ,ₛ` are the closed points; by Deligne's
  argument (loc. cit., proof of 3.2; see also the ind-holonomic analogue in D. Abe, *Around the
  nearby cycle functor for arithmetic 𝒟-modules*, §2) the cohomology sheaves of `Ψ B` are
  extensions of sums of skyscrapers at closed points by constructible sheaves, and the skyscraper
  parts are finite by the finiteness of
  `RΓ(ℙⁿ⁺¹_s, Ψ_{ℙⁿ⁺¹} j_! B) = RΓ(ℙⁿ⁺¹_η̄, j_! B)` (proper exchange and Deligne's finiteness
  over the field `η̄`).

Together with the trait case `n = 0`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`), the dévissage to
lisse sheaves and the proper-exchange cases, they prove the finiteness theorem by induction on `n`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj`).

## Implementation notes

The slice step is proved from Th. finitude 3.7 and the averaging splitting (M2)
(`WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayerIntegral`). Deligne's
argument for the criterion needs that the cohomology sheaves of `Ψ B` are ind-constructible,
which holds for every étale sheaf with torsion coefficients (Stacks 03SA) but has no analogue for
pro-étale `ℚ̄_ℓ`-sheaves. The criterion is therefore deduced from the finiteness theorem itself,
which is proved first with the finite coefficients `𝔽_E`, by Deligne's induction with the
closed-point criterion (`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsion`),
and then for `ℚ̄_ℓ` through integral models and the integral criterion for derived complete
`𝒪_E`-complexes (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`,
Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
