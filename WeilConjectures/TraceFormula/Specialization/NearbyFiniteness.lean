/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.RetractPadicAlgCl
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFiniteClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice

/-!

# Deligne's finiteness theorem for nearby cycles

Let `M` be a model of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.IsTraitModel`), `k'` separably closed of characteristic `p ≠ ℓ`, with total
space `𝒳`, geometric generic fibre `j : 𝒳_η̄ ⟶ 𝒳` and special fibre `i : X' ⟶ 𝒳`. Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) says that the geometric nearby cycles
`Ψ = Li^* Rj_* Lj^*` (the nearby cycles of the geometric model `M.geometric`) carry bounded
constructible `ℚ̄_ℓ`-complexes on `𝒳` to bounded constructible complexes on `X'`
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). Hence the nearby cycles
`Ψ = Li^* Rj_* Lε^*` of a model whose identification factors as `ε = j ≫ e` through the total
space preserve bounded constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`): `Lε^* ≅ Lj^* Le^*`, and the
pullback `Le^*` preserves bounded constructible complexes.

Following Deligne's proof, the theorem is reduced to the affine spaces `𝔸ⁿ_S`, where it is
proved by induction on `n`:
* **locality**: bounded constructibility on the special fibre is local on a finite open cover
  (`ProEtale.CondensedRing.boundedConstructible_of_openCover`), and nearby cycles commute with
  restriction to the members `V` of a finite affine open cover of `𝒳`
  (`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`), which reduces to affine `𝒳`
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_isAffine`);
* **closed embedding**: an affine `𝒳` embeds as a closed subscheme `c : 𝒳 ⟶ 𝔸ⁿ_S`; by the proper
  exchange `Ψ_{𝔸ⁿ} Rc_* ≅ Rc_{s*} Ψ_𝒳` (blueprint `det-sp-nearby-cycles-exchanges` (2),
  `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), the full faithfulness of
  `Rc_{s*}` and the preservation of bounded constructibility by `Rc_*`
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`),
  this reduces to `𝒳 = 𝔸ⁿ_S` with its standard model `NearbyCyclesModel.traitStdModel`
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj`);
* **induction on `n`**, for all separably closed fields `k'` at once
  (`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice`): for `n = 0` the nearby
  cycles of the trait itself are computed directly on the pro-étale site
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`); for `n + 1`,
  the restrictions of `Ψ B` to the coordinate generic slices `𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`,
  `K = k'(x)^alg`, are retracts of the nearby cycles over the trait `Spec K⟦t⟧` of the pullbacks
  of `B` to `𝔸ⁿ_{K⟦t⟧}`
  (`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`),
  bounded constructible by induction and closure under retracts
  (`ProEtale.boundedConstructible_of_retract_padicAlgClRingObj`);
* **dévissage**, inside the induction step: along the truncation triangles and by noetherian
  induction along the open–closed triangles, to the extensions by zero `v_! L` of lisse sheaves
  along locally closed immersions into the generic or the special fibre
  (`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`). The nearby cycles
  vanish if the support misses the generic fibre or its closure misses the special fibre
  (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`), the quasi-finite case reduces
  to the trait by the proper exchange
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite`),
  and Deligne's criterion on the slices
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`) treats the
  remaining case.

## Implementation notes

The comparison with the slices (SGA 4½, [Th. finitude], Lemme 3.3 and 3.7) is proved in
`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice`. Deligne's criterion on the
slices (loc. cit., proof of Thm. 3.2) needs the ind-constructibility of torsion étale sheaves,
which has no analogue for pro-étale `ℚ̄_ℓ`-sheaves; it is deduced there from the finiteness
theorem on `𝔸ⁿ_S`, proved first with the finite coefficients `𝔽_E` by Deligne's induction
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`) and then for
`ℚ̄_ℓ` through integral models
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`).
No blueprint node states the finiteness theorem: the blueprint uses it without a node
in the proofs of `sk-prop-tf-nearby-duality-foundation` ("bounded constructible by the finiteness
theorem for nearby cycles") and `det-sp-constant-family-vanishing` ("an exact functor with
bounded constructible values"). The reductions also use the proper exchange (blueprint
`det-sp-nearby-cycles-exchanges` (2),
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
