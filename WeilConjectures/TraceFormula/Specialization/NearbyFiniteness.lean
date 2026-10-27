/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.RetractPadicAlgCl
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFiniteClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice

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
  (`ProEtale.boundedConstructible_of_retract_padicAlgClRingObj`), and Deligne's criterion
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_slices`) concludes.

## Unfinished input

The two steps of the induction, the comparison with the slices (SGA 4½, [Th. finitude],
Lemme 3.3 and 3.7) and Deligne's criterion on the slices (loc. cit., proof of Thm. 3.2), are
`sorry`ed in `WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice`; see its module
docstring. No blueprint node states the finiteness theorem: the blueprint uses it without a node
in the proofs of `sk-prop-tf-nearby-duality-foundation` ("bounded constructible by the finiteness
theorem for nearby cycles") and `det-sp-constant-family-vanishing` ("an exact functor with
bounded constructible values"). The reductions also use the proper exchange (blueprint
`det-sp-nearby-cycles-exchanges` (2), `sorry`ed in
`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`).

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

/-- **Deligne's finiteness theorem for nearby cycles on an affine space** (SGA 4½,
[Th. finitude], Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): over the strictly
henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the geometric nearby
cycles of the standard model of `𝔸ⁿ_S` preserve bounded constructible complexes.

Deligne's induction on `n`, for all separably closed fields `k'` at once: for `n = 0`,
`𝔸⁰_S ⟶ S` is an isomorphism and the nearby cycles of the trait are computed directly
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`). For `n + 1`, by
Deligne's criterion (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_slices`)
it suffices that the restrictions `Lhᵢ,ₛ^* Ψ B` to the coordinate generic slices of the special
fibre are bounded constructible; they are retracts
(`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`) of the nearby
cycles over the trait `Spec K⟦t⟧`, `K = k'(x)^alg`, of the pullbacks `Lhᵢ^* B` to `𝔸ⁿ_{K⟦t⟧}`,
which are bounded constructible by induction. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj (n : ℕ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' n).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  induction n generalizing k' with
  | zero => exact boundedConstructible_nearbyCycles_affineSpaceModel_zero hB
  | succ n ih =>
    have hK : ringChar (coordinateSliceField k') = ringChar k' :=
      (Algebra.ringChar_eq k' (coordinateSliceField k')).symm
    have : Fact (ringChar (coordinateSliceField k')).Prime := ⟨hK ▸ Fact.out⟩
    have : Fact (ringChar (coordinateSliceField k') ≠ ℓ) := ⟨hK ▸ Fact.out⟩
    have : IsNoetherian (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n);
        trait (coordinateSliceField k')) ↘ trait (coordinateSliceField k'))).left :=
      isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel n)
    refine boundedConstructible_nearbyCycles_affineSpace_of_slices n (fun i B' hB' ↦ ?_) hB
    obtain ⟨e⟩ := nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice n i hB'
    exact ProEtale.boundedConstructible_of_retract_padicAlgClRingObj ℓ e
      (ih (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB'))

/-- **Reduction to affine spaces**: for a model `M` of finite type over the trait with affine
total space `𝒳`, the geometric nearby cycles preserve bounded constructible complexes. Choose a
closed immersion `c : 𝒳 ⟶ 𝔸ⁿ_S` over the trait; then
`Ψ_𝒳 B ≅ Lc_s^* Rc_{s*} Ψ_𝒳 B ≅ Lc_s^* Ψ_{𝔸ⁿ} (Rc_* B)` by the full faithfulness of `Rc_{s*}` and
the proper exchange, and `Rc_* B` is bounded constructible. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_isAffine
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel) [IsAffine M.total]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  obtain ⟨q, g, _, _, _, hj, hi⟩ := hM.exists_isPullback
  obtain ⟨n, c, hc, _⟩ := exists_isClosedImmersion_affineSpace_of_isAffine q
  exact boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
    (N := affineSpaceModel k' n) (isTraitModel_affineSpaceModel n) (traitStdHom _ hj hi c hc)
    rfl (isPullback_traitStdHom_generic _ hj hi c hc) (isPullback_traitStdHom_special _ hi c hc)
    (fun hB' ↦ boundedConstructible_nearbyCycles_affineSpace_obj n hB') hB

/-- **Deligne's finiteness theorem for nearby cycles** (SGA 4½, [Th. finitude], Thm. 3.2; for
`ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): for a model `M` of finite type over the strictly
henselian trait `Spec k'⟦t⟧`, the geometric nearby cycles `Li^* Rj_* Lj^*` carry bounded
constructible complexes on the total space `𝒳` to bounded constructible complexes on the special
fibre. Bounded constructibility on the special fibre is checked on the traces `i⁻¹ V` of a
finite affine open cover of `𝒳`, where the nearby cycles are those of the restricted models
(`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`), and the affine case is
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_isAffine`. -/
theorem boundedConstructible_geometricNearbyCycles_obj
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := hM.isNoetherian_total
  have := isNoetherian_of_isTraitModel hM
  obtain ⟨n, V, hV⟩ := hM.exists_affineOpens_cover
  refine boundedConstructible_of_openCover _ (fun a ↦ M.i ⁻¹ᵁ (V a : M.total.Opens))
    (fun x ↦ hV (M.i.base x)) _ fun a ↦ ?_
  have : TopologicalSpace.NoetherianSpace (V a : M.total.Opens) :=
    (V a : M.total.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (V a : M.total.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsAffine (M.restrict (V a : M.total.Opens)).total := (V a).2
  have := isIso_pullbackExchange_restrictHom (Profinite.padicAlgClRingObj ℓ) M (V a)
  exact (boundedConstructible _).prop_of_iso
    (asIso (((M.restrictHom (V a)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B)).symm
    (boundedConstructible_geometricNearbyCycles_obj_of_isAffine _ (hM.restrict _)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB))

/-- **Deligne's finiteness theorem for the nearby cycles of a model** (SGA 4½, [Th. finitude],
Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): over the strictly henselian trait
`Spec k'⟦t⟧`, the nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model of finite type whose
identification factors as `ε = j ≫ e` through the total space preserve bounded constructible
complexes: `Lε^* A ≅ Lj^* Le^* A`, the pullback `Le^* A` is bounded constructible, and the
geometric nearby cycles `Li^* Rj_* Lj^*` preserve bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). No blueprint node states
this theorem; it is the analogue over the trait of `lem-sfb-dc-lower-star-preserves`
(`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`). -/
theorem preservesBoundedConstructible_of_isTraitModel (M : NearbyCyclesModel X X'.left)
    (hM : M.IsTraitModel) (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) := by
  obtain ⟨e, he⟩ := hε
  intro K hK
  have hB := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicAlgClRingObj ℓ) e K hK
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    he.symm K).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) M.j e).app K
  exact (boundedConstructible _).prop_of_iso
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (i₁ ≪≫ i₂)).symm)
    (boundedConstructible_geometricNearbyCycles_obj M hM hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
