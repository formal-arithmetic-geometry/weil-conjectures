/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding

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

Following Deligne's proof, the theorem is reduced to the affine spaces `𝔸ⁿ_S` and to
extensions by zero of lisse sheaves:
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
* **dévissage**: along the truncation triangles, to constructible sheaves placed in degree `0`
  (`ProEtale.boundedConstructible_obj_of_forall_singleFunctor`), and by noetherian induction along
  the open–closed triangles, to the extensions by zero `v_! L` of lisse sheaves `L` along locally
  closed immersions `v` (`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse`).

## Unfinished input

The theorem for the extension by zero `v_! L` of a lisse sheaf along a locally closed immersion
into an affine space `𝔸ⁿ_S`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse`) is `sorry`ed: it is
Deligne's theorem for torsion coefficients (SGA 4½, [Th. finitude], Thm. 3.2), passed to
`ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices, derived completeness and the Milnor sequence
(Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8). The reductions also use the proper
exchange (blueprint `det-sp-nearby-cycles-exchanges` (2), `sorry`ed in
`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`) and that bounded
constructible complexes on the special fibre form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`, `sorry`ed on the branch).

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

/-- The special fibre of a model of finite type over the trait is a noetherian scheme: it is of
finite type over the field `k'`. -/
lemma isNoetherian_of_isTraitModel {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsNoetherian X'.left := by
  obtain ⟨q, g, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType X'.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hi ‹_›
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) hi ‹_›
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  exact ⟨⟩

/-- The standard model of the affine space `𝔸ⁿ_S` over the trait `S = Spec k'⟦t⟧`. -/
noncomputable abbrev affineSpaceModel (k' : Type u) [Field k'] (n : ℕ) :=
  traitStdModel (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')

/-- The standard model of `𝔸ⁿ_S` is a model of finite type over the trait. -/
lemma isTraitModel_affineSpaceModel (n : ℕ) : (affineSpaceModel k' n).IsTraitModel :=
  isTraitModel_traitStdModel _

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Deligne's finiteness theorem for nearby cycles, for the extension by zero of a lisse sheaf
on a locally closed subscheme of an affine space** (SGA 4½, [Th. finitude], Thm. 3.2; for
`ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices and passage to the limit, Bhatt–Scholze, *The
pro-étale topology for schemes*, §6.8): over the strictly henselian trait `S = Spec k'⟦t⟧`
(`k'` separably closed, `ℓ ≠ char k'`), let `v : E ⟶ 𝔸ⁿ_S` be a locally closed immersion,
factored as a closed immersion `c' : E ⟶ W` into an open `W` of a closed subscheme
`c : D ⟶ 𝔸ⁿ_S`, and let `L` be a lisse (pro-étale locally finitely presented) sheaf of
`ℚ̄_ℓ`-modules on `E`. Then the geometric nearby cycles `Li^* Rj_* Lj^*` of its extension by zero
`v_! L = Rc_* j_{W!} Rc'_* L`, with `j : 𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` and `i : 𝔸ⁿ_s ⟶ 𝔸ⁿ_S`, are a bounded
constructible complex on the special fibre `𝔸ⁿ_s`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) :=
  sorry

/-- Deligne's finiteness theorem for nearby cycles on an affine space `𝔸ⁿ_S`: the geometric
nearby cycles of the standard model of `𝔸ⁿ_S` preserve bounded constructible complexes. This is
reduced to the extensions by zero of lisse sheaves on locally closed subschemes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse`) by the dévissage
`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj (n : ℕ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' n).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)).IsTriangulated :=
    isTriangulated_boundedConstructible (ℓ := ℓ) _ _
  exact boundedConstructible_obj_of_forall_lisse
    (Φ := L(((affineSpaceModel k' n).geometric.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
      R(((affineSpaceModel k' n).geometric.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(((affineSpaceModel k' n).geometric.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (fun D c _ W E c' _ L hL ↦ by
      exact boundedConstructible_nearbyCycles_affineSpace_lisse n D c W E c' L hL) hB

/-- **Reduction along a closed embedding**: let `φ : M.geometric ⟶ N.geometric` be a morphism of
the geometric models of two models of finite type over the trait, whose morphism of total spaces
`t` is a closed immersion and whose squares of geometric generic fibres and of special fibres are
cartesian. If the geometric nearby cycles of `N` preserve bounded constructible complexes, then
so do those of `M`: `Ψ_M B ≅ Lt_s^* Rt_{s*} Ψ_M B ≅ Lt_s^* Ψ_N (Rt_* B)` by the full faithfulness
of `Rt_{s*}` and the proper exchange
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), and `Rt_* B` is bounded
constructible. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding {Y : Scheme.{u}}
    {Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} (hM : M.IsTraitModel) (hN : N.IsTraitModel)
    {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left} (φ : M.geometric.Hom N.geometric t f')
    (ht : φ.total = t) [IsClosedImmersion t] (hj : IsPullback φ.generic M.j N.j t)
    (hi : IsPullback M.i f' t N.i)
    (hN' : ∀ {B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.total))},
      boundedConstructible _ B' → boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
        ((N.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B'))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := hN.isNoetherian_total
  have : IsClosedImmersion f' := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hi ‹_›
  have : IsProper t := inferInstance
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app B) :=
    Hom.isIso_pushforwardExchange_app_of_isProper hM hN φ ht hj hi B hB
  have h₁ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
      ((N.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((t)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)) :=
    hN' (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ t hB)
  have h₂ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
      ((R((f')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B)) :=
    (boundedConstructible _).prop_of_iso
      (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app B)) h₁
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f').counit.app _))
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' _ h₂)

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
    (N := affineSpaceModel k' n) hM (isTraitModel_affineSpaceModel n) (traitStdHom _ hj hi c hc)
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

/-- The derived pullbacks along equal morphisms agree on objects. -/
lemma nonempty_leftDerivedUpperStar_obj_iso_of_eq (Λ : Sheaf (coherentTopology Profinite.{u})
    Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    Nonempty ((L((a)^*⟦Λ⟧)).obj K ≅ (L((b)^*⟦Λ⟧)).obj K) := by
  subst h
  exact ⟨Iso.refl _⟩

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
