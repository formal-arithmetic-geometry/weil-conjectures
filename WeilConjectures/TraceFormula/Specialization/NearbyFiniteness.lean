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
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

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
  closed immersions `v : E ⟶ 𝔸ⁿ_S` whose image lies either in the generic fibre `𝔸ⁿ_η` or in the
  special fibre (`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`);
* **special fibre**: if the image of `v` misses the generic fibre, then `Lj^* v_! L = 0`, since
  `j : 𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` factors through the open `𝔸ⁿ_η`, and the nearby cycles vanish
  (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_isZero`).

## Unfinished input

The theorem for the extension by zero `v_! L` of a lisse sheaf along a locally closed immersion
into the generic fibre `𝔸ⁿ_η` of an affine space `𝔸ⁿ_S`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic`) rests on the
`sorry`ed `NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core`
for `n ≥ 1` when `D` meets the special fibre and `D ⟶ S` is not a closed immersion. If `D`
misses the special fibre, the nearby cycles vanish by the proper exchange
(`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`); if `D ⟶ S` is a closed
immersion, they reduce to those of the trait
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`).
For `n = 0` the theorem is proved: `𝔸⁰_S ⟶ S` is an isomorphism, and the nearby cycles of
the trait itself are computed directly on the pro-étale site
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`). For `n ≥ 1` it is
Deligne's theorem for torsion coefficients (SGA 4½, [Th. finitude], Thm. 3.2), passed to
`ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices, derived completeness and the Milnor sequence
(Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8). No blueprint node states this
theorem: the blueprint uses it without a node in the proofs of
`sk-prop-tf-nearby-duality-foundation` ("bounded constructible by the finiteness theorem for
nearby cycles") and `det-sp-constant-family-vanishing` ("an exact functor with bounded
constructible values"). It does not follow from the finiteness of direct images available in
`sec-six-functors`: those nodes concern morphisms of finite type over a field, or proper
morphisms, while `j : 𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` is neither. Writing `Ψ` as the colimit of the
`i^* Rj'_*` over the finite extensions `η'` of `η` is only valid for torsion coefficients, and
there the system does not stabilise: already on `𝔸⁰_S` with `Λ = ℤ/ℓ`, the transition maps on
`H¹ = Hom(I_t, Λ)` are multiplication by the ramification indices. The reductions also use the
proper exchange (blueprint `det-sp-nearby-cycles-exchanges` (2), `sorry`ed in
`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`) and that bounded
constructible complexes on the special fibre form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj`, `sorry`ed on the branch).

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

/-- The derived pullbacks along equal morphisms agree on objects. -/
lemma nonempty_leftDerivedUpperStar_obj_iso_of_eq (Λ : Sheaf (coherentTopology Profinite.{u})
    Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    Nonempty ((L((a)^*⟦Λ⟧)).obj K ≅ (L((b)^*⟦Λ⟧)).obj K) := by
  subst h
  exact ⟨Iso.refl _⟩

variable (k') in
/-- The generic fibre `S ∖ {s} = D(t)` of the trait `S = Spec k'⟦t⟧`, as an open subscheme. -/
noncomputable def traitGenericOpen : (trait k').Opens :=
  (trait k').basicOpen ((Scheme.ΓSpecIso (.of (PowerSeries k'))).inv PowerSeries.X)

/-- The geometric generic point of the trait lies in its generic fibre `D(t)`: `t` is a nonzero
element of the field `Ω`. -/
lemma traitGenericPoint_preimage_traitGenericOpen :
    traitGenericPoint k' ⁻¹ᵁ traitGenericOpen k' = ⊤ := by
  rw [traitGenericOpen, Scheme.preimage_basicOpen_top, traitGenericPoint,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    Scheme.basicOpen_of_isUnit]
  refine IsUnit.map _ (Ne.isUnit ?_)
  change algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X ≠ 0
  rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
  exact (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero))

/-- The closed point of the trait does not lie in its generic fibre `D(t)`. -/
lemma traitClosedPoint_preimage_traitGenericOpen :
    traitClosedPoint k' ⁻¹ᵁ traitGenericOpen k' = ⊥ := by
  rw [traitGenericOpen, Scheme.preimage_basicOpen_top, traitClosedPoint,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  change Scheme.basicOpen _ ((Scheme.ΓSpecIso (.of k')).inv
    (PowerSeries.constantCoeff PowerSeries.X)) = ⊥
  rw [PowerSeries.constantCoeff_X, map_zero, Scheme.basicOpen_zero]

variable (k') in
/-- The generic fibre `𝔸ⁿ_η` of the affine space `𝔸ⁿ_S`, as an open subscheme: the preimage of
the generic fibre `D(t)` of the trait. -/
noncomputable def affineSpaceGenericOpen (n : ℕ) : (affineSpaceModel k' n).total.Opens :=
  (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') ⁻¹ᵁ traitGenericOpen k'

/-- The geometric generic fibre `𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` lands in the generic fibre `𝔸ⁿ_η`. -/
lemma range_j_affineSpaceModel_subset (n : ℕ) :
    Set.range (affineSpaceModel k' n).j.base ⊆
      Set.range (affineSpaceGenericOpen k' n).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  change y ∈ (affineSpaceModel k' n).j ⁻¹ᵁ affineSpaceGenericOpen k' n
  rw [affineSpaceGenericOpen, ← Scheme.Hom.comp_preimage]
  simp only [affineSpaceModel, traitStdModel_j, pullback.condition, Scheme.Hom.comp_preimage,
    traitGenericPoint_preimage_traitGenericOpen, Scheme.Hom.preimage_top]
  trivial

/-- **Nearby cycles of a complex supported on the special fibre vanish**: if `Rc_* K` is a
complex on `𝔸ⁿ_S` pushed forward along a closed immersion `c : D ⟶ 𝔸ⁿ_S`, and the restriction of
`K` to the generic fibre `c⁻¹ 𝔸ⁿ_η` vanishes, then `Lj^* Rc_* K = 0`, so the geometric nearby
cycles `Li^* Rj_* Lj^* Rc_* K` vanish. -/
lemma isZero_nearbyCycles_affineSpace_of_isZero (n : ℕ) {D : Scheme.{u}}
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      K)) :
    IsZero (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have h := isZero_leftDerivedUpperStar_ι_obj_rightDerivedLowerStar_obj
    (Profinite.padicAlgClRingObj ℓ) (affineSpaceGenericOpen k' n) c hK
  have hfac := IsOpenImmersion.lift_fac (affineSpaceGenericOpen k' n).ι
    (affineSpaceModel k' n).j (range_j_affineSpaceModel_subset n)
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    hfac.symm ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
    (IsOpenImmersion.lift (affineSpaceGenericOpen k' n).ι (affineSpaceModel k' n).j
      (range_j_affineSpaceModel_subset n)) (affineSpaceGenericOpen k' n).ι).app
    ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)
  exact (L(((affineSpaceModel k' n).geometric.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
    ((R(((affineSpaceModel k' n).geometric.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
      (((L((IsOpenImmersion.lift (affineSpaceGenericOpen k' n).ι (affineSpaceModel k' n).j
        (range_j_affineSpaceModel_subset n))^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
          h).of_iso (i₁ ≪≫ i₂)))

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction along a closed embedding**: let `φ : M.geometric ⟶ N.geometric` be a morphism of
the geometric models of two models of finite type over the trait, whose morphism of total spaces
`t` is a closed immersion and whose squares of geometric generic fibres and of special fibres are
cartesian. If the geometric nearby cycles of `N` preserve bounded constructible complexes, then
so do those of `M`: `Ψ_M B ≅ Lt_s^* Rt_{s*} Ψ_M B ≅ Lt_s^* Ψ_N (Rt_* B)` by the full faithfulness
of `Rt_{s*}` and the proper exchange
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`), and `Rt_* B` is
bounded constructible. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding {Y : Scheme.{u}}
    {Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} (hN : N.IsTraitModel)
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
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ ht hj hi B hB
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

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The extension by zero `j_{W!} Rc'_* L` of a lisse sheaf `L` on `E` along a closed immersion
`c' : E ⟶ W` into an open `W` of a closed subscheme `c : D ⟶ 𝔸ⁿ_S` is a bounded constructible
complex on `D`. -/
lemma boundedConstructible_lisseExtension_closed (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D)
      (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hL' : IsConstructibleModuleObject _ L :=
    ⟨Scheme.Stratification.trivial E, fun _ ↦ (isLocallyFinitelyPresented_mapMod_iff _ _ _).2
      (IsLocallyFinitelyPresented.upperStar _ _ hL)⟩
  exact boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _ W.ι _
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ c'
      (boundedConstructible_singleFunctor_zero_obj _ L hL'))

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The extension by zero `v_! L = Rc_* j_{W!} Rc'_* L` of a lisse sheaf `L` along a locally closed
immersion `v : E ⟶ 𝔸ⁿ_S`, factored through a closed immersion `c' : E ⟶ W` into an open `W` of a
closed subscheme `c : D ⟶ 𝔸ⁿ_S`, is a bounded constructible complex on `𝔸ⁿ_S`. -/
lemma boundedConstructible_lisseExtension (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceModel k' n).total)
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj L)))) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  exact boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ c
    (boundedConstructible_lisseExtension_closed n D c W E c' L hL)

omit [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Deligne's finiteness theorem for nearby cycles on `𝔸⁰_S`**: the geometric nearby cycles of
the standard model of `𝔸⁰_S` preserve bounded constructible complexes. The structure map
`q : 𝔸⁰_S ⟶ S` is an isomorphism, hence a closed embedding with cartesian squares of fibres into
the trait, whose nearby cycles preserve bounded constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`). -/
theorem boundedConstructible_nearbyCycles_affineSpaceModel_zero
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' 0).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' 0).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' 0).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  let q := 𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k'
  have : IsClosedImmersion q :=
    inferInstanceAs (IsClosedImmersion (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k'))
  let φ : (affineSpaceModel k' 0).geometric.Hom (traitSelfModel k').geometric q
      (pullback.snd q (traitClosedPoint k')) :=
    { total := q
      generic := pullback.snd q (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  exact boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
    (Y' := Over.mk (𝟙 (Spec (.of k')))) (N := traitSelfModel k') (isTraitModel_traitSelfModel k')
    φ rfl
    (IsPullback.of_hasPullback q (traitGenericPoint k')).flip
    (IsPullback.of_hasPullback q (traitClosedPoint k'))
    (fun hB' ↦ preservesBoundedConstructible_traitSelfModel k' _ hB') hB

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Nearby cycles of a complex supported away from the special fibre vanish**: if the closed
subscheme `c : D ⟶ 𝔸ⁿ_S` misses the special fibre `𝔸ⁿ_s`, then `Ψ (Rc_* K) = 0` for every bounded
constructible `K` on `D`. By the proper exchange, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`, and the
special fibre `D_s` of `D` is empty. -/
lemma isZero_nearbyCycles_affineSpace_of_disjoint (n : ℕ) {D : Scheme.{u}}
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hc : Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' n).i.base))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    IsZero (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  let q := 𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'
  let M := traitStdModel (c ≫ q)
  have hj : IsPullback M.j (pullback.snd (c ≫ q) (traitGenericPoint k')) (c ≫ q)
      (traitGenericPoint k') := IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre (c ≫ q)).hom (c ≫ q) (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let φ := traitStdHom q hj hi c rfl
  have : IsEmpty (traitStdSpecialFibre (c ≫ q)).left := by
    refine ⟨fun x ↦ Set.disjoint_left.1 hc ⟨M.i.base x, rfl⟩
      ⟨(traitStdSpecialHom q hi c rfl).base x, ?_⟩⟩
    exact congrArg (fun g ↦ g.base x) φ.comm_i
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ rfl
      (isPullback_traitStdHom_generic q hj hi c rfl) (isPullback_traitStdHom_special q hi c rfl)
      K hK
  refine IsZero.of_iso ?_ (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K))
  exact (R((traitStdSpecialHom q hi c rfl)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
    (isZero_derivedCategory_of_isEmpty' _ _)

omit [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Nearby cycles of a complex supported on a closed subscheme embedded in the trait**: if the
closed subscheme `c : D ⟶ 𝔸ⁿ_S` maps by a closed immersion to the trait `S` (for instance the
closure of an `S`-integral point of the generic fibre), then `Ψ (Rc_* K)` is bounded constructible
for every bounded constructible `K` on `D`. By the closed-embedding reduction along `D ⟶ S`, the
nearby cycles of `D` preserve bounded constructible complexes, the trait's do
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`); and by the proper exchange,
`Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp (n : ℕ)
    {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hcq : IsClosedImmersion (c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  let q := 𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'
  let M := traitStdModel (c ≫ q)
  have hj : IsPullback M.j (pullback.snd (c ≫ q) (traitGenericPoint k')) (c ≫ q)
      (traitGenericPoint k') := IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre (c ≫ q)).hom (c ≫ q) (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let ψ : M.geometric.Hom (traitSelfModel k').geometric (c ≫ q)
      (pullback.snd (c ≫ q) (traitClosedPoint k')) :=
    { total := c ≫ q
      generic := pullback.snd (c ≫ q) (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have hΨ : boundedConstructible _ ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      K) :=
    boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
      (Y' := Over.mk (𝟙 (Spec (.of k')))) (N := traitSelfModel k')
      (isTraitModel_traitSelfModel k') ψ rfl hj.flip hi
      (fun hB' ↦ preservesBoundedConstructible_traitSelfModel k' _ hB') hK
  let φ := traitStdHom q hj hi c rfl
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ rfl
      (isPullback_traitStdHom_generic q hj hi c rfl) (isPullback_traitStdHom_special q hi c rfl)
      K hK
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have := isClosedImmersion_traitStdSpecialHom q hi c rfl
  exact (boundedConstructible _).prop_of_iso
    (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K)).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ _ hΨ)

/-- **Deligne's finiteness theorem for nearby cycles, core case** (SGA 4½, [Th. finitude],
Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): the statement of
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic` in its open case:
`n ≥ 1`, the closed subscheme `D` meets the special fibre and `D ⟶ S` is not a closed immersion.
The other cases are proved. No blueprint node states this theorem; it is
`sorry`ed (see the module docstring). -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core (n : ℕ) (hn : n ≠ 0)
    (D : Scheme.{u}) (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hc : ¬ Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' n).i.base))
    (hcq : ¬ IsClosedImmersion (c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'))) (W : D.Opens)
    (hW : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' n) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c'] (hc' : Surjective c')
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

/-- **Deligne's finiteness theorem for nearby cycles, for the extension by zero of a lisse sheaf
on a locally closed subscheme of the generic fibre of an affine space** (SGA 4½, [Th. finitude],
Thm. 3.2; for `ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices and passage to the limit, Bhatt–Scholze,
*The pro-étale topology for schemes*, §6.8): over the strictly henselian trait
`S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), let `v : E ⟶ 𝔸ⁿ_S` be a locally closed
immersion, factored as a surjective closed immersion `c' : E ⟶ W` (so `E` is `W` up to
nilpotents) onto an open `W` of a closed subscheme `c : D ⟶ 𝔸ⁿ_S`, with `W` contained in the
preimage `c⁻¹ 𝔸ⁿ_η` of the generic fibre `𝔸ⁿ_η = 𝔸ⁿ_S ×_S D(t)`, and let `L` be a lisse
(pro-étale locally finitely presented) sheaf of `ℚ̄_ℓ`-modules on `E`. Then the geometric nearby
cycles `Li^* Rj_* Lj^*` of its extension by zero `v_! L = Rc_* j_{W!} Rc'_* L`, with
`j : 𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` and `i : 𝔸ⁿ_s ⟶ 𝔸ⁿ_S`, are a bounded constructible complex on the special
fibre `𝔸ⁿ_s`. (When `W` misses the generic fibre, these nearby cycles vanish:
`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_isZero`.) The case `n = 0` is
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`, and the case where `D`
misses the special fibre is `NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`; the
case where `D ⟶ S` is a closed immersion is
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`; the
remaining case is the `sorry`ed
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_generic (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens)
    (hW : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' n) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c'] (hc' : Surjective c')
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) := by
  cases n with
  | zero =>
    exact boundedConstructible_nearbyCycles_affineSpaceModel_zero
      (boundedConstructible_lisseExtension 0 D c W E c' L hL)
  | succ n =>
    by_cases hc : Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' (n + 1)).i.base)
    · exact boundedConstructible_of_isZero _ (isZero_nearbyCycles_affineSpace_of_disjoint _ c hc
        (boundedConstructible_lisseExtension_closed _ D c W E c' L hL))
    by_cases hcq : IsClosedImmersion (c ≫ (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k'))
    · exact boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp _ c hcq
        (boundedConstructible_lisseExtension_closed _ D c W E c' L hL)
    exact boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core _ n.succ_ne_zero D c hc
      hcq W hW E c' hc' L hL

/-- Deligne's finiteness theorem for nearby cycles on an affine space `𝔸ⁿ_S`: the geometric
nearby cycles of the standard model of `𝔸ⁿ_S` preserve bounded constructible complexes. By the
dévissage `ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`, adapted to the
generic fibre `𝔸ⁿ_η`, this is reduced to the extensions by zero `Rc_* j_{W!} Rc'_* L` of lisse
sheaves with `W` either inside the generic fibre
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic`) or inside the
special fibre, where the nearby cycles vanish
(`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_isZero`). -/
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
    isTriangulated_boundedConstructible_padicAlgClRingObj _ ℓ
  refine boundedConstructible_obj_of_forall_lisse_along
    (Φ := L(((affineSpaceModel k' n).geometric.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
      R(((affineSpaceModel k' n).geometric.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(((affineSpaceModel k' n).geometric.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (U := affineSpaceGenericOpen k' n) (fun D c _ W hW E c' _ hc' L hL ↦ ?_) hB
  rcases hW with hW | hW
  · exact boundedConstructible_nearbyCycles_affineSpace_lisse_generic n D c W hW E c' hc'
      L hL
  · have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace (c ⁻¹ᵁ affineSpaceGenericOpen k' n) :=
      (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι :=
      ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    exact boundedConstructible_of_isZero _ (isZero_nearbyCycles_affineSpace_of_isZero n c
      (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint _ W.ι
        (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι (by rwa [Scheme.Opens.range_ι,
          Scheme.Opens.range_ι]) _))

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
