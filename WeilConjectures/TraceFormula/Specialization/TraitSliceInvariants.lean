/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCompRetraction
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGeneric
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The generic-slicing identification of nearby cycles with invariants

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and let
`M''` be its geometric slice over the trait `T = Spec K⟦t⟧` along the generic slice
`σ : T ⟶ 𝔸¹_S` (`NearbyCyclesModel.baseChange`), with geometric generic fibre
`𝒳'' ×_T Spec Ω_K`. The projection `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`) factors through
the *intermediate slice model* `M₁` (`NearbyCyclesModel.sliceBaseModel`): the slice model
(`NearbyCyclesModel.sliceModel`) whose generic fibre is `𝒳'' ×_T (T ×_S Spec Ω) = 𝒳'' ×_𝒳 𝒳_η̄`,
over the map `Spec Ω_K ⟶ T ×_S Spec Ω` of geometric generic points
(`AlgebraicGeometry.traitGenericToBase`):
```
M'' --ρ--> M₁ --ψ--> M
```
(`NearbyCyclesModel.sliceDescentHom`, `NearbyCyclesModel.sliceHom`). This splits the
generic-slicing identification (blueprint `sk-prop-tf-nearby-external-kunneth`, "Facts about
traits", identification (2); SGA 4½, [Th. finitude], §§3.4, 3.7) into its two classical parts:

* the pullback exchange of `ψ` is invertible: nearby cycles over the generic fibre `𝒳_η̄` commute
  with the base change `𝒳'' ⟶ 𝒳` of the generic slice
  (`NearbyCyclesModel.isIso_pullbackExchange_sliceBaseHom_app`, unfinished);
* the pullback exchange of `ρ` is the inclusion of the invariants of the pro-`p` kernel
  `P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` of the map of inertia groups, which acts on the nearby cycles of
  `M''` through a finite quotient
  (`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceDescentHom`, unfinished).

Together they give the identification of the slicing exchange of `M` with the inclusion of the
`P'`-invariants (`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The fibre product `Spec K⟦t⟧ ×_S Spec Ω` of the trait map and of the geometric generic point
of `S = Spec k'⟦t⟧`. -/
noncomputable abbrev traitGenericBase : Scheme.{u} :=
  pullback (traitMap k' K) (traitGenericPoint k')

/-- The map `Spec Ω_K ⟶ Spec K⟦t⟧ ×_S Spec Ω` of geometric generic points. -/
noncomputable def traitGenericToBase :
    Spec (.of (traitGenericField K)) ⟶ traitGenericBase k' K :=
  pullback.lift (traitGenericPoint K) (traitGenericPointMap k' K) (traitGenericPoint_traitMap k' K)

@[reassoc (attr := simp)]
lemma traitGenericToBase_fst :
    traitGenericToBase k' K ≫ pullback.fst _ _ = traitGenericPoint K :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitGenericToBase_snd :
    traitGenericToBase k' K ≫ pullback.snd _ _ = traitGenericPointMap k' K :=
  pullback.lift_snd _ _ _

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' K} (x : K) {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- The *intermediate slice model* `M₁`: total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, special fibre
that of the geometric slice and generic fibre `𝒳'' ×_{Spec K⟦t⟧} (Spec K⟦t⟧ ×_S Spec Ω)`, the
slice model `NearbyCyclesModel.sliceModel` over `Spec K⟦t⟧ ×_S Spec Ω`. -/
noncomputable def sliceBaseModel :
    NearbyCyclesModel X (baseChangeSpecial b (traitSlice x)).left where
  total := pullback b (traitSlice x)
  generic := sliceGeneric x b (pullback.fst (traitMap k' K) (traitGenericPoint k'))
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := sliceGenericMap x hM hb pullback.condition ≫ M.ε

/-- The projection `M₁ ⟶ M` from the intermediate slice model. -/
noncomputable def sliceBaseHom :
    (sliceBaseModel x hM hb).Hom M (𝟙 X)
      (baseChangeSpecialMap hM b hb (traitSlice x) (traitSlice_over x)) where
  total := pullback.fst _ _
  generic := sliceGenericMap x hM hb pullback.condition
  comm_j := hM.isPullback_j.lift_fst _ _ _
  comm_i := baseChangeSpecialMap_i hM b hb _ _
  comm_ε := (Category.comp_id _).symm

/-- The map of generic fibres `𝒳'' ×_T Spec Ω_K ⟶ 𝒳'' ×_T (T ×_S Spec Ω)` from the geometric
slice to the intermediate slice model. -/
noncomputable def sliceDescentGeneric :
    (baseChange hM b hb (traitSlice x) (traitSlice_over x)).generic ⟶
      (sliceBaseModel x hM hb).generic :=
  pullback.map _ _ _ _ (𝟙 _) (traitGenericToBase k' K) (𝟙 _) (by simp) (by simp)

lemma sliceDescentGeneric_comp_sliceGenericMap :
    sliceDescentGeneric x hM hb ≫ (sliceBaseHom x hM hb).generic =
      (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).generic := by
  refine hM.isPullback_j.hom_ext ?_ ?_
  · simp [sliceDescentGeneric, sliceBaseHom, sliceGenericMap]
  · simp [sliceDescentGeneric, sliceBaseHom, sliceGenericMap]

/-- The morphism of models `ρ : M'' ⟶ M₁` from the geometric slice to the intermediate slice
model: the identity on the total space `𝒳''` and `𝒳'' ×_T Spec Ω_K ⟶ 𝒳'' ×_T (T ×_S Spec Ω)` on
generic fibres. -/
noncomputable def sliceDescentHom :
    (baseChange hM b hb (traitSlice x) (traitSlice_over x)).Hom (sliceBaseModel x hM hb) (𝟙 X)
      (𝟙 (baseChangeSpecial b (traitSlice x)).left) where
  total := 𝟙 _
  generic := sliceDescentGeneric x hM hb
  comm_j := by simp [sliceDescentGeneric, sliceBaseModel]
  comm_i := by simp only [Category.id_comp, Category.comp_id]; rfl
  comm_ε := by
    rw [Category.comp_id]
    change _ ≫ sliceGenericMap _ _ _ _ ≫ M.ε = baseChangeGenericMap _ _ _ _ _ ≫ M.ε
    rw [← Category.assoc]
    exact congrArg (· ≫ M.ε) (sliceDescentGeneric_comp_sliceGenericMap x hM hb)


variable [IsSepClosed k'] [Fact (ringChar k').Prime] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **Nearby cycles commute with the generic slice** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits"; SGA 4½, [Th. finitude], §§3.4, 3.7):
for a model `M` of finite type over the strictly henselian trait `S = Spec k'⟦t⟧` with a
coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the pullback exchange `α_ψ : Lσ^* Ψ_M A ⟶ Ψ_{M₁} A` of the projection
`ψ : M₁ ⟶ M` from the intermediate slice model is an isomorphism for bounded constructible `A`.
Here the generic fibre of `M₁` is `𝒳'' ×_𝒳 𝒳_η̄`, so `α_ψ` is base change of `Rj_*`, for
`j : 𝒳_η̄ ⟶ 𝒳`, along the base change `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳` of the generic slice,
restricted to the special fibre. The generic slice is the composite of the strict localization
`S' = (𝔸¹_S)_{(s')}` at the generic point of the special-fibre line, along which base change
holds since it is weakly étale, and of the change of strictly henselian traits
`Spec K⟦t⟧ ⟶ S'` (completion and passage to the algebraic closure of the residue field, with the
same uniformizer), along which nearby cycles do not change (Th. finitude 3.7).

Unfinished: the invariance of nearby cycles under the change of traits `Spec K⟦t⟧ ⟶ S'` is
Deligne's theorem (proved in [Th. finitude] by the dévissage of the finiteness theorem 3.2); it
needs base change of `Rj_*` along a morphism which is not weakly étale. Only weakly étale and
universally homeomorphic base change are formalised for pro-étale `ℚ̄_ℓ`-sheaves, and the strict
localization `S'` is not formalised. -/
theorem isIso_pullbackExchange_sliceBaseHom_app
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)) :
    IsIso (((sliceBaseHom (traitSliceCoord k') hM hb).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app A) :=
  sorry

/-- **Nearby cycles of the intermediate slice model are the `P'`-invariants** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", identification (2); SGA 4½,
[Th. finitude], §3.7; SGA 7, Exp. XIII, §1.3). The generic fibre of the geometric slice `M''` is
the pullback of that of the intermediate slice model `M₁` along the pro-`p` Galois cover
`Spec Ω_K ⟶ (Spec K⟦t⟧ ×_S Spec Ω)_red` with group
`P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` (`NearbyCyclesModel.GenericAut`), the kernel of the map of
inertia groups. For bounded constructible `C`:
* the action of `P'` on `Ψ_{M''} C` (`NearbyCyclesModel.baseChangeAut`) factors through a finite
  quotient: a subgroup `V` of finite index acts trivially (continuity of the action, from the
  finiteness of `Ψ_{M''} C`);
* the pullback exchange `α_ρ : Ψ_{M₁} C ⟶ Ψ_{M''} C` is the inclusion of the invariants: it is a
  split monomorphism whose idempotent is `1 / [P' : V]` times the sum of the actions of
  representatives of `P' ⧸ V` (Hochschild–Serre for the pro-`p` cover; `[P' : V]` is a power of
  `p`, invertible in `ℚ̄_ℓ`).

Unfinished: neither group actions on pro-étale `ℚ̄_ℓ`-sheaves (continuous cohomology of the
pro-`p` group `P'`, Galois descent along pro-finite étale covers) nor the continuity of the action
on nearby cycles is formalised; the latter needs Deligne's finiteness theorem for `M''`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core`, still
`sorry`) and the continuity of cohomology along the limit `Spec Ω_K = lim Spec L_U` of the finite
subextensions, which is not formalised for `ℚ̄_ℓ`-coefficients. -/
theorem exists_subgroup_pullbackExchange_sliceDescentHom
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ r, ((sliceDescentHom (traitSliceCoord k') hM hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ r = 𝟙 _ ∧
        Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) •
          (r ≫ ((sliceDescentHom (traitSliceCoord k') hM hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C) =
        ∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) :=
  sorry

/-- **The generic-slicing identification of nearby cycles with invariants** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", identification (2)): for a model `M`
over `S = Spec k'⟦t⟧` with a coordinate `b`, a subgroup `V` of finite index of the pro-`p` kernel
`P'` acts trivially on the nearby cycles `Ψ_{M''} A` of the geometric slice, and the slicing
exchange `α : Lσ^* Ψ_M A ⟶ Ψ_{M''} A` is a split monomorphism whose idempotent is `1 / [P' : V]`
times the sum of the actions of representatives of `P' ⧸ V`. It is the composite of the exchange
of the intermediate slice model, invertible by
`NearbyCyclesModel.isIso_pullbackExchange_sliceBaseHom_app`, and of the inclusion of the
`P'`-invariants `NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceDescentHom`
(`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`). -/
theorem exists_subgroup_pullbackExchange_baseChangeHom_traitSlice
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)) :
    ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _) ∧
      ∃ r, ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A ≫ r =
            𝟙 _ ∧
        Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) •
          (r ≫ ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A) =
        ∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  have hA' : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)) :=
    (boundedConstructible _).prop_of_iso (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).mapIso
      ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X).app A).symm) hA
  have hD := exists_subgroup_pullbackExchange_sliceDescentHom (ℓ := ℓ) hM hb
    (C := L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) hA'
  obtain ⟨V, hV, htriv, r, hr, havg⟩ := hD
  have hs := isIso_pullbackExchange_sliceBaseHom_app (ℓ := ℓ) hM hb (A := A) hA
  refine ⟨V, hV, fun σ hσ ↦ eq_id_of_eq_id_aux _
    (fun g ↦ Hom.autAction_naturality _ _ g)
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (Category.id_comp (𝟙 X))).app A) (htriv σ hσ), ?_⟩
  have key := exists_retraction_pullbackExchange_of_comp (Profinite.padicAlgClRingObj ℓ)
    (sliceDescentHom (traitSliceCoord k') hM hb) (sliceBaseHom (traitSliceCoord k') hM hb)
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
    (Category.id_comp _) (sliceDescentGeneric_comp_sliceGenericMap (traitSliceCoord k') hM hb) A
    (by exact_mod_proofs hs)
    Finset.univ (Fintype.card (GenericAut k' (traitSliceField k') ⧸ V))
    (fun σ : GenericAut k' (traitSliceField k') ⧸ V ↦ (baseChangeAut hM b hb
      (traitSlice (traitSliceCoord k')) (traitSlice_over _) σ.out).autAction
        (Profinite.padicAlgClRingObj ℓ))
    (fun σ _ _ g ↦ Hom.autAction_naturality _ _ g) r (by exact_mod_proofs hr)
    (by exact_mod_proofs havg)
  exact_mod_proofs key

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
