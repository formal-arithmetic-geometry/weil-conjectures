/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeNormal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeValues

/-!
# Lattices of lisse `E`-sheaves are submodules

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. For a
locally free `𝒪_{E,S}`-module `M`, the unit `M ⟶ E_S ⊗_{𝒪_{E,S}} M` is a monomorphism
(`AlgebraicGeometry.ProEtale.mono_extendRestrictAdjunction_unit_app_of_isLocallyFree`): this is
local on `S` (`ProEtale.CondensedRing.mono_of_mono_upperStar_map_of_cover`, the pullbacks along a
pro-étale cover being jointly conservative and left exact), the formation of the unit commutes
with pullbacks (`ProEtale.CondensedRing.upperStar_map_unit_app_comp_comapUpperStarIso_inv_app`),
and for free modules the unit is a monomorphism
(`AlgebraicGeometry.ProEtale.mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers`).

Hence on a connected normal Noetherian scheme every lisse `E`-module `L` contains a lisse
`𝒪_E`-submodule `M` with `M[1/ℓ] = L`
(`AlgebraicGeometry.ProEtale.exists_mono_isLocallyFree_padicIntegers_of_isIntegrallyClosed_stalk`,
blueprint `lemma-global-lattice-normal-scheme`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Mono

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Monomorphisms of module objects are local for the pro-étale topology**: a morphism whose
pullbacks along the members of a pro-étale cover are monomorphisms is a monomorphism. -/
theorem mono_of_mono_upperStar_map_of_cover {S : Scheme.{u}}
    {N N' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)} (g : N ⟶ N')
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (h : ∀ i, Mono ((𝒰.f i)^*⟦Λ⟧.map g)) : Mono g := by
  rw [mono_iff_isIso_fst (pullbackIsPullback g g)]
  refine isIso_of_isIso_upperStar_map_of_cover Λ _ 𝒰 fun i ↦ ?_
  rw [PullbackCone.mk_fst, ← PreservesPullback.iso_hom_fst]
  infer_instance

end Mono

section Unit

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The pullback of the unit `K ⟶ Res (Λ'_S ⊗ K)` along `f` is, through
`f^* Res ≅ Res f^*` and (Pull), the unit at `f^* K`. -/
lemma upperStar_map_unit_app_comp_comapUpperStarIso_inv_app {X S : Scheme.{u}} (f : X ⟶ S)
    (K : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (f)^*⟦Λ⟧.map ((Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app K) ≫
        (comapUpperStarIso a f).inv.app _ =
      (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app ((f)^*⟦Λ⟧.obj K) ≫
        (Mod.comap (coefficientMap a X)).map ((pullIso a f).hom.app K) := by
  have h := pullIso_hom_app_comp_upperStar_map_homEquiv_symm a f
    ((Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app K)
  have h0 : ((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv _ _).symm
      ((Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app K) = 𝟙 _ := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have key : ((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv _ _)
      ((pullIso a f).hom.app K) = (f)^*⟦Λ⟧.map
        ((Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app K) ≫
          (comapUpperStarIso a f).inv.app _ := by
    refine (Equiv.eq_symm_apply _).1 (Eq.trans ?_ h)
    rw [h0, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [Adjunction.homEquiv_unit] at key
  exact key.symm

end Unit

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- **The unit `M ⟶ E_S ⊗_{𝒪_{E,S}} M` of a locally free `𝒪_{E,S}`-module is a
monomorphism.** -/
theorem mono_extendRestrictAdjunction_unit_app_of_isLocallyFree {S : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S))
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S) M) :
    Mono ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield S ℓ E)).unit.app M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine mono_of_mono_upperStar_map_of_cover _ _ 𝒰 fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := isFree_upperStar_of_isFree_mapMod _ (h𝒰 i)
  have := mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers ℓ E (𝒰.X i) n
  have hfree : Mono ((Mod.extendRestrictAdjunction
      (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).unit.app
      ((𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.obj M)) := by
    have hn := (Mod.extendRestrictAdjunction
      (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).unit.naturality e.inv
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [Iso.inv_comp_eq] at hn
    rw [hn]
    have : Mono ((Mod.comap (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).map
        ((Mod.extendScalars (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).map e.inv)) :=
      inferInstance
    have := mono_comp ((Mod.extendRestrictAdjunction
      (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).unit.app
        (Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (𝒰.X i)) n))
      ((Mod.comap (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).map
        ((Mod.extendScalars (padicIntegersToPadicSubfield (𝒰.X i) ℓ E)).map e.inv))
    exact mono_comp _ _
  have h := upperStar_map_unit_app_comp_comapUpperStarIso_inv_app
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (𝒰.f i) M
  rw [← Iso.app_inv, Iso.comp_inv_eq] at h
  rw [h]
  infer_instance


/-- **Lisse `E`-modules on connected normal Noetherian schemes contain lisse lattices**
(blueprint `lemma-global-lattice-normal-scheme`, first part). Let `X` be a connected Noetherian
scheme whose local rings are integrally closed domains. Every lisse (locally free) `E_X`-module
`L` contains a lisse `𝒪_{E,X}`-submodule `M` with `M[1/ℓ] = L`: there is a monomorphism
`ι : M ⟶ L` of `𝒪_{E,X}`-modules whose adjoint `E_X ⊗_{𝒪_{E,X}} M ⟶ L` is an isomorphism. -/
theorem exists_mono_isLocallyFree_padicIntegers_of_isIntegrallyClosed_stalk {X : Scheme.{u}}
    [IsNoetherian X] [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    (hL : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) X) L) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
      (ι : M ⟶ (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj L),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M ∧ Mono ι ∧
        IsIso (((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).homEquiv
          M L).symm ι) := by
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    exists_isLocallyFree_padicIntegers_extendScalars_iso_of_isIntegrallyClosed_stalk hX L hL
  have := mono_extendRestrictAdjunction_unit_app_of_isLocallyFree M hM
  refine ⟨M, (Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).unit.app M ≫
    (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).map e.hom, hM, mono_comp _ _, ?_⟩
  rw [← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  infer_instance

end AlgebraicGeometry.ProEtale
