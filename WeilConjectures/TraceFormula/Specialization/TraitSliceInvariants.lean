/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCompRetraction
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The generic-slicing identification of nearby cycles with invariants

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and let
`M''` be its geometric slice over the trait `T = Spec K⟦t⟧` along the generic slice
`σ : T ⟶ 𝔸¹_S` (`NearbyCyclesModel.baseChange`), with total space `𝒳'' = 𝒳 ×_{𝔸¹_S} T`. The
projection `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`) factors through the change of trait
`M_T = M ×_S T` of `M`, with total space `𝒳 ×_S T`:
```
M'' --θ--> M_T --ψ--> M
```
where `θ` (`NearbyCyclesModel.geometricSliceTraitChangeHom`) is the base change of the identity of
`M` along `𝔸¹_S ⟶ S`: the slice of `M_T` along the section `T ⟶ 𝔸¹_T` given by the
coordinate `x ∈ K`. This splits the generic-slicing identification (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", identification (2); SGA 4½,
[Th. finitude], §§3.4, 3.7) into the two facts about traits used in the blueprint:

* the pullback exchange of `ψ` is invertible: nearby cycles do not change under the change of
  trait `T ⟶ S` (`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`);
* the pullback exchange of `θ` is the inclusion of the invariants of the pro-`p` kernel
  `P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` of the map of inertia groups, which acts on the nearby cycles of
  `M''` through a finite quotient
  (`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom`, unfinished).

Together they give the identification of the slicing exchange of `M` with the inclusion of the
`P'`-invariants (`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)

variable (x : K) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

include hb in
lemma comp_structureMorphism_eq_id_total_comp :
    b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = (Hom.id M).total ≫ q := by
  rw [Hom.id_total, Category.id_comp, hb]

/-- The morphism of models `θ : M'' ⟶ M_T` from the geometric slice `M''` of `M` along the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` to the change of trait `M_T = M ×_S Spec K⟦t⟧`: the base change
of the identity of `M` along `𝔸¹_S ⟶ S`. On total spaces it is the slice
`𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳 ×_S Spec K⟦t⟧` along the section of `𝔸¹_{K⟦t⟧}` given by `x`. -/
noncomputable abbrev geometricSliceTraitChangeHom :=
  (Hom.id M).baseChange hM hM (Category.comp_id q) (Category.comp_id (traitMap k' K)) hb
    (traitSlice_over x) (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
    (comp_structureMorphism_eq_id_total_comp hb) (traitSlice_over x)
    (by rw [Hom.id_generic, Category.id_comp])

lemma geometricSliceTraitChangeHom_total_comp :
    (geometricSliceTraitChangeHom hM x hb).total ≫
        (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)).total =
      (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).total :=
  (Hom.baseChange_total_comp hM hM _ _ _ _ (Hom.id M) _ _ _ _).trans (Category.comp_id _)

lemma geometricSliceTraitChangeHom_generic_comp :
    (geometricSliceTraitChangeHom hM x hb).generic ≫
        (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)).generic =
      (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).generic :=
  (Hom.baseChange_generic_comp hM hM _ _ _ _ (Hom.id M) _ _ _ _).trans (Category.comp_id _)

lemma geometricSliceTraitChangeHom_special_comp :
    (Hom.id M).baseChangeSpecial (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
        (comp_structureMorphism_eq_id_total_comp hb) (traitSlice_over x) ≫
        baseChangeSpecialMap hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _) =
      baseChangeSpecialMap hM b hb (traitSlice x) (traitSlice_over x) :=
  (Hom.baseChangeSpecial_comp hM hM _ _ _ _ (Hom.id M) _ _ _).trans (Category.comp_id _)

variable [IsSepClosed k'] [Fact (ringChar k').Prime] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **Nearby cycles of the slice of the change of trait are the `P'`-invariants** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", identification (2); SGA 4½,
[Th. finitude], §3.7; SGA 7, Exp. XIII, §1.3). The geometric slice `M''` of `M` is the slice of
the change of trait `M_T = M ×_S Spec K⟦t⟧` along the section `x` of `𝔸¹_{K⟦t⟧}`
(`NearbyCyclesModel.geometricSliceTraitChangeHom`). The pro-`p` kernel
`P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` of the map of inertia groups (`NearbyCyclesModel.GenericAut`)
acts on the nearby cycles of both (`NearbyCyclesModel.baseChangeAut`), trivially on those of
`M_T` by the invariance under change of trait. For bounded constructible `C`:
* the action of `P'` on `Ψ_{M''} C` factors through a finite quotient: a subgroup `V` of finite
  index acts trivially (continuity of the action, from the finiteness of `Ψ_{M''} C`);
* the pullback exchange `α_θ : Ψ_{M_T} C ⟶ Ψ_{M''} C` is the inclusion of the invariants: it is a
  split monomorphism whose idempotent is `1 / [P' : V]` times the sum of the actions of
  representatives of `P' ⧸ V` (Hochschild–Serre for the pro-`p` cover
  `Spec Ω_K ⟶ (Spec K⟦t⟧ ×_S Spec Ω)_red`; `[P' : V]` is a power of `p`, invertible in `ℚ̄_ℓ`).

Unfinished: the finite quotient. With torsion coefficients the invariant projector exists by
continuity along the finite Galois layers
(`exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`),
and with `ℚ̄_ℓ`-coefficients the exchange of a generic slice trait is a split monomorphism
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`). Neither
gives a subgroup `V` of finite index acting trivially on the `ℚ̄_ℓ`-complex `Ψ_{M''} C`, nor that
the idempotent is the projector onto all the invariants. This needs that the action of `P'` on
the torsion nearby cycles of `M''` factors through a finite quotient, i.e. Deligne's finiteness
theorem with torsion coefficients (SGA 4½, [Th. finitude], Thm. 3.2), which is not formalised:
only the `ℚ̄_ℓ` version exists (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`),
and it does not control the torsion of the integral nearby cycles. -/
theorem exists_subgroup_pullbackExchange_sliceTraitChangeHom
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ r, ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ r = 𝟙 _ ∧
        Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) •
          (r ≫ ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
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
of the change of trait, invertible by
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`, and of the
inclusion of the `P'`-invariants
`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp`). -/
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
  have hD := exists_subgroup_pullbackExchange_sliceTraitChangeHom (ℓ := ℓ) hM hb
    (C := L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) hA'
  obtain ⟨V, hV, htriv, r, hr, havg⟩ := hD
  have hs := isIso_pullbackExchange_baseChangeHom_traitMap_of_generic (ℓ := ℓ) hM (A := A) hA
  refine ⟨V, hV, fun σ hσ ↦ eq_id_of_naturality_of_iso _
    (fun g ↦ Hom.autAction_naturality _ _ g)
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (Category.id_comp (𝟙 X))).app A) (htriv σ hσ), ?_⟩
  have key := exists_retraction_pullbackExchange_of_comp (Profinite.padicAlgClRingObj ℓ)
    (geometricSliceTraitChangeHom hM (traitSliceCoord k') hb)
    (baseChangeHom hM q (Category.comp_id q) (traitMap k' (traitSliceField k'))
      (Category.comp_id _))
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
    (geometricSliceTraitChangeHom_special_comp hM (traitSliceCoord k') hb)
    (geometricSliceTraitChangeHom_total_comp hM (traitSliceCoord k') hb)
    (geometricSliceTraitChangeHom_generic_comp hM (traitSliceCoord k') hb) A
    (by exact_mod_proofs hs)
    Finset.univ (Fintype.card (GenericAut k' (traitSliceField k') ⧸ V))
    (fun σ : GenericAut k' (traitSliceField k') ⧸ V ↦ (baseChangeAut hM b hb
      (traitSlice (traitSliceCoord k')) (traitSlice_over _) σ.out).autAction
        (Profinite.padicAlgClRingObj ℓ))
    (fun σ _ _ g ↦ Hom.autAction_naturality _ _ g) r (by exact_mod_proofs hr)
    (by exact_mod_proofs havg)
  exact_mod_proofs key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
