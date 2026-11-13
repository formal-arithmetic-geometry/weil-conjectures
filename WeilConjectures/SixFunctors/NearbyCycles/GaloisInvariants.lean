/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction

/-!

# Nearby cycles of an intermediate field as invariants: the formal part

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a field
extension, `N_Ω` the Galois layer (`NearbyCyclesModel.galoisLayer`) with generic fibre
`G_Ω = N.generic ×_{Spec L} Spec Ω` and projection `g : G_Ω ⟶ N.generic`. The pullback exchange
`α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection `N_Ω ⟶ N` is `Li^* Rj_*` of the derived
unit `A ⟶ Rg_* Lg^* A` at `A = Lε^* C`
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`),
and the action of `σ ∈ Aut(Ω/L)` on `Ψ_{N_Ω}` is `Li^* Rj_*` of the derived unit transport `u_σ`
along `Spec σ` (`NearbyCyclesModel.galoisLayerAut_autAction`).

Hence a retraction `R` of the derived unit which is invariant under all the `u_σ` gives a
retraction `r` of `α` whose idempotent `r ≫ α` is fixed by the action of `Aut(Ω/L)` on both sides
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_invariant`): `α` is the
inclusion of a direct summand of `Ψ_{N_Ω}`, cut out by a Galois-invariant projector onto the
invariant part. This is the formal part of the identification `Ψ_N = (Ψ_{N_Ω})^P` (SGA 4½,
[Th. finitude], Lemme 3.4; blueprint `proposition-external-kunneth-formula-nearby-cycles`,
identification (2)).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Transporting an invariant retraction along two functors.** Let `α = i ≫ F₂ (F₁ η ≫ c)` for
an isomorphism `i`, functors `F₁`, `F₂` and `c` with `F₂ c = κ` an isomorphism, and let `R` be a
retraction of `η` invariant under endomorphisms `u σ` (`u σ ≫ R = R`). If `ρ σ = κ⁻¹ ≫ F₂ (F₁ (u σ))
≫ κ`, then `α` has a retraction `r` whose idempotent `r ≫ α` is fixed by all `ρ σ` on the left. -/
lemma exists_retraction_of_eq_comp_map_comp_of_invariant {C D E : Type*} [Category C]
    [Category D] [Category E] (F₁ : C ⥤ D) (F₂ : D ⥤ E) {A T : C} {W : D} {P : E}
    (α : P ⟶ F₂.obj W) (i : P ≅ F₂.obj (F₁.obj A)) (c : F₁.obj T ⟶ W)
    (κ : F₂.obj (F₁.obj T) ≅ F₂.obj W) (hκ : κ.hom = F₂.map c) (η : A ⟶ T) (R : T ⟶ A)
    (hα : α = i.hom ≫ F₂.map (F₁.map η ≫ c)) (hR : η ≫ R = 𝟙 A) {ι : Type*}
    (u : ι → (T ⟶ T)) (ρ : ι → (F₂.obj W ⟶ F₂.obj W))
    (hρ : ∀ σ, ρ σ = κ.inv ≫ F₂.map (F₁.map (u σ)) ≫ κ.hom) (hinv : ∀ σ, u σ ≫ R = R) :
    ∃ r, α ≫ r = 𝟙 P ∧ ∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α := by
  rw [F₂.map_comp, ← hκ] at hα
  refine ⟨κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv, ?_, fun σ ↦ ?_⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, hR, F₁.map_id, F₂.map_id, Category.id_comp,
      Iso.hom_inv_id]
  · rw [hρ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, hinv]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]

set_option maxHeartbeats 1600000 in
-- matching the objects of the Galois layer with the unfolded composite of derived functors
-- (`κ`, `α`) is a large defeq check
/-- **Invariant retractions of the derived unit give invariant retractions of the exchange.** Let
`R : Rg_* Lg^* A ⟶ A` be a retraction of the derived unit at `A = Lε^* C`, for the projection
`g : G_Ω ⟶ N.generic`, which is invariant under the derived unit transports along all the
`Spec σ`, `σ ∈ Aut(Ω/L)`. Then the pullback exchange `α` of `N_Ω ⟶ N` has a retraction `r` whose
idempotent `r ≫ α` is fixed by the Galois action on both sides. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_invariant
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦Λ⟧).obj
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦Λ⟧).obj
          (L((N.ε)^*⟦Λ⟧).obj C)) ⟶ L((N.ε)^*⟦Λ⟧).obj C)
    (hR : (derivedUpperStarLowerStarAdjunction Λ
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = R) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      ∀ σ : Ω ≃ₐ[L] Ω,
        N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) ≫
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ∧
        (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) ≫
            N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C := by
  have hα := Hom.pullbackExchange_app_of_total_eq_id Λ N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) _ rfl
    (N.galoisLayerHom h Ω) rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  have key := exists_retraction_of_eq_comp_map_comp_of_invariant R((N.j)_*⟦Λ⟧) L((N.i)^*⟦Λ⟧) _
    ((leftDerivedUpperStarId Λ X').app _) _ (N.galoisLayerExchangeIso h Ω Λ C) rfl _ R hα hR
    (fun σ ↦ derivedUnitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C))
    (fun σ ↦ N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C))
    (fun σ ↦ galoisLayerAut_autAction Λ N h Ω σ C) hinv
  obtain ⟨r, h₁, h₂⟩ := key
  refine ⟨r, h₁, fun σ ↦ ⟨?_, ?_⟩⟩
  · exact h₂ σ
  · rw [Category.assoc, pullbackExchange_galoisLayerHom_app_comp_galoisLayerAction]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
