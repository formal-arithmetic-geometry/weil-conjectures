/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldFiniteFree

/-!
# Restriction of scalars along `E_X ⟶ F_X` preserves constructibility

Let `E ≤ F` be finite subextensions of `ℚ̄_ℓ / ℚ_ℓ` and `X` a scheme. Since `F_X` is finite free
over `E_X` (`ProEtale.CondensedRing.exists_comap_regular_iso_finiteFree`), the restriction of
scalars along `E_X ⟶ F_X` preserves finitely presented, pro-étale locally finitely presented and
constructible module objects
(`ProEtale.CondensedRing.isConstructibleModuleObject_comap_padicSubfieldRingObjMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-! ### Restriction of scalars preserves constructibility -/

section Constructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- Restriction of scalars along `E_X ⟶ F_X` preserves finitely presented module objects, `F_X`
being finite free over `E_X`. -/
lemma isFinitelyPresented_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hN : Mod.IsFinitelyPresented (padicSubfieldRingObj X ℓ F) N) :
    Mod.IsFinitelyPresented (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj N) := by
  obtain ⟨d, hd⟩ := exists_comap_regular_iso_finiteFree ℓ h
  exact hN.comap_of_finiteFree _ (hd X).some

/-- Restriction of scalars along `E_X ⟶ F_X` preserves pro-étale locally finitely presented
module objects: it commutes with the pullbacks to the members of a pro-étale cover. -/
lemma isLocallyFinitelyPresented_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hN : IsLocallyFinitelyPresented (padicSubfieldRingObj X ℓ F) N) :
    IsLocallyFinitelyPresented (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj N) := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  refine ⟨𝒰, fun i ↦ (isFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj E) _ _).2 ?_⟩
  have e := (comapUpperStarIso (Profinite.padicSubfieldRingObjMap ℓ h) (𝒰.f i)).app N
  dsimp only [Functor.comp_obj] at e
  have h₁ := (isFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj F) _ _).1 (h𝒰 i)
  have h₂ := isFinitelyPresented_comap_padicSubfieldRingObjMap ℓ h h₁
  exact h₂.of_iso e

/-- Restriction of scalars along `E_X ⟶ F_X` preserves constructible module objects: it
commutes with the pullbacks to the strata of a stratification. -/
lemma isConstructibleModuleObject_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ F) M) :
    IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦
    (isLocallyFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj E) _ _).2 ?_⟩
  exact IsLocallyFinitelyPresented.of_iso
    ((comapUpperStarIso (Profinite.padicSubfieldRingObjMap ℓ h) (S.immersion a)).app M)
    (isLocallyFinitelyPresented_comap_padicSubfieldRingObjMap ℓ h
      ((isLocallyFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj F) _ _).1 (hS a)))

end Constructible

end AlgebraicGeometry.ProEtale.CondensedRing
