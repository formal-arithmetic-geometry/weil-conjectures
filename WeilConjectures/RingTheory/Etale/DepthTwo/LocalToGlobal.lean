/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite étale algebras of bounded rank are local on the base

If `s ⊆ D` generates the unit ideal and `D_g ⊗_D X` is finite étale of rank at most `k` over
`D_g` for every `g ∈ s`, then `X` is finite étale of rank at most `k` over `D`
(`Algebra.etale_finite_of_span_eq_top`). This is used in the proof of the depth-two step of
blueprint `sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace Algebra

variable {D X : Type u} [CommRing D] [CommRing X] [Algebra D X]

/-- The localization `Localization.awayMap (algebraMap D X) g` is étale if
`D_g ⊗_D X` is étale over `D_g`. -/
lemma etale_awayMap_of_etale_tensor (g : D)
    (h : Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[D] X)) :
    (Localization.awayMap (algebraMap D X) g).Etale := by
  let Y := Localization.Away g ⊗[D] X
  let : Algebra X Y := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization.Away (algebraMap D X g) Y :=
    IsLocalization.Away.tensorRight g (Localization.Away g)
  let e : Y ≃ₐ[X] Localization.Away (algebraMap D X g) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap D X g)) Y _
  have heq : Localization.awayMap (algebraMap D X) g =
      e.toRingEquiv.toRingHom.comp (algebraMap (Localization.Away g) Y) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun d ↦ ?_)
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    have : algebraMap (Localization.Away g) Y (algebraMap D (Localization.Away g) d) =
        algebraMap X Y (algebraMap D X d) := by
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Y]
      change algebraMap D (Localization.Away g) d ⊗ₜ[D] (1 : X) =
        (1 : Localization.Away g) ⊗ₜ[D] algebraMap D X d
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact (e.commutes _).symm
  rw [heq]
  exact RingHom.Etale.respectsIso.1 _ e.toRingEquiv (RingHom.etale_algebraMap.mpr h)

/-- **Finite étale algebras of rank at most `k` are local on the base.** -/
theorem etale_finite_of_span_eq_top (s : Set D) (hs : Ideal.span s = ⊤) {k : ℕ}
    (H : ∀ g ∈ s, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[D] X) ∧
      Module.Finite (Localization.Away g) (Localization.Away g ⊗[D] X) ∧
      ∀ p, Module.rankAtStalk (R := Localization.Away g) (Localization.Away g ⊗[D] X) p ≤ k) :
    Algebra.Etale D X ∧ Module.Finite D X ∧ ∀ p, Module.rankAtStalk (R := D) X p ≤ k := by
  have hE : Algebra.Etale D X := RingHom.etale_algebraMap.mp
    (RingHom.Etale.ofLocalizationSpan (algebraMap D X) s hs
      fun g ↦ etale_awayMap_of_etale_tensor g.1 (H g.1 g.2).1)
  have hF : Module.Finite D X := Module.Finite.of_localizationSpan' s hs
      (Rₚ := fun g ↦ Localization.Away g.1) (Mₚ := fun g ↦ Localization.Away g.1 ⊗[D] X)
      (fun g ↦ TensorProduct.mk D _ X 1) fun g ↦ (H g.1 g.2).2.1
  refine ⟨hE, hF, fun p ↦ ?_⟩
  · obtain ⟨g, hgs, hgp⟩ : ∃ g ∈ s, g ∉ p.asIdeal := by
      by_contra! h
      exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 h))
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap D (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hgp
    obtain ⟨p', rfl⟩ := hp
    rw [← Module.rankAtStalk_baseChange]
    exact (H g hgs).2.2 p'

/-- **Finite étale base changes, locally.** If elements `h` of `B` with `B_h ⊗_B T₀` finite étale of
rank at most `k` over `B_h` cover `Spec D` (through `B → D`), then `D ⊗_B T₀` is finite étale of
rank at most `k` over `D`. -/
theorem etale_finite_tensor_of_forall_isPrime {B D T₀ : Type u} [CommRing B] [CommRing D]
    [CommRing T₀] [Algebra B D] [Algebra B T₀] {k : ℕ}
    (H : ∀ Q : Ideal D, Q.IsPrime → ∃ h : B, algebraMap B D h ∉ Q ∧
      Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
      ∀ p, Module.rankAtStalk (R := Localization.Away h) (Localization.Away h ⊗[B] T₀) p ≤ k) :
    Algebra.Etale D (D ⊗[B] T₀) ∧ Module.Finite D (D ⊗[B] T₀) ∧
      ∀ p, Module.rankAtStalk (R := D) (D ⊗[B] T₀) p ≤ k := by
  let s : Set D := {g | ∃ h : B, g = algebraMap B D h ∧
    Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
    Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
    ∀ p, Module.rankAtStalk (R := Localization.Away h) (Localization.Away h ⊗[B] T₀) p ≤ k}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hQ, hE⟩ := H m hm.isPrime
    exact hQ (hle (Ideal.subset_span ⟨h, rfl, hE⟩))
  refine etale_finite_of_span_eq_top s hs ?_
  rintro _ ⟨h, rfl, hE, hF, hk⟩
  let Bh := Localization.Away h
  let Dg := Localization.Away (algebraMap B D h)
  let : Algebra Bh Dg := (Localization.awayMap (algebraMap B D) h).toAlgebra
  have : IsScalarTower B Bh Dg := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, IsScalarTower.algebraMap_apply B D Dg]
  let e : Dg ⊗[Bh] (Bh ⊗[B] T₀) ≃ₐ[Dg] Dg ⊗[D] (D ⊗[B] T₀) :=
    (Algebra.TensorProduct.cancelBaseChange B Bh Dg Dg T₀).trans
      (Algebra.TensorProduct.cancelBaseChange B D Dg Dg T₀).symm
  refine ⟨.of_equiv e, .equiv e.toLinearEquiv, fun p ↦ ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv e.toLinearEquiv, Module.rankAtStalk_baseChange]
  exact hk _

end Algebra
