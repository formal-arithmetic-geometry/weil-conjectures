/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.TotallySplit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GenericFibre

/-!
# The rank of a Galois cover

A Galois cover `Z` of a scheme `Y` with finite group `G` has rank at most `|G|`: over an affine
open `V ⊆ Y`, the rank of `Γ(Z.P, π⁻¹ V)` over `Γ(Y, V)` at every prime is at most `|G|`
(`AlgebraicGeometry.Scheme.GaloisCover.rankAtStalk_app_le`). Indeed, the rank at a prime `p` is
the number of geometric points of the fibre over `p`, and `G` acts simply transitively on them.

This is used in the depth-two step of the proof of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.Etale

/-- A finite étale algebra `A` over a separably closed field `Ω` of dimension `n` has at least
`n` distinct points with values in `Ω`, given by the evaluations of `A ≅ Ωⁿ`. -/
lemma exists_injective_algHom_of_isSepClosed (Ω A : Type*) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.Etale Ω A] :
    ∃ ψ : Fin (Module.finrank Ω A) → (A →ₐ[Ω] Ω), Function.Injective ψ := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Ω A
  have hn : Module.finrank Ω A = n := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  refine ⟨fun i ↦ (Pi.evalAlgHom Ω (fun _ ↦ Ω) (Fin.cast hn i)).comp e.toAlgHom,
    fun i j hij ↦ ?_⟩
  have := congrArg (fun f : A →ₐ[Ω] Ω ↦ f (e.symm (Pi.single (Fin.cast hn j) 1))) hij
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at this
  by_contra h
  have h' : Fin.cast hn i ≠ Fin.cast hn j := fun h'' ↦ h (Fin.cast_injective hn h'')
  simp [h'] at this

end Algebra.Etale

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **The rank of a Galois cover.** For a Galois cover `Z` of `Y` with group `G` and an affine
open `V ⊆ Y`, the rank of `Γ(Z.P, π⁻¹ V)` over `Γ(Y, V)` is at most `|G|` at every prime:
the geometric points of the fibre form a single orbit under the free action of `G`. This is used
in the proof of blueprint `sbc-thm-spreading-finite-etale-galois`. -/
theorem rankAtStalk_app_le (Z : GaloisCover G Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (p : PrimeSpectrum Γ(Y, V)) :
    letI := (Z.π.app V).hom.toAlgebra
    Module.rankAtStalk (R := Γ(Y, V)) Γ(Z.P, Z.π ⁻¹ᵁ V) p ≤ Nat.card G := by
  let := (Z.π.app V).hom.toAlgebra
  have := Z.isFinite
  have := Z.etale
  have hW : IsAffineOpen (Z.π ⁻¹ᵁ V) := hV.preimage Z.π
  have : Module.Finite Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := IsFinite.finite_app Z.π _ hV
  have : Algebra.Etale Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := by
    have := HasRingHomProperty.appLE @Etale Z.π inferInstance ⟨_, hV⟩ ⟨_, hW⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  -- the geometric fibre over `p`
  let Ω := AlgebraicClosure p.asIdeal.ResidueField
  let A := Ω ⊗[Γ(Y, V)] Γ(Z.P, Z.π ⁻¹ᵁ V)
  have hrank : Module.rankAtStalk (R := Γ(Y, V)) Γ(Z.P, Z.π ⁻¹ᵁ V) p =
      Module.finrank Ω A := by
    have h := Module.rankAtStalk_baseChange (R := Γ(Y, V)) (M := Γ(Z.P, Z.π ⁻¹ᵁ V))
      (S := Ω) ⟨⊥, Ideal.isPrime_bot⟩
    have hp : PrimeSpectrum.comap (algebraMap Γ(Y, V) Ω) ⟨⊥, Ideal.isPrime_bot⟩ = p := by
      ext1
      rw [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot,
        IsScalarTower.algebraMap_eq Γ(Y, V) p.asIdeal.ResidueField Ω,
        RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField Ω).injective,
        Ideal.ker_algebraMap_residueField]
    rw [hp, Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.symm
  rw [hrank]
  obtain ⟨ψ, hψ⟩ := Algebra.Etale.exists_injective_algHom_of_isSepClosed Ω A
  -- the corresponding geometric points of `Z.P`
  let f (i : Fin (Module.finrank Ω A)) : Γ(Z.P, Z.π ⁻¹ᵁ V) →+* Ω :=
    (((ψ i).restrictScalars Γ(Y, V)).comp Algebra.TensorProduct.includeRight).toRingHom
  have hf (i) : (f i).comp (algebraMap Γ(Y, V) _) = algebraMap Γ(Y, V) Ω :=
    RingHom.ext fun r ↦
      (((ψ i).restrictScalars Γ(Y, V)).comp Algebra.TensorProduct.includeRight).commutes r
  have hfinj : Function.Injective f := fun i j hij ↦ hψ <|
    Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun l ↦ congrArg (· l) hij)
  let x (i : Fin (Module.finrank Ω A)) : Spec (.of Ω) ⟶ Z.P :=
    Spec.map (CommRingCat.ofHom (f i)) ≫ hW.fromSpec
  have hx (i) : x i ≫ Z.π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) Ω)) ≫ hV.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Z.π hV hW le_rfl,
      ← Scheme.Hom.app_eq_appLE, ← Category.assoc, ← Spec.map_comp, ← hf i]
    rfl
  have hxinj : Function.Injective x := fun i j hij ↦ by
    have := hW.isOpenImmersion_fromSpec
    have h1 := (cancel_mono hW.fromSpec).1 hij
    exact hfinj (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  rcases Nat.eq_zero_or_pos (Module.finrank Ω A) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hg (i) := Z.exists_comp_smul_eq (x ⟨0, hpos⟩) (x i) (by rw [hx, hx])
  choose g hg using hg
  have hginj : Function.Injective g := fun i j hij ↦ hxinj (by rw [← hg i, ← hg j, hij])
  simpa using Nat.card_le_card_of_injective g hginj

end AlgebraicGeometry.Scheme.GaloisCover
