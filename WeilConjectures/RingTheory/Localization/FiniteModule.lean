/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Flat.Localization

/-!
# Localizations of finite modules

* `Module.exists_annihilator_of_subsingleton_localizedModule`: if `M` is finite and `S⁻¹M = 0`,
  then a single `s ∈ S` kills `M`.
* `Module.exists_localizationAway_equiv_finsupp_of_finite_projective`: a finite projective
  module is free of finite rank on a principal open neighbourhood of every prime.
-/

@[expose] public section

/-- If `M` is a finitely generated `A`-module with `S⁻¹M = 0`, then some `s ∈ S` annihilates
`M`: take the product of annihilating elements of finitely many generators.
(blueprint: `lem-weil-pbc-finite-module-localization-zero-annihilator`) -/
theorem Module.exists_annihilator_of_subsingleton_localizedModule {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (S : Submonoid A)
    [h : Subsingleton (LocalizedModule S M)] : ∃ s ∈ S, ∀ m : M, s • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  choose x hx hx' using LocalizedModule.subsingleton_iff.mp h
  refine ⟨∏ m ∈ s, x m, S.prod_mem fun m _ => hx m, ?_⟩
  rw [← Module.mem_annihilator, ← Submodule.annihilator_top, ← hs,
    Submodule.mem_annihilator_span]
  rintro ⟨m, hm⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x hm
  rw [hk, mul_comm, mul_smul, hx', smul_zero]

/-- A finite projective `A`-module `M` is locally free of finite rank: for every prime `p` there
is `f ∉ p` with `M_f ≃ A_f^r` for some `r`.
(blueprint: `lem-weil-pbc-finite-projective-prime-local-free`) -/
theorem Module.exists_localizationAway_equiv_finsupp_of_finite_projective {A M : Type*}
    [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    (p : Ideal A) [p.IsPrime] :
    ∃ f ∉ p, ∃ r : ℕ, Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
      (Fin r →₀ Localization.Away f)) := by
  have := Module.finitePresentation_of_projective A M
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  have : Nontrivial (Localization.Away f) :=
    (IsLocalization.map (M := .powers f) (T := p.primeCompl) (Localization.AtPrime p)
      (RingHom.id A) (Submonoid.powers_le.mpr hf)).domain_nontrivial
  exact ⟨f, hf, _, ⟨(Module.finBasis (Localization.Away f)
    (LocalizedModule.Away f M)).repr⟩⟩
