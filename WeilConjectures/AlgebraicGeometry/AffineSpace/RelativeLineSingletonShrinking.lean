/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Generic shrinking for a relative line with any singleton coordinate type

The source-library proof for `PUnit` works for every unique coordinate type.
(blueprint: lem-zl-relative-line-singleton-shrinking)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.AffineSpace

/-- After shrinking an integral affine base to a nonempty principal open, a nonempty open
of its relative affine line meets every fibre and has finite complement in every fibre.
The coordinate type can be any singleton, including `ULift (Fin 1)`.

Source: latest blueprint, thm-zl-relative-line-stratification.proof.md, paragraph 1;
the source-library theorem `AffineSpace.exists_basicOpen_forall_exists_mem_and_finite`.
(blueprint: lem-zl-relative-line-singleton-shrinking).

Proof: identify the line with the spectrum of the one-variable polynomial ring using
`MvPolynomial.uniqueAlgEquiv`. The proper closed complement has a nonzero polynomial in its
vanishing ideal. Invert its leading coefficient. On each resulting fibre the polynomial
has only finitely many prime zeros and there is a prime avoiding it, by the existing
polynomial-spectrum lemmas. Pull these statements back through the spectral homeomorphism.
The leading coefficient is nonzero, so its principal open is nonempty on the integral base.
-/
theorem exists_basicOpen_forall_exists_mem_and_finite_unique
    (n : Type u) [Unique n] {V : Scheme.{u}} [IsAffine V]
    [IsIntegral V] (U : 𝔸(n; V).Opens)
    (hU : (U : Set 𝔸(n; V)).Nonempty) :
    ∃ b : Γ(V, ⊤), (V.basicOpen b : Set V).Nonempty ∧ ∀ s ∈ V.basicOpen b,
      (∃ x ∈ U, (𝔸(n; V) ↘ V) x = s) ∧
        {x | x ∉ U ∧ (𝔸(n; V) ↘ V) x = s}.Finite := by
  set R := Γ(V, ⊤)
  set φ := isoOfIsAffine n V
  set e : MvPolynomial n R ≃ₐ[R] Polynomial R := MvPolynomial.uniqueAlgEquiv (R := R) _
  -- the points of `𝔸¹_V` are the primes of `R[X]`
  set Ψ := (Scheme.homeoOfIso φ).trans (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv)
  have hC : (e.symm.toRingEquiv : Polynomial R →+* MvPolynomial n R).comp
      Polynomial.C = MvPolynomial.C := by
    refine RingHom.ext fun r ↦ ?_
    exact e.symm.commutes r
  have hΨ (x : 𝔸(n; V)) :
      PrimeSpectrum.comap Polynomial.C (Ψ x) = V.isoSpec.hom ((𝔸(n; V) ↘ V) x) := by
    have h1 : φ.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        (𝔸(n; V) ↘ V) ≫ V.isoSpec.hom := by
      rw [← cancel_epi φ.inv, Iso.inv_hom_id_assoc, isoOfIsAffine_inv_over_assoc,
        Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun f ↦ f x) h1
    simp only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] at h2
    refine Eq.trans ?_ h2
    rw [← hC, PrimeSpectrum.comap_comp_apply]
    rfl
  -- the complement of `U`, as a closed proper subset of `Spec R[X]`
  set Z := Ψ '' (U : Set 𝔸(n; V))ᶜ
  have hZ : IsClosed Z := Ψ.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨g, hgZ, hgx₀⟩ : ∃ g ∈ PrimeSpectrum.vanishingIdeal Z, g ∉ (Ψ x₀).asIdeal := by
    by_contra! h
    have : Ψ x₀ ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact h
    obtain ⟨y, hy, hyx⟩ := this
    exact hy (Ψ.injective hyx ▸ hx₀)
  have hg0 : g ≠ 0 := fun h ↦ hgx₀ (h ▸ (Ψ x₀).asIdeal.zero_mem)
  have hgZ' (x : 𝔸(n; V)) (hx : x ∉ U) : g ∈ (Ψ x).asIdeal :=
    (PrimeSpectrum.mem_vanishingIdeal _ _).1 hgZ _ ⟨x, hx, rfl⟩
  refine ⟨g.leadingCoeff, ?_, fun s hs ↦ ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : V.basicOpen g.leadingCoeff = ⊥ := SetLike.coe_injective (by simpa using h)
    exact hg0 (Polynomial.leadingCoeff_eq_zero.1 ((basicOpen_eq_bot_iff _).1 this))
  have hbs : g.leadingCoeff ∉ (V.isoSpec.hom s).asIdeal := by
    rw [← V.toSpecΓ_preimage_basicOpen] at hs
    exact hs
  refine ⟨?_, ?_⟩
  · obtain ⟨Q, hgQ, hQ⟩ := Polynomial.exists_primeSpectrum_notMem_comap_C_eq _ hbs
    refine ⟨Ψ.symm Q, by_contra fun hx ↦ hgQ ?_, V.isoSpec.hom.homeomorph.injective ?_⟩
    · simpa using hgZ' _ hx
    · rw [Scheme.Hom.homeomorph_apply, Scheme.Hom.homeomorph_apply, ← hΨ,
        Homeomorph.apply_symm_apply, hQ]
  · refine ((Polynomial.finite_setOf_mem_comap_C_eq _ hbs).preimage Ψ.injective.injOn).subset
      fun x ⟨hxU, hxs⟩ ↦ ⟨hgZ' x hxU, ?_⟩
    rw [hΨ, hxs]

end AlgebraicGeometry.AffineSpace
