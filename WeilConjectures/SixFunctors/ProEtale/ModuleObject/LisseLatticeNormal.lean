/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeCocycleNormal

/-!
# Lattices of lisse `E`-sheaves on connected normal schemes

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `S`
a connected Noetherian scheme whose local rings are integrally closed domains. Every lisse
(locally free) `E_S`-module `L` has a lattice: there is a locally free `𝒪_{E,S}`-module `L₀` with
`E_S ⊗_{𝒪_{E,S}} L₀ ≅ L`
(`ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso_of_isIntegrallyClosed_stalk`,
blueprint `lemma-global-lattice-normal-scheme`).

The proof is that of the regular case
`AlgebraicGeometry.ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`, with the
integral conjugation of the transition values on connected normal schemes
(`AlgebraicGeometry.exists_integral_conj_of_transitionValues_of_isIntegrallyClosed_stalk`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- **Lisse `E`-sheaves on connected normal Noetherian schemes have lattices** (blueprint
`lemma-global-lattice-normal-scheme`). See the module docstring. -/
theorem exists_isLocallyFree_padicIntegers_extendScalars_iso_of_isIntegrallyClosed_stalk
    {S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) S))
    (hL : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) S) L) :
    ∃ L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S) L₀ ∧
        Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield S ℓ E)).obj L₀ ≅ L) := by
  classical
  obtain ⟨𝒰, h𝒰, haff, hfree⟩ := CondensedRing.exists_finite_affine_cover_isFree_upperStar hL
  choose n e using hfree
  let e' (k : 𝒰.I₀) := (e k).some.symm
  have hsurj : ∀ s : S, ∃ k v, (𝒰.f k).base v = s :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ 𝒰.mem₀)).1
  -- the ranks agree at points with the same image
  have hn (j k : 𝒰.I₀) (v : 𝒰.X j) (v' : 𝒰.X k) (hvv' : (𝒰.f j).base v = (𝒰.f k).base v') :
      n j = n k := by
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f j) (g := 𝒰.f k) v v'
      hvv'
    exact rank_eq_of_comp_eq (e' j) (e' k) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition w
  -- the rank is constant, `S` being connected
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨k₀, v₀, -⟩ := hsurj s₀
  let A (m : ℕ) : Set S := {s | ∃ k, ∃ v : 𝒰.X k, (𝒰.f k).base v = s ∧ n k = m}
  have hpre (m : ℕ) (j : 𝒰.I₀) : (𝒰.f j).base ⁻¹' A m = if n j = m then Set.univ else ∅ := by
    ext v
    simp only [Set.mem_preimage, A, Set.mem_ofPred_eq]
    split_ifs with h
    · exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨j, v, rfl, h⟩⟩
    · exact ⟨fun ⟨i, v', hv', hi⟩ ↦ h ((hn j i v v' hv'.symm).trans hi), fun h ↦ h.elim⟩
  have hopen (m : ℕ) : IsOpen (A m) :=
    Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage 𝒰.f 𝒰.mem₀ _ fun j ↦ by
      rw [hpre]
      split_ifs <;> simp
  have hA : A (n k₀) = Set.univ := by
    refine IsClopen.eq_univ ⟨?_, hopen _⟩ ⟨(𝒰.f k₀).base v₀, k₀, v₀, rfl, rfl⟩
    have : (A (n k₀))ᶜ = ⋃ m ∈ ({n k₀}ᶜ : Set ℕ), A m := by
      ext s
      obtain ⟨i, v, rfl⟩ := hsurj s
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, A,
        Set.mem_ofPred_eq]
      constructor
      · exact fun h ↦ ⟨n i, fun h' ↦ h ⟨i, v, rfl, h'⟩, i, v, rfl, rfl⟩
      · rintro ⟨m, hm, i', v', hv', rfl⟩ ⟨i'', v'', hv'', h''⟩
        exact hm ((hn i' i'' v' v'' (hv'.trans hv''.symm)).trans h'')
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun m _ ↦ hopen m
  have hrank (k : 𝒰.I₀) (v : 𝒰.X k) : n k = n k₀ := by
    obtain ⟨i', v', hv', h'⟩ : (𝒰.f k).base v ∈ A (n k₀) := by
      rw [hA]
      trivial
    exact (hn k i' v v' hv'.symm).trans h'
  -- trivialisations of a single rank
  have he (k : 𝒰.I₀) : Nonempty (Mod.finiteFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) (𝒰.X k)) (n k₀) ≅
        (𝒰.f k)^*⟦Profinite.continuousMapRingObj E.1⟧.obj L) := by
    by_cases hk : Nonempty (𝒰.X k)
    · obtain ⟨v⟩ := hk
      rw [← hrank k v]
      exact ⟨e' k⟩
    · have : IsEmpty (𝒰.X k) := not_nonempty_iff.1 hk
      exact ⟨(isZero_mod_of_isEmpty _).iso (isZero_mod_of_isEmpty _)⟩
  have : Finite 𝒰.I₀ := h𝒰
  obtain ⟨Tval, hc, hc', hcomp, htrans, hself, hdesc⟩ :=
    exists_transitionValues L 𝒰 fun k ↦ (he k).some
  obtain ⟨g, hg, hg', hint₁, hint₂⟩ :=
    exists_integral_conj_of_transitionValues_of_isIntegrallyClosed_stalk hS 𝒰 Tval hc hc' hcomp
      htrans hself
  exact hdesc g hg hg' hint₁ hint₂

end AlgebraicGeometry.ProEtale
