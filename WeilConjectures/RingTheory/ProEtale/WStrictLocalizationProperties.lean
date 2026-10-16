/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Properties of the étale contraction and of the strict w-local cover

We bundle the properties of the ind-étale contraction `R^e = IndEtaleContraction R`
(blueprint `lem-weil-pbc-etale-contraction`) and of the strict w-local cover
`C_A = WStrictLocalization A` (blueprint `lem-weil-pbc-strict-w-cover`).
-/

@[expose] public section

universe u

open PrimeSpectrum

/-- **Blueprint `lem-weil-pbc-etale-contraction`**: the map `R → R^e` is faithfully flat and
ind-étale, every faithfully flat étale `R^e`-algebra has a section, and every maximal localization
of `R^e` is strictly henselian. -/
theorem IndEtaleContraction.spec (R : Type u) [CommRing R] :
    Algebra.IndEtale R (IndEtaleContraction R) ∧
      Module.FaithfullyFlat R (IndEtaleContraction R) ∧
      (∀ (S : Type u) [CommRing S] [Algebra (IndEtaleContraction R) S],
        Algebra.Etale (IndEtaleContraction R) S →
        Module.FaithfullyFlat (IndEtaleContraction R) S →
        Nonempty (S →ₐ[IndEtaleContraction R] IndEtaleContraction R)) ∧
      ∀ (m : Ideal (IndEtaleContraction R)) [m.IsMaximal],
        IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  refine ⟨inferInstance, inferInstance, fun S _ _ hS hff ↦ ?_, fun m _ ↦
    IsStrictlyHenselianLocalRing.localization_atPrime_indEtaleContraction R m⟩
  obtain ⟨g, hg⟩ := RingHom.Etale.exists_comp_eq_id_indContraction
    (algebraMap (IndEtaleContraction R) S) (RingHom.etale_algebraMap.mpr hS)
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  exact ⟨{ g with commutes' := fun r ↦ congrArg (fun φ : _ →+* _ ↦ φ r) hg }⟩

/-- **Blueprint `lem-weil-pbc-strict-w-cover`**: the algebra `C_A = WStrictLocalization A` is
faithfully flat and ind-étale over `A`, its spectrum is w-local, its maximal local rings are
strictly henselian, and its closed points surject onto `Spec A`. -/
theorem WStrictLocalization.spec (A : Type u) [CommRing A] :
    Algebra.IndEtale A (WStrictLocalization A) ∧
      Module.FaithfullyFlat A (WStrictLocalization A) ∧
      IsWLocalRing (WStrictLocalization A) ∧
      (∀ (m : Ideal (WStrictLocalization A)) [m.IsMaximal],
        IsStrictlyHenselianLocalRing (Localization.AtPrime m)) ∧
      Set.SurjOn (PrimeSpectrum.comap (algebraMap A (WStrictLocalization A)))
        (closedPoints (PrimeSpectrum (WStrictLocalization A))) Set.univ := by
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun m _ ↦ IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m,
    fun p _ ↦ ?_⟩
  obtain ⟨x, hx, hxp⟩ := WStrictLocalization.exists_mem_zeroLocus_comap_eq A p
  rw [WStrictLocalization.zeroLocus_map_eq_closedPoints] at hx
  exact ⟨x, hx, hxp⟩
