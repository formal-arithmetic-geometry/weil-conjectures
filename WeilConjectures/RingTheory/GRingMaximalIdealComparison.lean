/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularThroughLocalization
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# A comparison local ring for the maximal-ideal G-ring criterion

If the completion maps of the localizations of a Noetherian ring `R` at its maximal ideals are
regular, then every prime localization `R_p` admits a flat local map to a Noetherian local ring
`B` whose composite with the completion map of `B` is regular.

## Implementation details

For a maximal ideal `m ⊇ p`, set `A = R_m`; faithful flatness of `A → Â` gives a prime `q` of `Â`
over `p A`, and `B = Â_q`. The composite `R → A → Â → B → B̂` is regular by composition of
regular maps (Tag 07QI), using that `Â` is a G-ring (Tag 07PS), and regularity through
localization gives the claim.

## References

* [Stacks, Tag 07PT] (proof, up to the final application of Tag 07NT)
* [Stacks, Tags 07QI, 07PS]
-/

@[expose] public section

universe w

/-- Maximal-local regularity supplies a flat local comparison map whose composite
with the comparison ring's completion map is regular: if the completion maps of all
localizations at maximal ideals are regular, then for every prime `p` there is a flat local map
`φ : R_p → B` to a Noetherian local ring `B` such that `R_p → B → B̂` is regular. -/
theorem exists_flat_local_regular_completion_comparison
    (R : Type w) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      RingHom.IsRegular
        (algebraMap (Localization.AtPrime m)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Localization.AtPrime m))))
    (p : Ideal R) [p.IsPrime] :
    ∃ (B : Type w) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ φ : Localization.AtPrime p →+* B,
        φ.Flat ∧
        (∀ x : Localization.AtPrime p,
          x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) →
            φ x ∈ IsLocalRing.maximalIdeal B) ∧
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ).IsRegular := by
  classical
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top ‹_›)
  let : m.IsMaximal := hm
  let A := Localization.AtPrime m
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing _
  have : Module.FaithfullyFlat A Ahat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hd : Disjoint (m.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr (fun x hx hp ↦ hx (hpm hp))
  let pA : Ideal A := p.map (algebraMap R A)
  have : pA.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl A p
    inferInstance hd
  have hpA : pA.comap (algebraMap R A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl A inferInstance hd
  obtain ⟨q, hq, hqA⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := Ahat) pA
  let : q.IsPrime := hq
  have hqR : p = q.comap (algebraMap R Ahat) := by
    have hqA' : q.comap (algebraMap A Ahat) = pA := hqA.over.symm
    rw [IsScalarTower.algebraMap_eq R A Ahat, ← Ideal.comap_comap, hqA', hpA]
  let B := Localization.AtPrime q
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  have : IsNoetherianRing B := inferInstance
  have : IsNoetherianRing Bhat := AdicCompletion.isNoetherianRing _
  let φ := Localization.localRingHom p q (algebraMap R Ahat) hqR
  have hc : (algebraMap A Ahat).IsRegular := h m
  have hRA : (algebraMap R A).IsRegular :=
    (IsLocalization.isRegular_and_fiber m.primeCompl).1
  have hRAhat : (algebraMap R Ahat).IsRegular :=
    hRA.comp_of_fiber_noetherian hc (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hAB : (algebraMap Ahat B).IsRegular :=
    (IsLocalization.isRegular_and_fiber q.primeCompl).1
  have hRB : (algebraMap R B).IsRegular :=
    hRAhat.comp_of_fiber_noetherian hAB (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hcB : (algebraMap B Bhat).IsRegular :=
    (isGRing_of_isNoetherianRing_of_isAdicComplete Ahat).2 q
  have hRBhat : (algebraMap R Bhat).IsRegular :=
    hRB.comp_of_fiber_noetherian hcB (fun p ↦ Ideal.isNoetherianRing_fiber p)
  have hflat : φ.Flat := hRAhat.1.localRingHom q p hqR
  have hlocal : ∀ x : Localization.AtPrime p,
      x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) →
        φ x ∈ IsLocalRing.maximalIdeal B := by
    intro x hx
    exact map_nonunit φ x hx
  let : Algebra (Localization.AtPrime p) Bhat :=
    ((algebraMap B Bhat).comp φ).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) Bhat :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      change algebraMap R Bhat x = algebraMap B Bhat (φ (algebraMap R _ x))
      rw [Localization.localRingHom_to_map]
      exact IsScalarTower.algebraMap_apply R Ahat Bhat x)
  refine ⟨B, inferInstance, inferInstance, inferInstance, φ, hflat, hlocal, ?_⟩
  exact RingHom.isRegular_of_comp_algebraMap_localization p.primeCompl hRBhat
