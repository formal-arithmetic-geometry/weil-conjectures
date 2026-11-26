/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularPermanence
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion maps of G-rings are regular

The canonical map from a G-ring to its completion along any ideal is regular.

## Implementation details

Regularity is checked after localizing at each maximal ideal `m'` of the completion. With `m`
its inverse image in `A`, the local map `A_m → B = (Â)_{m'}` is flat, extends `m` to the maximal
ideal of `B`, and induces an isomorphism of completions. Composing gives a faithfully flat map
`B → Â_m` through which the (regular) completion map of `A_m` factors, so regularity descends
to `A_m → B`.

## References

* [Stacks, Tag 0AH2]
* [Matsumura, *Commutative Ring Theory*, Theorem 79]
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The canonical map from a G-ring to its completion along any ideal is regular. -/
theorem isRegular_of_isGRing (A : Type u) [CommRing A] (I : Ideal A) (hA : IsGRing A) :
    RingHom.IsRegular (algebraMap A (AdicCompletion I A)) := by
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing (AdicCompletion I A) := isNoetherianRing I
  apply (RingHom.isRegular_iff_localRingHom_prime_and_maximal
    (algebraMap A (AdicCompletion I A))).2.mpr
  intro q hq
  let p := q.comap (algebraMap A (AdicCompletion I A))
  have hfg : I.FG := I.fg_of_isNoetherianRing
  have hcomplete := isAdicComplete_self I hfg
  have hIq : Ideal.map (algebraMap A (AdicCompletion I A)) I ≤ q :=
    (IsAdicComplete.le_jacobson_bot _).trans (sInf_le ⟨bot_le, hq⟩)
  have hker : RingHom.ker (evalOneₐ I).toRingHom ≤ q := by
    rw [ker_evalOneₐ_eq_map I hfg]
    exact hIq
  have happrox : ∀ b : AdicCompletion I A, ∃ a : A,
      b - algebraMap A (AdicCompletion I A) a ∈ RingHom.ker (evalOneₐ I).toRingHom := by
    intro b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalOneₐ I b)
    refine ⟨a, ?_⟩
    change evalOneₐ I (b - algebraMap A (AdicCompletion I A) a) = 0
    rw [map_sub, show evalOneₐ I (algebraMap A (AdicCompletion I A) a) =
      Ideal.Quotient.mk I a from congrArg (fun f : A →+* A ⧸ I => f a)
        (evalOneₐ_comp_algebraMap_eq_mk I), ha, sub_self]
  have hmap : Ideal.map (algebraMap A (AdicCompletion I A)) p = q := by
    apply le_antisymm (Ideal.map_comap_le)
    intro b hb
    obtain ⟨a, ha⟩ := happrox b
    have hap : a ∈ p := by
      change algebraMap A (AdicCompletion I A) a ∈ q
      simpa only [sub_sub_cancel] using q.sub_mem hb (hker ha)
    have hd : b - algebraMap A (AdicCompletion I A) a ∈
        Ideal.map (algebraMap A (AdicCompletion I A)) I := by
      rwa [← ker_evalOneₐ_eq_map I hfg]
    have hIp : I ≤ p := Ideal.map_le_iff_le_comap.mp hIq
    simpa only [sub_add_cancel] using
      (Ideal.map (algebraMap A (AdicCompletion I A)) p).add_mem (Ideal.map_mono hIp hd)
        (Ideal.mem_map_of_mem _ hap)
  let R := Localization.AtPrime p
  let B := Localization.AtPrime q
  let φ : R →+* B :=
    Localization.localRingHom p q (algebraMap A (AdicCompletion I A)) rfl
  have hflat : φ.Flat := RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr inferInstance) q p rfl
  have hmax : Ideal.map φ (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      show φ.comp (algebraMap A R) =
        (algebraMap (AdicCompletion I A) B).comp (algebraMap A (AdicCompletion I A)) by
        apply RingHom.ext
        intro x
        exact Localization.localRingHom_to_map p q _ rfl x,
      ← Ideal.map_map, hmap, Localization.AtPrime.map_eq_maximalIdeal]
  have hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge) := by
    refine ⟨Ideal.quotientMap_injective' (IsLocalRing.maximalIdeal_comap φ).le, ?_⟩
    intro y
    obtain ⟨b, hb⟩ := q.algebraMap_residueField_surjective y
    obtain ⟨a, ha⟩ := happrox b
    refine ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R a), ?_⟩
    rw [Ideal.quotientMap_mk, Localization.localRingHom_to_map, ← hb]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    change algebraMap (AdicCompletion I A) B
      (algebraMap A (AdicCompletion I A) a) - algebraMap (AdicCompletion I A) B b ∈ _
    rw [← map_sub]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply Ideal.mem_map_of_mem
    simpa only [neg_sub] using q.neg_mem (hker ha)
  let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  obtain ⟨φhat, _, hbij, hcomm⟩ := RingHom.flat_local_completion_iso φ hflat hmax hres
  let e : Rhat ≃+* Bhat := RingEquiv.ofBijective φhat hbij
  let g : B →+* Rhat := e.symm.toRingHom.comp (algebraMap B Bhat)
  let : Algebra R B := φ.toAlgebra
  let : Algebra B Rhat := g.toAlgebra
  have htriangle : g.comp φ = algebraMap R Rhat := by
    rw [show g.comp φ = e.symm.toRingHom.comp
      ((algebraMap B Bhat).comp φ) from rfl, ← hcomm]
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply _
  let : IsScalarTower R B Rhat := IsScalarTower.of_algebraMap_eq' htriangle.symm
  have hgflat : g.Flat := RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B Bhat))
    (RingHom.Flat.of_bijective e.symm.bijective)
  have : Module.Flat B Rhat := hgflat
  have : IsLocalHom e.symm.toRingHom := e.symm.surjective.isLocalHom
  have : IsLocalHom g := by
    dsimp only [g]
    infer_instance
  have : Module.FaithfullyFlat B Rhat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.isRegular_of_isRegular_comp (C := Rhat) (hA.2 p) hgflat
    PrimeSpectrum.comap_surjective_of_faithfullyFlat

end AdicCompletion
