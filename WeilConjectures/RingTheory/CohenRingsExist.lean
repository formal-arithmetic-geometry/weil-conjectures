/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.CohenCompletionDVR
import WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField

/-!
# Existence of Cohen rings

Every field of prime characteristic `p` is the residue field of a Cohen ring
(`exists_cohenRing`).

## Implementation details

The residue field `ZMod p` of `ℤ_[p]` maps into `k`; the flat local extension theorem gives a
local `ℤ_[p]`-algebra `S` with maximal ideal `(p)` and residue field `k`. The Cohen ring is the
`m`-adic completion of `S`, which is a complete discrete valuation ring with maximal ideal `(p)`
and residue field `k`.

## References

* [Stacks, Tag 0328]
* [Stacks, Tag 03C3]
-/

@[expose] public section

universe u

/-- Every field of prime characteristic `p` is the residue field of a Cohen ring. -/
theorem exists_cohenRing (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [CharP k p] :
    ∃ (Λ : Type u) (_ : CommRing Λ),
      IsCohenRing p Λ ∧ Nonempty ((Λ ⧸ Ideal.span {(p : Λ)}) ≃+* k) := by
  let : Fact p.Prime := ⟨hp⟩
  let ι : IsLocalRing.ResidueField ℤ_[p] →+* k :=
    (ZMod.castHom (dvd_refl p) k).comp PadicInt.residueField.toRingHom
  obtain ⟨S, hComm, hLocal, φ, hLocalHom, hFlat, hMax, e, _⟩ :=
    IsLocalRing.exists_flat_local_extension_given_residue_field ℤ_[p] k ι
  let : CommRing S := hComm
  let : IsLocalRing S := hLocal
  have hMaxS : IsLocalRing.maximalIdeal S = Ideal.span {(p : S)} := by
    rw [← hMax, PadicInt.maximalIdeal_eq_span_p]
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  have hfg : (IsLocalRing.maximalIdeal S).FG := by
    rw [hMaxS]
    exact Submodule.fg_span_singleton _
  let Λ := AdicCompletion (IsLocalRing.maximalIdeal S) S
  obtain ⟨hDom, hDvr⟩ := adicCompletion_dvr_of_flat_padicInt p S φ hFlat hMaxS
  let : IsDomain Λ := hDom
  let : IsDiscreteValuationRing Λ := hDvr
  have hMap : (IsLocalRing.maximalIdeal S).map (algebraMap S Λ) =
      Ideal.span {(p : Λ)} := by
    calc
      _ = (Ideal.span {(p : S)}).map (algebraMap S Λ) :=
        congrArg (Ideal.map (algebraMap S Λ)) hMaxS
      _ = _ := by simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  have hMaxΛ : IsLocalRing.maximalIdeal Λ = Ideal.span {(p : Λ)} :=
    (AdicCompletion.maximalIdeal_eq_map_of_fg hfg).trans hMap
  have hComplete : IsAdicComplete (Ideal.span {(p : Λ)}) Λ := by
    rw [← hMap]
    exact AdicCompletion.isAdicComplete_self (IsLocalRing.maximalIdeal S) hfg
  have hKer : Ideal.span {(p : Λ)} =
      RingHom.ker (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal S)).toRingHom := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ hfg]
    exact hMap.symm
  let eΛ : (Λ ⧸ Ideal.span {(p : Λ)}) ≃+* IsLocalRing.ResidueField S :=
    (Ideal.quotEquivOfEq hKer).trans
      (RingHom.quotientKerEquivOfSurjective
        (AdicCompletion.evalOneₐ_surjective (IsLocalRing.maximalIdeal S)))
  exact ⟨Λ, inferInstance, ⟨hp, hDom, hDvr, hMaxΛ, hComplete⟩, ⟨eΛ.trans e⟩⟩
