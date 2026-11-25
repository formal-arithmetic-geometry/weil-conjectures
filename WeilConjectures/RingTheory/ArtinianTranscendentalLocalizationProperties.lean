/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# A component of the transcendental polynomial localization argument

Structural properties of the localization of `D[t]` at the prime pulled back from an Artinian
local `D`-algebra along a transcendental element.

## Implementation details

Transcendence shows that `P = m_D[t]`, so `D[t]_P` is Noetherian local with nilpotent maximal
ideal, hence Artinian; the polynomial algebra is smooth, so the localization is essentially
smooth. All properties are transported across the `ULift` ring equivalence. The flatness
assumption is not needed for this component.

## References

* [Stacks, Tag 07FI] (Smoothing Ring Maps, proof)
-/

@[expose] public section
set_option autoImplicit false
universe u v z
namespace Algebra

/-- Let `D → S` be a local map of Artinian local rings and `x ∈ S` with transcendental residue
over the residue field of `D`. The localization of `D[t]` at the inverse image `P` of the
maximal ideal of `S` under `t ↦ x` is Artinian local, local and essentially smooth over `D`. -/
theorem localization_artinian_transcendental_properties
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    IsLocalRing T ∧ IsArtinianRing T ∧ IsLocalHom (algebraMap D T) ∧
      EssentiallySmooth D T := by
  have _ := hflat
  dsimp
  let P : Ideal (Polynomial D) :=
    (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
  have hP : P = Ideal.map (Polynomial.C : D →+* Polynomial D)
      (IsLocalRing.maximalIdeal D) := by
    ext f
    rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
    have he : Polynomial.aeval (IsLocalRing.residue S x)
        (f.map (IsLocalRing.residue D)) =
        IsLocalRing.residue S (Polynomial.eval₂RingHom (algebraMap D S) x f) := by
      have heq : (Polynomial.aeval (IsLocalRing.residue S x)).toRingHom.comp
          (Polynomial.mapRingHom (IsLocalRing.residue D)) =
          (IsLocalRing.residue S).comp (Polynomial.eval₂RingHom (algebraMap D S) x) := by
        ext a <;> simp [IsLocalRing.ResidueField.algebraMap_residue]
      exact DFunLike.congr_fun heq f
    constructor
    · intro hf
      have hz : f.map (IsLocalRing.residue D) = 0 :=
        (transcendental_iff.mp hx) _ (he.trans ((IsLocalRing.residue_eq_zero_iff _).mpr hf))
      intro n
      have hn := congrArg (fun p => Polynomial.coeff p n) hz
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
        IsLocalRing.residue_eq_zero_iff] using hn
    · intro hf
      have hz : f.map (IsLocalRing.residue D) = 0 := by
        ext n
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
          IsLocalRing.residue_eq_zero_iff] using hf n
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [← he, hz, map_zero]
  let L := Localization.AtPrime P
  have : IsNoetherianRing D := inferInstance
  have : IsNoetherianRing (Polynomial D) := inferInstance
  have : IsArtinianRing L := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal L).mpr
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal D).mp
      (inferInstance : IsArtinianRing D)
    refine ⟨n, ?_⟩
    have hm := congrArg (Ideal.map (algebraMap (Polynomial D) L)) hP
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hm, Ideal.map_map,
      ← Ideal.map_pow, hn]
    exact Ideal.map_bot
  have : IsLocalHom (algebraMap D L) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap D L)).out 4 1).mp
    intro d hd
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (Polynomial D) L,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (S := L) P]
    change Polynomial.C d ∈ P
    rw [hP, Ideal.mem_map_C_iff]
    intro n
    by_cases hn : n = 0
    · simpa [hn] using hd
    · simp [Polynomial.coeff_C, hn]
  have : IsLocalRing (ULift.{max u v z} L) := ULift.ringEquiv.symm.isLocalRing
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact ULift.ringEquiv.symm.isArtinianRing
  · refine ⟨fun d hd => ?_⟩
    apply isUnit_of_map_unit (algebraMap D L) d
    exact hd.map (ULift.ringEquiv : ULift.{max u v z} L ≃+* L).toRingHom
  · let Q := ULift.{max u v z} (Polynomial D)
    let e : Polynomial D ≃ₐ[D] Q := ULift.algEquiv.symm
    have : Smooth D (Polynomial D) := ⟨inferInstance, inferInstance⟩
    have : Smooth D Q := Smooth.of_equiv e
    let M : Submonoid Q := Submonoid.map e P.primeCompl
    exact ⟨Q, inferInstance, inferInstance, inferInstance, M,
      ⟨(ULift.algEquiv (R := D)).trans
        (IsLocalization.algEquivOfAlgEquiv (M := P.primeCompl) (T := M)
          L (Localization M) e rfl)⟩⟩


end Algebra
