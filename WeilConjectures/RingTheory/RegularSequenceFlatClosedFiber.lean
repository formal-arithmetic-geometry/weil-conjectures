/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.FlatModInjective
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting a regular sequence from a closed fibre

A regular sequence in the closed fibre of a flat local homomorphism of Noetherian local rings
lifts to a regular sequence, and all prefix quotients are flat over the source.

## Implementation details

Induct on the prefix length. Each prefix quotient `S_i` is a Noetherian local ring flat over
`R`, and multiplication by the next element is injective on its closed fibre; the local
flatness criterion (Tags 00ME, 00MF) makes it injective on `S_i` with cokernel `S_{i+1}` flat
over `R`. The final quotient is nonzero since its closed fibre is.

## References

* [Stacks, Tag 00MG]
* [Stacks, Tags 00MF, 00ME]
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence

open scoped Pointwise in
private theorem flat_quotSMulTop_of_residue_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] [Module.Flat R M]
    (x : S)
    (h : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        ((LinearMap.lsmul S M x).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
          ((LinearMap.lsmul S M x).restrictScalars R)))) :
    IsSMulRegular M x ∧ Module.Flat R (QuotSMulTop x M) := by
  let u := (LinearMap.lsmul S M x).restrictScalars R
  have hc : Module.compHom M (algebraMap R S) = (inferInstance : Module R M) := by
    ext r m
    exact algebraMap_smul S r m
  have hcrit := flat_mod_injective (N := M) (M := M) (algebraMap R S)
    (fun r hr ↦ map_nonunit (algebraMap R S) r hr)
  rw [hc] at hcrit
  obtain ⟨hinj, hflat⟩ := hcrit u h
  have hrange : LinearMap.range u = (x • (⊤ : Submodule S M)).restrictScalars R := by
    ext y
    change (∃ z, x • z = y) ↔ y ∈ x • (⊤ : Submodule S M)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  refine ⟨hinj, ?_⟩
  have : Module.Flat R (M ⧸ LinearMap.range u) := hflat
  exact Module.Flat.of_linearEquiv
    ((Submodule.Quotient.restrictScalarsEquiv R (x • (⊤ : Submodule S M))).symm.trans
      (Submodule.quotEquivOfEq _ _ hrange.symm))

open scoped Pointwise in
/-- A flat prefix quotient remains flat after killing the next element, which is regular. -/
private theorem closedFiber_regular_step
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (fs : List S) (i : ℕ) (hi : i < fs.length) :
    letI : Algebra R S := φ.toAlgebra
    let I : Ideal S := (IsLocalRing.maximalIdeal R).map φ
    IsRegular (S ⧸ I) (fs.map (Ideal.Quotient.mk I)) →
    Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) →
    IsSMulRegular
        (S ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule S S))) fs[i] ∧
      Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := by
  let : Algebra R S := φ.toAlgebra
  dsimp only
  intro hreg hflat
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map φ
  let J : Ideal S := Ideal.ofList (fs.take i)
  let Q := S ⧸ J
  have : Module.Flat R Q := hflat
  have hlen : i < (fs.map (Ideal.Quotient.mk I)).length := by simpa using hi
  have hbar := hreg.regular_mod_prev i (by simpa using hi)
  have hJ : Ideal.ofList ((fs.map (Ideal.Quotient.mk I)).take i) =
      J.map (Ideal.Quotient.mk I) := by
    rw [← List.map_take, ← Ideal.map_ofList]
  have hsmul : (Ideal.ofList ((fs.map (Ideal.Quotient.mk I)).take i) •
      (⊤ : Submodule (S ⧸ I) (S ⧸ I))) = J.map (Ideal.Quotient.mk I) := by
    rw [hJ, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [hsmul] at hbar
  have hbar' : IsSMulRegular ((S ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (fs.map (Ideal.Quotient.mk I))[i] := hbar
  let e := DoubleQuot.quotQuotEquivCommₐ S I J
  have hQ : IsSMulRegular (Q ⧸ I.map (Ideal.Quotient.mk J)) fs[i] := by
    have hb : IsSMulRegular ((S ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) fs[i] := by
      rw [List.getElem_map] at hbar'
      exact (isSMulRegular_algebraMap_iff (A := S ⧸ I)).mp hbar'
    exact (e.toLinearEquiv.isSMulRegular_congr fs[i]).mp hb
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q) =
      (I.map (Ideal.Quotient.mk J)).restrictScalars R := by
    rw [Ideal.smul_top_eq_map, Ideal.map_map]
    rfl
  let eR : (Q ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))) ≃ₗ[R]
      Q ⧸ I.map (Ideal.Quotient.mk J) :=
    (Submodule.quotEquivOfEq _ _ hI).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)
  have hmod : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))
        ((LinearMap.lsmul S Q fs[i]).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
          ((LinearMap.lsmul S Q fs[i]).restrictScalars R))) := by
    intro a b hab
    apply eR.injective
    apply hQ
    have hcomm (a : Q ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))) :
        eR (((IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q)).mapQ
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))
          ((LinearMap.lsmul S Q fs[i]).restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
            ((LinearMap.lsmul S Q fs[i]).restrictScalars R))) a) = fs[i] • eR a := by
      induction a using Submodule.Quotient.induction_on with
      | H a => rfl
    change fs[i] • eR a = fs[i] • eR b
    rw [← hcomm, ← hcomm, hab]
  have hstep := flat_quotSMulTop_of_residue_injective (R := R) fs[i] hmod
  have hregular : IsSMulRegular
      (S ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule S S))) fs[i] := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hstep.1
  refine ⟨hregular, ?_⟩
  have : Module.Flat R (QuotSMulTop fs[i] Q) := hstep.2
  let eNext := Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter S fs[i] (fs.take i)
  have heq : Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule S S) =
      Ideal.ofList (fs[i] :: fs.take i) • (⊤ : Submodule S S) := by
    congr 1
    rw [List.take_succ_eq_append_getElem hi, Ideal.ofList_append]
    simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_comm]
    rw [bot_sup_eq]
  let e₁ := Submodule.quotEquivOfEq _ _ heq
  have heqJ : Ideal.ofList (fs.take i) • (⊤ : Submodule S S) = J := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e₂ := QuotSMulTop.congr fs[i] (Submodule.quotEquivOfEq _ _ heqJ)
  have heqNext : Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule S S) =
      Ideal.ofList (fs.take (i + 1)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e₀ := (Submodule.quotEquivOfEq _ _ heqNext).symm
  exact Module.Flat.of_linearEquiv
    ((e₀.trans (e₁.trans (eNext.trans e₂))).restrictScalars R)

/-- A regular sequence in the closed fibre of a flat local homomorphism of Noetherian
local rings lifts to a regular sequence, and all prefix quotients are flat over the source. -/
theorem isRegular_and_flat_quotient_of_closedFiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat) (fs : List S) :
    letI : Algebra R S := φ.toAlgebra
    let I : Ideal S := (IsLocalRing.maximalIdeal R).map φ
    IsRegular (S ⧸ I) (fs.map (Ideal.Quotient.mk I)) →
      IsRegular S fs ∧
        ∀ i : ℕ, i ≤ fs.length → Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) := by
  let : Algebra R S := φ.toAlgebra
  dsimp only
  intro hreg
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map φ
  have hprefix : ∀ i, i ≤ fs.length →
      Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) := by
    intro i hi
    induction i with
    | zero =>
      have : Module.Flat R S := hflat
      rw [List.take_zero, Ideal.ofList_nil]
      exact Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEqBot (⊥ : Submodule S S) rfl).restrictScalars R)
    | succ i ih =>
      exact (closedFiber_regular_step φ fs i (Nat.lt_of_succ_le hi)
        hreg (ih (Nat.le_of_succ_le hi))).2
  refine ⟨⟨⟨?_⟩, ?_⟩, hprefix⟩
  · intro i hi
    exact (closedFiber_regular_step φ fs i hi hreg (hprefix i (Nat.le_of_lt hi))).1
  · intro htop
    have htop' : Ideal.ofList fs = ⊤ := by
      simpa [Ideal.smul_eq_mul] using htop.symm
    have hmap : Ideal.ofList (fs.map (Ideal.Quotient.mk I)) = ⊤ := by
      rw [← Ideal.map_ofList, htop', Ideal.map_top]
    exact hreg.top_ne_smul (by rw [hmap, Submodule.top_smul])

end RingTheory.Sequence
