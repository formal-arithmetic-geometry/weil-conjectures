/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.ExistsCompleteLocalFlatPresentation
import WeilConjectures.RingTheory.FlatPermanence
import WeilConjectures.RingTheory.FormallySmoothAdicCompleteSourceTarget
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete

/-!
# Flatness of adically formally smooth local ring maps

A local homomorphism of Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology on its target is flat.

## Implementation details

We first pass to maximal-ideal completions, which are Noetherian complete local rings, and
formal smoothness passes to the induced map. In the complete case, a flat presentation gives
surjections `R → A` and `S → B` of complete Noetherian local rings with `R → S` flat; with
`I = ker (R → A)`, the ring `C = S ⧸ I S` is flat over `A` and surjects onto `B` with closed
kernel. Lifting into the complete ring `C` (Tag 07NJ) gives an `A`-algebra section, so `B` is
a retract of the flat `A`-module `C`. Finally flatness descends from `B̂` to `B` since
`B → B̂` is faithfully flat.

## References

* [Stacks, Tag 07NP]
* [Stacks, Tag 07NI]
* [Stacks, Tag 07NJ]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A surjection `q : C → B` of complete local `A`-algebras, with `B` formally smooth over `A`
for its maximal-ideal-adic topology, has an `A`-algebra section. -/
private theorem section_of_formallySmoothAdic
    {A : Type u} {B : Type v} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsLocalRing B] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (h : Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B))
    (q : C →ₐ[A] B) (hq : Function.Surjective q) :
    ∃ s : B →ₐ[A] C, q.comp s = AlgHom.id A B := by
  let J := RingHom.ker q
  let I := IsLocalRing.maximalIdeal C
  have hlocal : IsLocalHom q.toRingHom := IsLocalHom.of_surjective q.toRingHom hq
  have hmax : I.map q.toRingHom = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective q.toRingHom hq
  have hJI : J ≤ I := by
    intro x hx
    have hx' : q x = 0 := hx
    have : q x ∈ IsLocalRing.maximalIdeal B := hx' ▸ Ideal.zero_mem _
    change x ∈ IsLocalRing.maximalIdeal C
    rw [← IsLocalRing.maximalIdeal_comap q.toRingHom]
    exact this
  have hclosed : J = ⨅ (n : ℕ) (_ : 1 ≤ n), J ⊔ I ^ n := by
    apply le_antisymm
    · exact le_iInf fun n => le_iInf fun _ => le_sup_left
    · intro x hx
      change q x = 0
      have he : (fun _ : Unit => q x) = (fun _ : Unit => (0 : B)) := by
        apply IsHausdorff.funext' (IsLocalRing.maximalIdeal B)
        intro n _
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        cases n with
        | zero => simp
        | succ n =>
          have hm := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx (n + 1)) (by omega)
          have hp : (IsLocalRing.maximalIdeal B) ^ (n + 1) =
              (I ^ (n + 1)).map q.toRingHom := by rw [Ideal.map_pow, hmax]
          rw [hp]
          change x ∈ ((I ^ (n + 1)).map q.toRingHom).comap q.toRingHom
          rw [Ideal.comap_map_of_surjective q.toRingHom hq,
            ← RingHom.ker_eq_comap_bot, sup_comm]
          exact hm
      exact congrFun he ()
  let e : (C ⧸ J) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hq
  obtain ⟨s, hs, _⟩ := h.exists_lift_into_complete (IsLocalRing.maximalIdeal B)
    I J 1 (by omega) (by simpa only [pow_one] using hJI) hclosed
    e.symm.toAlgHom 1 (by omega) (by
      intro x hx
      simp only [pow_one] at hx
      obtain ⟨y, rfl⟩ := hq x
      have hy : y ∈ I := by
        change y ∈ IsLocalRing.maximalIdeal C
        rw [← IsLocalRing.maximalIdeal_comap q.toRingHom]
        exact hx
      change e.symm (q y) ∈ I.map (Ideal.Quotient.mk J)
      rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
      exact Ideal.mem_map_of_mem _ hy)
  refine ⟨s, ?_⟩
  ext x
  have hx := AlgHom.congr_fun hs x
  have he := congrArg e hx
  change e (Ideal.Quotient.mk J (s x)) = e (e.symm x) at he
  rw [AlgEquiv.apply_symm_apply] at he
  exact he

/-- A local homomorphism of complete Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology on its target is flat. -/
private theorem flat_of_formallySmoothAdic_complete
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (φ : A →+* B) [IsLocalHom φ]
    (h : letI := φ.toAlgebra
      Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) : φ.Flat := by
  obtain ⟨R, S, rR, rS, lR, lS, nR, nS, cR, cS, g, q, b,
      lg, lq, lb, hq, hb, hg, hcomm⟩ := exists_completeLocal_flat_presentation φ
  let : CommRing R := rR
  let : CommRing S := rS
  have : IsLocalRing R := lR
  have : IsLocalRing S := lS
  have : IsNoetherianRing R := nR
  have : IsNoetherianRing S := nS
  have : IsAdicComplete (IsLocalRing.maximalIdeal S) S := cS
  let : Algebra R S := g.toAlgebra
  let I := RingHom.ker q
  let K := I.map g
  have hK : K ≤ RingHom.ker b := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change b (g x) = 0
    have he := RingHom.congr_fun hcomm x
    change q x = 0 at hx
    simpa [hx] using he
  have hproper : K ≠ ⊤ := by
    intro he
    have h1 : (1 : S) ∈ RingHom.ker b := hK (by rw [he]; trivial)
    simp at h1
  let C := S ⧸ K
  have : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing C :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  obtain ⟨nC, _, _, cC⟩ := quotient_complete_local S K hproper
  have : IsNoetherianRing C := nC
  have : IsAdicComplete (IsLocalRing.maximalIdeal C) C := cC
  let d : R ⧸ I →+* C := Ideal.quotientMap K g (Ideal.le_comap_map)
  have hd : d.Flat := by
    have : Module.Flat R S := hg
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
    change (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  let e := q.quotientKerEquivOfSurjective hq
  let a : A →+* C := d.comp e.symm.toRingHom
  have ha : a.Flat := (RingHom.Flat.of_bijective e.symm.bijective).comp hd
  let p : C →+* B := Ideal.Quotient.lift K b hK
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y, rfl⟩ := hb x
    exact ⟨Ideal.Quotient.mk K y, rfl⟩
  have hpa : p.comp a = φ := by
    ext x
    obtain ⟨y, rfl⟩ := hq x
    change p (d (e.symm (q y))) = φ (q y)
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
    exact RingHom.congr_fun hcomm y
  let : Algebra A B := φ.toAlgebra
  let : Algebra A C := a.toAlgebra
  let pA : C →ₐ[A] B := ⟨p, fun x => RingHom.congr_fun hpa x⟩
  have : Module.Flat A C := ha
  obtain ⟨s, hs⟩ := section_of_formallySmoothAdic h pA hp
  exact Module.Flat.of_retract s.toLinearMap pA.toLinearMap
    (LinearMap.ext fun x => AlgHom.congr_fun hs x)

/-- A local homomorphism of Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology on its target is flat. The algebra structure in the hypothesis
is the one induced by the given ring map. -/
theorem flat_of_formallySmoothAdic {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (h : letI : Algebra A B := φ.toAlgebra
      Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    φ.Flat := by
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing _
  have : IsNoetherianRing Bhat := AdicCompletion.isNoetherianRing _
  obtain ⟨ψ, hψ, hfs⟩ := Algebra.exists_formallySmoothAdic_completeSourceTarget A B φ
  have hcomm : ψ.comp (algebraMap A Ahat) = (algebraMap B Bhat).comp φ := by
    apply RingHom.ext
    intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    exact (hψ n _ a (AdicCompletion.evalₐ_of _ n a)).trans
      (AdicCompletion.evalₐ_of _ n (φ a)).symm
  have hlocal : IsLocalHom ψ := by
    apply ((IsLocalRing.local_hom_TFAE ψ).out 1 3).mpr
    rw [AdicCompletion.maximalIdeal_eq_map (R := A)]
    rw [Ideal.map_map]
    apply le_trans (le_of_eq
      (congrArg (fun f : A →+* Bhat => (IsLocalRing.maximalIdeal A).map f) hcomm))
    rw [← Ideal.map_map]
    exact (Ideal.map_mono (IsLocalRing.map_maximalIdeal_le φ)).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap B Bhat))
  have hflat : ψ.Flat := flat_of_formallySmoothAdic_complete ψ (by
    rw [AdicCompletion.maximalIdeal_eq_map (R := B)]
    exact hfs h)
  have hcompFlat : ((algebraMap B Bhat).comp φ).Flat := by
    rw [← hcomm]
    exact (RingHom.flat_algebraMap_iff.mpr inferInstance).comp hflat
  have : Module.FaithfullyFlat B Bhat := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply RingHom.flat_of_flat_module_of_faithfullyFlat_module (M := Bhat) φ
  exact hcompFlat

end RingHom
