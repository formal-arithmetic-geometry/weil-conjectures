/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.RingTheory.FiniteWContractibleComponents
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.ProEtale.IntegralLocal
import WeilConjectures.Mathlib.RingTheory.Idempotents

/-! # Finite finitely presented algebras over w-contractible rings -/

@[expose] public section

universe u

open Topology IsLocalRing
open scoped BigOperators TensorProduct

private theorem quotient_isLocalRing {R : Type u} [CommRing R] [IsWLocalRing R]
    (p : Ideal R) [p.IsPrime] : IsLocalRing (R ⧸ p) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := R ⧸ p)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, ?_⟩
  intro n hn
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hm' := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective (K := m) (H := hm)
  have hn' := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective (K := n) (H := hn)
  have hp_m : p ≤ m.comap (Ideal.Quotient.mk p) := by
    intro x hx
    change Ideal.Quotient.mk p x ∈ m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact m.zero_mem
  have hp_n : p ≤ n.comap (Ideal.Quotient.mk p) := by
    intro x hx
    change Ideal.Quotient.mk p x ∈ n
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact n.zero_mem
  let n' : PrimeSpectrum R := ⟨n.comap (Ideal.Quotient.mk p), hn'.isPrime⟩
  let m' : PrimeSpectrum R := ⟨m.comap (Ideal.Quotient.mk p), hm'.isPrime⟩
  exact congrArg PrimeSpectrum.asIdeal (WLocalSpace.eq_of_specializes
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal n').mpr hn')
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m').mpr hm')
    ((PrimeSpectrum.le_iff_specializes ⟨p, inferInstance⟩ n').mp hp_n)
    ((PrimeSpectrum.le_iff_specializes ⟨p, inferInstance⟩ m').mp hp_m))

private theorem quotient_henselian {R : Type u} [CommRing R] [IsWStrictlyLocalRing R]
    (p : Ideal R) [p.IsPrime] : HenselianLocalRing (R ⧸ p) := by
  have : IsLocalRing (R ⧸ p) := quotient_isLocalRing p
  let m := (IsLocalRing.maximalIdeal (R ⧸ p)).comap (Ideal.Quotient.mk p)
  have : m.IsMaximal := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective
  have : IsStrictlyHenselianLocalRing (Localization.AtPrime m) :=
    IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
  have hu (y : m.primeCompl) : IsUnit (Ideal.Quotient.mk p y) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact y.2
  let f : Localization.AtPrime m →+* (R ⧸ p) := IsLocalization.lift hu
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap R (Localization.AtPrime m) a, IsLocalization.lift_eq hu a⟩
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  obtain ⟨_, _, _, hs, _⟩ := isStrictlyHenselianLocalRing_quotient.{u, 0}
    (Localization.AtPrime m) inferInstance (RingHom.ker f) hker
  have : IsStrictlyHenselianLocalRing (R ⧸ p) :=
    IsStrictlyHenselianLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)
  infer_instance

private theorem quotient_integral_isLocalRing {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsWStrictlyLocalRing R]
    (p : Ideal S) [p.IsPrime] : IsLocalRing (S ⧸ p) := by
  have : HenselianLocalRing (R ⧸ p.comap (algebraMap R S)) :=
    quotient_henselian (p.comap (algebraMap R S))
  exact IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain
    (R := R ⧸ p.comap (algebraMap R S))

private theorem wLocal_of_integral {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsWStrictlyLocalRing R] : IsWLocalRing S := by
  refine ⟨{ eq_of_specializes := ?_, isClosed_closedPoints := ?_ }⟩
  · intro x c c' hc hc' hxc hxc'
    have : IsLocalRing (S ⧸ x.asIdeal) := quotient_integral_isLocalRing (R := R) x.asIdeal
    have hle : x.asIdeal ≤ c.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hxc
    have hle' : x.asIdeal ≤ c'.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hxc'
    have : c.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal c).mp hc
    have : c'.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal c').mp hc'
    have hker : RingHom.ker (Ideal.Quotient.mk x.asIdeal) = x.asIdeal :=
      Ideal.mk_ker
    have : (c.asIdeal.map (Ideal.Quotient.mk x.asIdeal)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le
        (f := Ideal.Quotient.mk x.asIdeal) Ideal.Quotient.mk_surjective (by rwa [hker])
    have : (c'.asIdeal.map (Ideal.Quotient.mk x.asIdeal)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le
        (f := Ideal.Quotient.mk x.asIdeal) Ideal.Quotient.mk_surjective (by rwa [hker])
    have heq : c.asIdeal.map (Ideal.Quotient.mk x.asIdeal) =
        c'.asIdeal.map (Ideal.Quotient.mk x.asIdeal) :=
      (IsLocalRing.eq_maximalIdeal inferInstance).trans
        (IsLocalRing.eq_maximalIdeal inferInstance).symm
    apply PrimeSpectrum.ext
    have := congrArg (Ideal.comap (Ideal.Quotient.mk x.asIdeal)) heq
    simpa only [Ideal.comap_map_mk hle, Ideal.comap_map_mk hle'] using this
  · have hclosed : closedPoints (PrimeSpectrum S) =
        (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' closedPoints (PrimeSpectrum R) := by
      ext q
      simp only [Set.mem_preimage, mem_closedPoints_iff,
        PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.comap_asIdeal]
      constructor
      · intro hq
        have := hq
        exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal
      · exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal
    rw [hclosed]
    exact WLocalSpace.isClosed_closedPoints.preimage (PrimeSpectrum.continuous_comap _)

private theorem strict_of_surjective {A T : Type u} [CommRing A] [CommRing T]
    [IsStrictlyHenselianLocalRing A] [Nontrivial T] (f : A →+* T)
    (hf : Function.Surjective f) : IsStrictlyHenselianLocalRing T := by
  have hker : RingHom.ker f ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top f)
  obtain ⟨_, _, _, hs, _⟩ := isStrictlyHenselianLocalRing_quotient.{u, 0}
    A inferInstance (RingHom.ker f) hker
  exact IsStrictlyHenselianLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)

private theorem strict_of_finite_fractions {A B T : Type u}
    [CommRing A] [CommRing B] [CommRing T] [IsStrictlyHenselianLocalRing A]
    [Algebra A B] [Module.Finite A B] [Algebra A T] [IsLocalRing T]
    [IsLocalHom (algebraMap A T)] (φ : B →ₐ[A] T)
    (hfrac : ∀ t : T, ∃ b s : B, IsUnit (φ s) ∧ φ s * t = φ b) :
    IsStrictlyHenselianLocalRing T := by
  classical
  obtain ⟨n, D, rings, algs, hens, locals, ⟨e⟩, finite, resfinite⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi A B
  let := rings
  let := algs
  let := hens
  let := locals
  have hstrict (i : Fin n) : IsStrictlyHenselianLocalRing (D i) := by
    have := resfinite i
    have : IsSepClosed (ResidueField (D i)) := Algebra.IsAlgebraic.isSepClosed
      (F := ResidueField A)
    exact ⟨this⟩
  let f : (∀ i, D i) →ₐ[A] T := φ.comp e.symm.toAlgHom
  have hsum : ∑ i : Fin n, f (Pi.single i 1) = 1 := by
    rw [← map_sum]
    simp only [Finset.univ_sum_single]
    exact map_one f
  obtain ⟨i, hi⟩ : ∃ i : Fin n, f (Pi.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hei : f (Pi.single i 1) = 1 := by
    have hId : IsIdempotentElem (f (Pi.single i 1)) := by
      apply IsIdempotentElem.map
      ext j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    exact hId.eq_zero_or_one_of_isLocalRing.resolve_left hi
  have hfactor (b : ∀ i, D i) : f (Pi.single i (b i)) = f b := by
    have hmul : Pi.single i 1 * b = Pi.single i (b i) := by
      ext j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    rw [← hmul, map_mul, hei, one_mul]
  let ψ : D i →+* T :=
    { toFun := fun a ↦ f (Pi.single i a)
      map_one' := hei
      map_zero' := by simp
      map_add' := by intro a b; rw [Pi.single_add, map_add]
      map_mul' := by intro a b; rw [Pi.single_mul, map_mul] }
  have hψ (a : A) : ψ (algebraMap A (D i) a) = algebraMap A T a := by
    exact (hfactor (algebraMap A (∀ i, D i) a)).trans (f.commutes a)
  have : IsLocalHom ψ := by
    apply ((local_hom_TFAE ψ).out 4 0).mp
    apply eq_maximalIdeal
    let P := (maximalIdeal T).comap ψ
    have : P.IsPrime := Ideal.comap_isPrime ψ _
    have : Module.Finite A (D i) := finite i
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) P
    have heq : P.comap (algebraMap A (D i)) = maximalIdeal A := by
      ext a
      change ψ (algebraMap A (D i) a) ∈ maximalIdeal T ↔ a ∈ maximalIdeal A
      rw [hψ]
      exact SetLike.ext_iff.mp (maximalIdeal_comap (algebraMap A T)) a
    rw [heq]
    infer_instance
  have hsurj : Function.Surjective ψ := by
    intro t
    obtain ⟨b, s, hs, ht⟩ := hfrac t
    have hs' : IsUnit (ψ ((e s) i)) := by
      change IsUnit (f (Pi.single i ((e s) i)))
      rw [hfactor]
      simpa only [f, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e.symm_apply_apply] using hs
    obtain ⟨v, hv⟩ := isUnit_of_map_unit ψ _ hs'
    have hb (b : B) : ψ ((e b) i) = φ b := by
      change f (Pi.single i ((e b) i)) = _
      rw [hfactor]
      simp [f]
    have ht' : ψ ((e s) i) * t = ψ ((e b) i) := by simpa only [hb] using ht
    refine ⟨↑v⁻¹ * (e b) i, ?_⟩
    rw [map_mul, ← ht', ← hv, ← mul_assoc, ← map_mul]
    simp
  have := hstrict i
  exact strict_of_surjective ψ hsurj

private theorem wStrict_of_finite {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [IsWStrictlyLocalRing R]
    (q : Ideal S) [q.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime q) := by
  let m := q.comap (algebraMap R S)
  have : m.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  let A := Localization.AtPrime m
  let T := Localization.AtPrime q
  have : IsStrictlyHenselianLocalRing A :=
    IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f : A →+* T := Localization.localRingHom m q (algebraMap R S) rfl
  let : Algebra A T := f.toAlgebra
  let : SMul A T := (inferInstance : Algebra A T).toSMul
  have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq fun r ↦
    (Localization.localRingHom_to_map m q (algebraMap R S) rfl r).symm
  have : IsLocalHom (algebraMap A T) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom m q (algebraMap R S) rfl))
  let B := A ⊗[R] S
  have : Module.Finite A B := Module.Finite.base_change R A S
  let φ : B →ₐ[A] T := Algebra.TensorProduct.lift (Algebra.ofId A T)
    (IsScalarTower.toAlgHom R S T) (fun _ _ ↦ Commute.all _ _)
  have hφ (s : S) : φ (Algebra.TensorProduct.includeRight s) = algebraMap S T s := by
    change φ (1 ⊗ₜ[R] s) = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  apply strict_of_finite_fractions φ
  intro t
  obtain ⟨⟨b, s⟩, ht⟩ := IsLocalization.surj q.primeCompl t
  exact ⟨Algebra.TensorProduct.includeRight b, Algebra.TensorProduct.includeRight s,
    by rw [hφ]; exact IsLocalization.map_units T s,
    by rw [hφ, hφ, mul_comm]; exact ht⟩

/-- A finite finitely presented algebra over a w-contractible ring is w-contractible.
Source: Stacks Project, Lemma 61.11.6, Section 61.11 (Tag 0986)
(blueprint: lem-ce-finite-finitely-presented-wcontractible).

Proof: For each prime p of R, w-locality makes R/p local. Its unique closed point m
allows a surjection R_m → R/p. Strict henselianity descends through this quotient, so R/p
is henselian. If q is prime in S, the integral domain S/q is integral over the henselian
local domain R/(q ∩ R), hence is local. Thus q has exactly one maximal specialization.
The closed points of Spec S are the inverse image of the closed points of Spec R by
integrality, and are closed. This proves w-locality of S.
For a maximal q of S with contraction m, put A = R_m. Decompose the finite A-algebra
A ⊗[R] S as a finite product of henselian local rings D_i. Their residue fields are finite
extensions of the separably closed residue field of A, hence separably closed. The map to
S_q factors through one D_i because a local ring has only trivial idempotents. This factor
map is local: its maximal ideal contracts to the maximal ideal of A, and integrality makes
that contraction maximal in D_i. The fraction presentation of S_q then makes D_i → S_q
surjective, since its denominators are units in D_i. Consequently S_q is strictly henselian.
Finally apply the component-space theorem to R and S, using the w-strict-locality just
proved. This supplies the remaining field of IsWContractibleRing S. The zero algebra is
allowed: its spectrum is empty and all maximal-localization conditions are vacuous. -/
theorem isWContractibleRing_of_finite_finitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsWContractibleRing R] [Module.Finite R S] [Algebra.FinitePresentation R S] :
    IsWContractibleRing S := by
  have : IsWLocalRing S := wLocal_of_integral (R := R)
  have : IsWStrictlyLocalRing S :=
    ⟨fun q _ ↦ wStrict_of_finite (R := R) q⟩
  exact ⟨extremallyDisconnected_components_of_finite_finitePresentation R S⟩
