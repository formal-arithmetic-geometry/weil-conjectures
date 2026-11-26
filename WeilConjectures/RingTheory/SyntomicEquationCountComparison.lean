/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
import all WeilConjectures.RingTheory.SyntomicEquationCountComparisonCore
import WeilConjectures.RingTheory.SyntomicCodimensionLocalKernelGenerators
import WeilConjectures.RingTheory.SyntomicEquationCountComparisonDimension

/-!
# An equation-count comparison quotient at a syntomic prime

A finitely presented algebra satisfying the syntomic hypotheses at a prime is locally isomorphic
to a quotient of a polynomial ring by exactly the fibre codimension many equations.

## Implementation details

Given a presentation `φ : P → S` with kernel `I`, the local kernel generators `f` satisfy
`IP_Q = (f)P_Q`. Since `I` is finitely generated, clearing denominators gives `s ∉ Q` with
`s • I ⊆ (f)`; the induced map `(P/(f))_s → S_{φ(s)}` is then bijective, and the local fibre
dimensions are compared through the resulting open embedding of spectra.

## References

* [Stacks, Tag 00SY], proof of (3) ⇒ (2)
* [Stacks, Tag 00SG]
* [Stacks, Tag 00SC]
* [Stacks, Tag 00P2]
-/

@[expose] public section

universe u v
namespace Algebra

/-- A finitely presented algebra with the syntomic local hypotheses at `q` is, after inverting an
element `u` with `π u ∉ q`, a quotient `T = R[x_1, …, x_n] / (f_1, …, f_c)` with `c ≤ n`, where
the fibre of `T` has local dimension `n - c` at the prime corresponding to `q`. No global fibre
condition is asserted. -/
theorem exists_equationCount_comparison_of_syntomicAtPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hfp : FinitePresentation R S)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      ∃ (π : T →ₐ[R] S) (u : T),
        Function.Surjective π ∧ π u ∉ q.asIdeal ∧
        Function.Bijective
          (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u) ∧
        c ≤ n ∧
        topologicalKrullDimAt
          (PrimeSpectrum.preimageEquivFiber R T
            ((q.comap π.toRingHom).comap (algebraMap R T))
            ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ) := by
  obtain ⟨n, φ, hφ, hfg⟩ := hfp.out
  obtain ⟨c, f, hcn, hJ, hlocal, hdim⟩ :=
    exists_codimension_local_kernel_generators q n φ hφ hfg hflat hci
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := RingHom.ker φ.toRingHom
  let J : Ideal P := Ideal.span (Set.range f)
  let p : Ideal P := q.asIdeal.comap φ.toRingHom
  obtain ⟨s, hs, hkill⟩ := exists_multiplier_of_localized_le p.primeCompl
    (Localization.AtPrime p) I J hfg (le_of_eq hlocal.symm)
  let T := P ⧸ J
  let π : T →ₐ[R] S := Ideal.Quotient.liftₐ J φ (fun x hx ↦ hJ hx)
  let u : T := Ideal.Quotient.mk J s
  have hπ : ∀ x : P, π (Ideal.Quotient.mk J x) = φ x := by
    intro x
    rfl
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Ideal.Quotient.mk J x, hπ x⟩
  have hu : π u ∉ q.asIdeal := hs
  have hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u) := by
    constructor
    · change Function.Injective (IsLocalization.Away.map
        (Localization.Away u) (Localization.Away (π u)) π.toRingHom u)
      apply (IsLocalization.Away.map_injective_iff
        (Localization.Away (π u)) π.toRingHom u).mpr
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨1, ?_⟩
      rw [pow_one]
      change Ideal.Quotient.mk J s * Ideal.Quotient.mk J a = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hkill a hx
    · exact IsLocalization.Away.mapₐ_surjective_of_surjective u hsurj
  refine ⟨n, c, f, π, u, hsurj, hu, hbij, hcn, ?_⟩
  exact equationCount_comparison_dimension q π u hsurj hu hbij hdim

end Algebra
