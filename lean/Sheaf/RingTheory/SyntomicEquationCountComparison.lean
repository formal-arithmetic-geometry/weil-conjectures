/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.LciConormalFreeRankCodimension
import Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference

/-!
# An equation-count comparison quotient at a syntomic prime

Source: Stacks Project, Algebra, Tag 00SY, middle of the proof of (3) ⇒ (2).
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison).
-/

@[expose] public section

universe u v
namespace Algebra

/-- A finitely presented algebra with the syntomic local hypotheses is locally a quotient
with exactly the fibre codimension many equations. No global fibre condition is asserted.
Source: Stacks Project, Algebra, Tag 00SY, proof of (3) ⇒ (2), from choosing a presentation
through Nakayama, with Tags 00SG, 00SC and 00P2 for the fibre dimension.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison).

Proof: write S = P/I for P = R[x_1,...,x_n] and a finitely generated ideal I. Scalar extension
identifies its fibre with k[x]/Ibar, where k is the residue field of the contracted prime.
At the canonical fibre prime the conormal module is free of rank c = n-d, where d is the
local dimension and d ≤ n (00SG and 00SC). Choose c elements f of I whose reductions form
a basis modulo the maximal ideal; Nakayama implies their images generate Ibar localized
at the inverse-image polynomial prime. Put T = P/(f) and let π : T → S be the quotient map.
Its kernel J is finitely generated. Localizing 0 → J → T → S → 0 at the polynomial prime
and tensoring with k stays exact on the left by flatness of S_q (00HL). The localized fibres
of T and S agree: the coefficient reduction from the localized polynomial ring onto
k[x] localized at the fibre prime is surjective with kernel the extended base prime,
and Ibar and (fbar) generate the same localized ideal. Thus the localized J modulo the
base prime is zero. Nakayama over the localized polynomial ring gives J localized equal
to zero. Choose one annihilating denominator for each of its finitely many generators and
multiply them to get u outside the inverse-image prime, with J_u = 0. The canonical map
T_u → S_{π(u)} is therefore bijective. Finally the chains of primes below the polynomial
fibre prime containing Ibar and (fbar) coincide, since the localized ideals coincide.
Their quotient-prime heights are equal; the height-difference formula 00P2 yields local
fibre dimension d = n-c for T at the inverse image of q. This proves both the equation
count inequality and the dimension equality. -/
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
            ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ) := by sorry

end Algebra
