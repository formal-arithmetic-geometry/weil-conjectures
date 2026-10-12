module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Uniform containment of local maximal-ideal powers

Source: Stacks Project, Tags 07N9 and 0394.
(blueprint: lem-weil-pbc-local-tensor-quotient-power-bound)
-/

@[expose] public section

universe u v
namespace AdicCompletion

/-- One positive exponent works for all primes over a fixed base prime.
Source: Stacks Project, Tag 0394 (radical-power argument) and Tag 07N9 (finite fibre).
(blueprint: lem-weil-pbc-local-tensor-quotient-power-bound)

Proof: Set A = R_p and B = A tensor_R S. B is finite over the Noetherian local
ring A. Its closed fibre is a finite-dimensional algebra over A/m, hence Artinian.
Its finitely many primes correspond to Q = p.primesOver S. For q in Q, localizing
this fibre gives S_q/mS_q, an Artinian local ring. Thus its only prime is its maximal
ideal, so the radical of mS_q is N_q. The ring S_q is Noetherian, hence N_q is finitely
generated. The radical-power lemma gives c_q with N_q^c_q contained in mS_q.
Increase c_q to at least one. Take c to be the maximum of one and these finitely
many exponents. Ideal powers decrease with the exponent, so c works for every q.
When Q is empty take c = 1; the containment is vacuous. -/
theorem local_tensor_quotient_power_bound
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∃ c : ℕ, 1 ≤ c ∧ ∀ q : p.primesOver S,
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ c ≤
        m.map (Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p))) := by sorry

end AdicCompletion
