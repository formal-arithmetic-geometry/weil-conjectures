module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! # Associated-prime detection of non-normal localizations

Source: Stacks Project, Algebra, Lemma Tag 0332, proof, Cases I and II.
(blueprint: lem-weil-pbc-normal-locus-associated-prime)
-/

@[expose] public section

universe u
namespace AlgebraicGeometry

/-- Every non-normal prime lies above a non-normal associated prime of the
principal quotient.

Source: Stacks Project, Algebra, Lemma Tag 0332, proof, Cases I and II.
(blueprint: lem-weil-pbc-normal-locus-associated-prime)

Proof:
1. Localize at `p` and apply Serre's criterion. Since `R_p` is not normal,
   there is a prime `q ≤ p` such that `R_q` fails S2, or has dimension at most
   one and is not regular. Localization of localization identifies these rings.
2. In either case `R_q` is not normal. Normality of `R_f` and preservation of
   normality by localization imply `f ∈ q`. Injectivity of localization in the
   domain makes the image of `f` a nonzero element of the maximal ideal of `R_q`.
3. The depth of `R_q` is at most one: in the S2 case its depth is strictly less
   than two; in the R1 case bound depth by dimension using the associated prime
   zero of the domain. Dimension zero cannot be the nonregular case, since the
   zero-dimensional local domain is a field.
4. The depth-drop theorem for the regular element `f` gives a nonzero quotient
   `R_q/fR_q` of depth zero. Its maximal ideal is associated: otherwise the
   nonzerodivisor theorem supplies a regular element in that ideal, a regular
   sequence of length one, contradicting depth zero.
5. Identify this quotient with the localization of `R/fR` at `q`. Descent of
   associated primes along localization contracts its associated maximal ideal
   to `q`, so `q` belongs to `associatedPrimes R (R ⧸ Ideal.span {f})`.
   These are exactly the witnesses asserted, with no finite-union or topology
   argument included. -/
theorem exists_nonNormal_associatedPrime_le
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (f : R) (hf : f ≠ 0)
    (hf_normal : IsDomain (Localization.Away f) ∧
      IsIntegrallyClosed (Localization.Away f))
    (p : PrimeSpectrum R)
    (hp : ¬ (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))) :
    ∃ q : PrimeSpectrum R,
      q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span {f}) ∧
      q.asIdeal ≤ p.asIdeal ∧
      ¬ (IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) := by
  sorry

end AlgebraicGeometry
