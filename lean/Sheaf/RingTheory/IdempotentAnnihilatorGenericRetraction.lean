module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Defs.Induced
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Retraction onto minimal primes for idempotent-generated annihilators

Source: Hochster, *Totally integrally closed rings and extremal spaces*, discussion after
Proposition 5, pp. 776–777; the reduced-ring generalization and its proof are the DAG's
agent argument (blueprint: lem-sfb-idempotent-annihilator-generic-retraction).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A reduced commutative ring with principal idempotent annihilators has a continuous
retraction from its spectrum onto its minimal primes, with the specified basic-open formula.
The first clause identifies minimal primes with generic points of irreducible components.

Source: Hochster, discussion after Proposition 5, pp. 776–777, generalized by the DAG's
agent argument (blueprint: lem-sfb-idempotent-annihilator-generic-retraction).

Proof: (1) By the component description in Stacks Tag 00ES, the components are the zero
loci of minimal primes. The point-closure formula identifies their generic points with
these primes, and injectivity of prime zero loci gives the converse.
(2) For a minimal prime q and an idempotent e generating Ann(a), one has a ∈ q iff e ∉ q.
Indeed, Tag 00EU makes q R_q zero because R is reduced. If a ∈ q, the equality of
localization fractions (Tag 00CO) supplies s ∉ q with sa = 0. Writing s = et gives e ∉ q.
Conversely ae = 0 and primality give a ∈ q whenever e ∉ q.
(3) If q ⊆ p are primes and e is idempotent, e ∈ q iff e ∈ p. In the reverse direction,
e ∈ p implies 1-e ∉ p, hence 1-e ∉ q; applying primality to e(1-e) = 0 gives e ∈ q.
Exactly one of e and 1-e lies in any prime, also using their sum 1.
(4) Tag 00E0(4) supplies a minimal prime below each p. Any two such primes have identical
membership for every a by (2) and (3), so they coincide. Take r(p) to be this unique prime;
if p is already minimal, this gives r(p) = p.
(5) For q = r(p), a ∉ q iff e ∈ q iff e ∈ p iff 1-e ∉ p. This gives the displayed
inverse-image formula for every idempotent generator e of Ann(a).
(6) By the basic-open basis theorem, Tag 00E0(11), (14), (16), the subspace topology on
the minimal primes has basis D(a) intersected with that subspace. Part (5) makes each
inverse image open, proving continuity. For the zero ring both spectra are empty, so
all clauses hold for the unique empty map. -/
theorem exists_continuous_retraction_minimalPrimes_of_idempotent_annihilators
    (R : Type u) [CommRing R] [IsReduced R]
    (hann : ∀ a : R, ∃ e : R, IsIdempotentElem e ∧
      {b : R | a * b = 0} = Set.range (fun c : R ↦ e * c)) :
    (∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R ↔
      ∃ Z ∈ irreducibleComponents (PrimeSpectrum R), IsGenericPoint q Z) ∧
    ∃ r : PrimeSpectrum R → {q : PrimeSpectrum R // q.asIdeal ∈ minimalPrimes R},
      (∀ p : PrimeSpectrum R, (r p).val.asIdeal ≤ p.asIdeal ∧
        ∀ q : {q : PrimeSpectrum R // q.asIdeal ∈ minimalPrimes R},
          q.val.asIdeal ≤ p.asIdeal → q = r p) ∧
      Continuous r ∧
      (∀ q : {q : PrimeSpectrum R // q.asIdeal ∈ minimalPrimes R}, r q.val = q) ∧
      (∀ a e : R, IsIdempotentElem e →
        {b : R | a * b = 0} = Set.range (fun c : R ↦ e * c) →
        r ⁻¹' (Subtype.val ⁻¹' (basicOpen a : Set (PrimeSpectrum R))) =
          (basicOpen (1 - e) : Set (PrimeSpectrum R))) := by
  sorry

end PrimeSpectrum
