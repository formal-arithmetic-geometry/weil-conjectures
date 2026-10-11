module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Rank-one propagation for a Zariski pair

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-rank-one-propagation)
-/

@[expose] public section

universe u v

namespace RingHom

/-- A finite flat algebra whose reduction modulo an ideal in the Jacobson radical is the
base quotient has rank one at every prime.
Source: Stacks Project, More on Algebra, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-rank-one-propagation).
Proof:
1. Finite presentation and flatness make `B` finite projective, hence its localizations
   are finite free with locally constant rank, using
   `lem-weil-pbc-finitely-presented-flat-module-projective` and
   `lem-weil-pbc-finite-projective-rank-locally-constant`.
2. At primes containing `I`, the quotient isomorphism identifies the fibre with the
   residue field, forcing rank one.
3. The rank-one locus is open and contains every maximal ideal because `I` lies in the
   Jacobson radical; its closed complement is therefore empty.
-/
theorem zariskiPair_rank_one_propagation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.FinitePresentation A B]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hflat : RingHom.Flat (algebraMap A B))
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Nonempty
        (LocalizedModule p.primeCompl B ≃ₗ[Localization.AtPrime p]
          Localization.AtPrime p) := by
  sorry

end RingHom
