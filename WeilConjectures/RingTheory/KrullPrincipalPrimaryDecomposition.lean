/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.AsSubring
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Height

/-!
# Principal ideals in Krull domains

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Definition 4.10.1
and Proposition 4.10.3 with its proof, printed p. 89
(blueprint: lem-trf-krull-principal-primary-decomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- The height-one primes containing a nonzero element of a Krull domain admit a finite,
duplicate-free enumeration. The principal ideal is the intersection of the contractions of
its localizations at these primes, and each contraction has the corresponding prime as radical.
The three Krull-domain conditions are written explicitly; height one means a nonzero prime
with no prime strictly between zero and it. Localizations in the fraction field use Mathlib's
canonical localization subalgebras. An empty intersection of these subalgebras is the whole
fraction field; an empty intersection of ideals is the unit ideal.

Source: Swanson–Huneke, Definition 4.10.1 and Proposition 4.10.3, printed p. 89
(blueprint: lem-trf-krull-principal-primary-decomposition).

Proof:
1. Krull condition (iii) makes the height-one primes containing `b` finite, so enumerate them
   without repetitions as `P : Fin t → PrimeSpectrum D`.
2. Each localization at `P i` has dimension one by
   lem-weil-pbc-localization-dimension-chains-below-prime. Condition (i), locality and
   lem-sc-normal-dim1-dvr make it a DVR. Since `b ∈ P i`, its image is a nonunit; by
   lem-weil-pbc-dvr-unit-times-uniformizer-power it is a unit times a positive power of a
   uniformizer. The radical of that power ideal is the maximal ideal: the power ideal is
   contained in the maximal ideal, and the uniformizer belongs to its radical. Radicals
   commute with contraction, and lem-trf-localization-maximal-contraction identifies the
   contracted maximal ideal with `P i`. This proves the asserted radical equalities.
3. Every multiple of `b` lies in each contraction. Conversely, for `x` in all contractions,
   `x/b` lies in all listed localizations. At every other height-one prime `b` is a unit,
   so `x/b` lies in its localization too. Condition (ii) gives `x/b ∈ D`, hence `x ∈ bD`.
4. If `t = 0`, the same argument applies since `b` is a unit at every height-one prime:
   it gives `bD = D`, the empty ideal intersection. There are then no radical claims.
-/
theorem krull_principal_primary_decomposition
    (D : Type u) [CommRing D] [IsDomain D]
    (hlocal : ∀ P : PrimeSpectrum D, P.asIdeal ≠ ⊥ →
      (∀ Q : Ideal D, Q.IsPrime → Q < P.asIdeal → Q = ⊥) →
      IsNoetherianRing (Localization.AtPrime P.asIdeal) ∧
        IsDomain (Localization.AtPrime P.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime P.asIdeal))
    (hintersection : Set.range (algebraMap D (FractionRing D)) =
      ⋂ (P : PrimeSpectrum D) (_ : P.asIdeal ≠ ⊥)
        (_ : ∀ Q : Ideal D, Q.IsPrime → Q < P.asIdeal → Q = ⊥),
        (Localization.subalgebra.ofField (FractionRing D) P.asIdeal.primeCompl
          P.asIdeal.primeCompl_le_nonZeroDivisors : Set (FractionRing D)))
    (hfinite : ∀ x : D, x ≠ 0 → Set.Finite {P : PrimeSpectrum D |
      P.asIdeal ≠ ⊥ ∧ (∀ Q : Ideal D, Q.IsPrime → Q < P.asIdeal → Q = ⊥) ∧ x ∈ P.asIdeal})
    (b : D) (hb : b ≠ 0) :
    ∃ (t : ℕ) (P : Fin t → PrimeSpectrum D), Function.Injective P ∧
      (∀ Q : PrimeSpectrum D, (∃ i : Fin t, P i = Q) ↔
        Q.asIdeal ≠ ⊥ ∧ (∀ I : Ideal D, I.IsPrime → I < Q.asIdeal → I = ⊥) ∧
          b ∈ Q.asIdeal) ∧
      Ideal.span ({b} : Set D) =
        ⨅ i : Fin t, Ideal.comap (algebraMap D (Localization.AtPrime (P i).asIdeal))
          (Ideal.span ({algebraMap D (Localization.AtPrime (P i).asIdeal) b} :
            Set (Localization.AtPrime (P i).asIdeal))) ∧
      ∀ i : Fin t,
        (Ideal.comap (algebraMap D (Localization.AtPrime (P i).asIdeal))
          (Ideal.span ({algebraMap D (Localization.AtPrime (P i).asIdeal) b} :
            Set (Localization.AtPrime (P i).asIdeal)))).radical = (P i).asIdeal := by
  sorry

end RingTheory
