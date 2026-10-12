/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u v

/-- A finite intermediate algebra can normalize all primes over one maximal ideal.
Source: Stacks Project, Algebra, Tag 0333, second paragraph of the reverse implication.
(blueprint: lem-weil-pbc-local-normal-intermediate-algebra)

Proof: Put S = A \ m. Identify the fraction field of A_m with K by the unique
fraction-field isomorphism fixing A_m. N-1 supplies finitely many module generators
of its integral closure. Integral closure commutes with localization (Tag 0307),
so write these generators as x_j/s_j, with x_j integral over A and s_j in S.
Let B = A[x_1,...,x_n] inside K. It is contained in the integral closure of A, and
is finite over A since it has finitely many integral algebra generators.
The ring S^{-1}B contains every chosen generator and is contained in the integral
closure of A_m; therefore it is exactly that integral closure, hence is a normal
domain. For any prime q of B contracting to m, every element of S avoids q.
Consequently B_q is a further localization of S^{-1}B, and is integrally closed.
This proves only the local approximation step, without asserting finiteness of
A's normalization or requiring any normal principal open. -/
theorem exists_local_normal_intermediate_algebra (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) [m.IsMaximal]
    (hm : IsN1 (Localization.AtPrime m) (FractionRing (Localization.AtPrime m))) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
        IsIntegrallyClosed (Localization.AtPrime q) := by
  sorry
