/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.NormalLocusOpen
import WeilConjectures.RingTheory.FiniteNormalCover
import WeilConjectures.RingTheory.FiniteNormalSup

/-!
# Patching finite intermediate algebras normal above maximal ideals

Finite subalgebras of the integral closure that are normal above individual maximal ideals patch
together to a finite subalgebra normal at all primes.

## Implementation details

Each finite intermediate algebra `C` has a closed non-normal locus (Tag 0332), whose image `Z_C`
in `Spec A` is closed. The complements of the `Z_C` cover `Spec A`; quasi-compactness gives
finitely many `C_i`, and their supremum is normal at all primes. The identification of this
supremum with the integral closure is not part of this file.

## References

* [Stacks, Tag 0333] (first and third paragraphs of the reverse implication)
* [Stacks, Tag 0332]
-/

@[expose] public section

universe u v

/-- Let `A` be a Noetherian domain with fraction field `K` such that `A_f` is normal for some
nonzero `f`. If for every maximal ideal `m` there is a finite subalgebra of the integral closure
of `A` in `K` that is normal at all primes over `m`, then there is a finite such subalgebra that
is normal at all primes. -/
theorem exists_finite_locally_normal_intermediate_algebra (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
        ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
          IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨s, S, hS, hs, hn⟩ := exists_finite_normal_cover A K hAway hLocal
  exact finite_normal_sup A K s S hS hs hn
