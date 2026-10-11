/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.RingTheory.HenselianTerminology
import Sheaf.RingTheory.QuasiFiniteAtPrime
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod

/-!
# Finite-type algebras over henselian local rings

Source: Stacks Project, Algebra, Lemma 10.153.5 (Tag 04GJ)
(blueprint: lem-weil-pbc-henselian-finite-type-product-decomposition).
-/

universe u v

namespace HenselianLocalRing

/-- A finite-type algebra over a henselian local ring splits into finitely many module-finite
local algebras and a factor having no quasi-finite prime above the maximal ideal.
Source: Stacks Project, Algebra, Lemma 10.153.5 (Tag 04GJ)
(blueprint: lem-weil-pbc-henselian-finite-type-product-decomposition).

Proof:
1. Henselianity gives the étale retraction property, by
   `lem-weil-pbc-henselian-etale-retraction` (04GG (1) ⇒ (8)): every étale algebra with
   a rational point above the maximal ideal retracts to R through that point.
2. Apply `lem-weil-pbc-etale-retraction-finite-type-splitting` (04GG (11)) to obtain
   S ≃ A × B with A module-finite and no quasi-finite prime of B above the maximal ideal.
3. Apply `lem-weil-pbc-etale-retraction-finite-product-local` (04GG (10)) to A, obtaining
   finitely many local R-algebras Aᵢ and A ≃ ∏ᵢ Aᵢ. Each Aᵢ is module-finite because
   its projection from A is a surjective R-linear map, so images of generators generate it.
4. Compose the two algebra isomorphisms, keeping B unchanged. Its projection from S is
   surjective, so B is finite type; this supplies the instance needed by the recorded
   quasi-finiteness predicate. The empty product is allowed when A is zero, and B may be
   zero, when its condition on primes is vacuous. -/
theorem finiteType_exists_algEquiv_pi_prod
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [HenselianLocalRing R] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (A : Fin n → CommAlgCat.{v} R) (B : CommAlgCat.{v} R)
      (_ : Algebra.FiniteType R B),
      Nonempty (S ≃ₐ[R] (∀ i, A i) × B) ∧
        (∀ i, IsLocalRing (A i) ∧ Module.Finite R (A i)) ∧
        (∀ q : PrimeSpectrum B,
          q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
            ¬ Algebra.IsQuasiFiniteAtPrime R B q) := by
  sorry

end HenselianLocalRing
