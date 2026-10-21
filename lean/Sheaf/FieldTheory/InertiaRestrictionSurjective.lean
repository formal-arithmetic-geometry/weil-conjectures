/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral

/-!
# Surjectivity of restriction on inertia in a Galois tower

Source: Stacks Project, More on Algebra, Tag 0BSX,
`lemma-one-orbit-geometric-galois-compare`, inertia-surjectivity clause.
(blueprint: lem-dl-a1-inertia-restriction-surjective)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Ideal

/-- Restriction from upper inertia has image exactly the inertia at the contracted prime.
Thus it induces a surjective group homomorphism between these inertia subgroups.
Here `inertia` means trivial action on the quotient ring; this automatically stabilizes
its ideal and is equivalent to trivial action on the fraction field of the quotient.

Source: Stacks Project, More on Algebra, Tag 0BSX,
`lemma-one-orbit-geometric-galois-compare`, inertia-surjectivity clause.
(blueprint: lem-dl-a1-inertia-restriction-surjective)

Proof:
1. By `lem-weil-pbc-integral-closure-algebraic-extension-normal`, the integral closures
   B and C are normal domains with fraction fields L and M. Moreover C is the integral
   closure of B in M: integrality over A implies integrality over B, and integrality over
   B implies integrality over C, which is integrally closed in M. Contraction embeds
   B/q into C/r and therefore embeds their fraction fields.
2. Normality of L/K makes restriction of every K-automorphism of M well-defined on L.
   Monic equations show that these automorphisms preserve both integral closures.
   Contraction and the residue-field inclusion show that upper inertia restricts to
   lower inertia. Restriction respects identity and composition.
3. Given h in lower inertia, use
   `lem-weil-pbc-normal-subextension-automorphism-extends` to lift h to tau in Gal(M/K).
   By `lem-dl-a1-galois-over-intermediate`, M/L is Galois, without a finiteness assumption.
4. The primes tau(r) and r contract to the same prime of B. Part (1) of
   `lem-dl-a1-galois-prime-residue-lifting` over B supplies rho in Gal(M/L) with
   rho(tau(r)) = r. Then d = rho * tau stabilizes r and restricts to h.
5. The residue action of d fixes the lower residue field because h is in inertia.
   Part (2) of `lem-dl-a1-galois-prime-residue-lifting` supplies epsilon in Gal(M/L)
   stabilizing r and inducing the same upper residue action as d. No finiteness or
   residue separability is needed.
6. Then epsilon⁻¹ * d has trivial residue action, stabilizes r, and still restricts to h.
   This gives the reverse image inclusion and proves equality of the subgroup image. -/
theorem inertia_map_restrictNormalHom
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (r.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom L) =
      (r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom).inertia
        (L ≃ₐ[K] L) := by
  sorry

end Ideal
