/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Flat descent of catenarity and equidimensionality

Source: Stacks Project, More on Algebra, Tag 0AW4,
lemma-flat-under-catenary-equidimensional
(blueprint: lem-per-flat-equidimensional-catenary-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace RingHom

/-- A flat local map of Noetherian local rings with catenary, equidimensional target
has equidimensional prime-extended quotients of the target, and catenary,
equidimensional source. Equidimensionality is equality of the topological Krull
dimensions of all irreducible components, with their subspace topologies.

Source: Stacks Project, More on Algebra, Tag 0AW4,
lemma-flat-under-catenary-equidimensional
(blueprint: lem-per-flat-equidimensional-catenary-descent).

Proof plan, following the eight steps of the node:
1. Set a = dim A and d = dim B, finite by
   lem-weil-pbc-noetherian-local-finite-krull-dimension. By
   lem-weil-pbc-spec-irreducible-components-minimal-primes,
   lem-weil-pbc-spec-quotient-homeomorphism-zero-locus and
   lem-weil-pbc-spec-topological-krull-dimension-ring, equidimensionality says
   dim(B/r) = d for every minimal prime r. Every chain extends down to a minimal
   prime by lem-weil-pbc-prime-contains-minimal-prime.
2. Catenarity (def-exc-excellent-ring) permits concatenating saturated chains from
   a minimal prime r through q to the maximal ideal. Their lengths give
   dim B_q = d - dim(B/q), using
   lem-weil-pbc-localization-dimension-chains-below-prime. Finite dimension
   ensures finite saturated refinements exist.
3. For q minimal over pB, going down (lem-sc-flat-going-down) forces q to contract
   to p: a smaller prime contracting to p would still contain pB. The prime q/pB
   has height zero. Thus lem-weil-pbc-flat-height-formula gives dim B_q = dim A_p,
   and dim(B/q) = d - dim A_p, independently of q.
4. The component/quotient/dimension correspondences from step 1 now show that
   Spec(B/pB) is equidimensional of dimension d - dim A_p. Locality puts pB
   inside the maximal ideal, so this quotient is nonzero.
5. By lem-weil-pbc-flat-module-quotient-flat, A/p to B/pB is flat; it is local
   and Noetherian. Apply lem-weil-pbc-flat-height-formula at maximal ideals to
   this map and to A to B. Both closed fibres are B/m_A B. Subtract their finite
   dimension equalities to obtain dim A_p = a - dim(A/p).
6. At a minimal prime p, dim A_p = 0 by
   lem-weil-pbc-localization-dimension-chains-below-prime. Hence dim(A/p) = a,
   which proves equidimensionality of Spec A by the correspondences in step 1.
7. For adjacent primes p < p', the quotient B/pB is catenary because its prime
   intervals and saturated chains are prime intervals and saturated chains of B.
   It is equidimensional by step 4. Reapply steps 1--5 to A/p to B/pB at p'/p.
   This localization has dimension one, so dim(A/p) - dim(A/p') = 1.
8. Every saturated chain is finite, bounded by a. Telescoping step 7 along such
   a chain shows that its length depends only on its endpoints. This is exactly
   IsCatenaryRing A, as defined in def-exc-excellent-ring. -/
theorem Flat.equidimensional_quotients_and_catenary_descent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Flat) (hcat : IsCatenaryRing B)
    (heq : ∀ (Z W : Set (Spec (.of B))),
      Z ∈ irreducibleComponents (Spec (.of B)) →
      W ∈ irreducibleComponents (Spec (.of B)) →
      topologicalKrullDim Z = topologicalKrullDim W) :
    (∀ (p : Ideal A) [p.IsPrime],
      ∀ (Z W : Set (Spec (.of (B ⧸ p.map f)))),
        Z ∈ irreducibleComponents (Spec (.of (B ⧸ p.map f))) →
        W ∈ irreducibleComponents (Spec (.of (B ⧸ p.map f))) →
        topologicalKrullDim Z = topologicalKrullDim W) ∧
    IsCatenaryRing A ∧
    (∀ (Z W : Set (Spec (.of A))),
      Z ∈ irreducibleComponents (Spec (.of A)) →
      W ∈ irreducibleComponents (Spec (.of A)) →
      topologicalKrullDim Z = topologicalKrullDim W) := sorry

end RingHom
