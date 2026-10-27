/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
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
import Mathlib.RingTheory.Spectrum.Prime.RingHom

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

namespace RingHom.Flat

/-- For a flat local map of Noetherian local rings with catenary equidimensional target,
all prime-extended quotients of the target are equidimensional, and the source is catenary
and equidimensional. Equidimensionality means equality of dimensions of all components.

Source: Stacks Project, More on Algebra, Tag 0AW4,
lemma-flat-under-catenary-equidimensional
(blueprint: lem-per-flat-equidimensional-catenary-descent).

Proof, following the eight steps of the node:
1. Write `a = dim A` and `d = dim B`, finite by
   `lem-weil-pbc-noetherian-local-finite-krull-dimension`. Components are zero loci of minimal
   primes by `lem-weil-pbc-spec-irreducible-components-minimal-primes`. The quotient
   homeomorphism `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` and
   `lem-weil-pbc-spec-topological-krull-dimension-ring` identify their dimensions with
   `dim (B/r)`. Every chain extends down to a minimal prime by
   `lem-weil-pbc-prime-contains-minimal-prime`, so the common component dimension is `d`.
2. Catenarity and equidimensionality of `B` imply `dim B_q = d - dim (B/q)`.
   Indeed, choose a minimal prime below `q`, refine chains to saturated ones using the finite
   bound `d`, and concatenate chains through `q`. Their lengths add; use
   `lem-weil-pbc-localization-dimension-chains-below-prime` for the height of `q`.
3. For a prime `p` of `A`, locality makes `pB` proper. If `q` is minimal over `pB`,
   `lem-sc-flat-going-down` and minimality give `q ∩ A = p`. The prime `q/pB` has height
   zero; `lem-weil-pbc-flat-height-formula` gives `dim B_q = dim A_p`. Hence every such
   `q` has `dim (B/q) = d - dim A_p`.
4. Apply the component/minimal-prime correspondence, quotient homeomorphism and
   spectrum dimension comparison from step 1 to `B/pB`. Its component dimensions are
   therefore all `d - dim A_p`, proving equidimensionality and the same total dimension.
5. The map `A/p → B/pB` is flat by `lem-weil-pbc-flat-module-quotient-flat`, local and
   Noetherian. Apply `lem-weil-pbc-flat-height-formula` at the maximal ideals to it and to
   `A → B`. Their closed fibre is `B/m_A B`, of finite dimension `f`. This gives
   `dim (B/pB) = dim (A/p) + f` and `d = a + f`. Substitution yields
   `dim A_p = a - dim (A/p)`.
6. At a minimal prime `p`, `dim A_p = 0` by
   `lem-weil-pbc-localization-dimension-chains-below-prime`. Thus `dim (A/p) = a`,
   and the component correspondence of step 1 proves equidimensionality of `Spec A`.
7. For adjacent primes `p < p'`, the quotient `B/pB` remains catenary because its prime
   intervals are the same intervals in `B`; it is equidimensional by step 4. Repeat steps
   1-5 for `A/p → B/pB` at `p'/p`. Its local dimension is one by
   `lem-weil-pbc-localization-dimension-chains-below-prime`, giving
   `dim (A/p) - dim (A/p') = 1`.
8. Prime-chain lengths in `A` are bounded by `a`; saturated refinements exist. Along any
   saturated chain, step 7 telescopes to its length being the difference of the endpoint
   quotient dimensions. This is exactly `IsCatenaryRing A` from `def-exc-excellent-ring`.
-/
theorem equidimensional_quotients_and_catenary_descent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Flat) (hcat : IsCatenaryRing B)
    (hequi : ∀ Z ∈ irreducibleComponents (Spec (CommRingCat.of B)),
      ∀ W ∈ irreducibleComponents (Spec (CommRingCat.of B)),
        topologicalKrullDim Z = topologicalKrullDim W) :
    (∀ (p : Ideal A) [p.IsPrime],
      ∀ Z ∈ irreducibleComponents (Spec (CommRingCat.of (B ⧸ p.map f))),
        ∀ W ∈ irreducibleComponents (Spec (CommRingCat.of (B ⧸ p.map f))),
          topologicalKrullDim Z = topologicalKrullDim W) ∧
    IsCatenaryRing A ∧
    (∀ Z ∈ irreducibleComponents (Spec (CommRingCat.of A)),
      ∀ W ∈ irreducibleComponents (Spec (CommRingCat.of A)),
        topologicalKrullDim Z = topologicalKrullDim W) := by
  sorry

end RingHom.Flat
