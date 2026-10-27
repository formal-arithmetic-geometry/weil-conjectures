/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.AlgebraicGeometry.Limits

/-!
# The inertia component of a transitive product

Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale`, final paragraph
(blueprint: lem-dl-a1-transitive-product-inertia-component).

A complete orthogonal family presents the product without choosing names for its factors.
The corner of the inertia-fixed ring at the first idempotent is precisely the fixed ring
of the first factor: both consist of inertia-fixed elements supported on that idempotent.
The complementary corner includes the zero ring when the product has one factor.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace RingTheory

/-- The inertia group is the prime and factor stabilizer. Projection identifies the full
fixed ring with the first inertia-fixed corner, with inverse given by the sum over factor
representatives, independent of those representatives. The inertia-fixed ring splits into
its first and complementary corners; the first spectrum is a clopen neighbourhood of the
contracted prime and maps isomorphically to the spectrum of the full fixed ring.

Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale`, final paragraph
(blueprint: lem-dl-a1-transitive-product-inertia-component).

Proof plan:
1. Apply `lem-dl-a1-finite-invariant-prime-orbits-residues` to the primes over `p`.
A prime in factor `j` omits `e j` and contains every other orthogonal idempotent.
Thus transitivity on primes implies transitivity on factors. Uniqueness of the prime
in each factor gives equality of the prime and idempotent stabilizers.
2. A prime-stabilizing automorphism acts on fractions of the quotient and fixes the base
residue field. Pure inseparability forces it to be the identity: in positive characteristic
raise the difference to a suitable characteristic power; in characteristic zero the
extension is trivial. Hence the prime stabilizer equals inertia. Representatives carrying
the first idempotent to `e j` form exactly one left inertia coset, with representative 1
at `j₀`.
3. For a fixed element supported on the first idempotent, sum its translates by those
representatives. Changing a representative by an inertia element changes no summand.
Left multiplication permutes the cosets, so the sum is fully invariant. Its first
projection is the original element, by orthogonality.
4. Projection is a unital ring map, with that sum as inverse: for a fully invariant
`b`, the sum is `(∑ j, e j) * b = b`. Give the first corner its canonical base-algebra
structure through this projection; the resulting equivalence is a base-algebra equivalence.
5. Projection to the two corners sends `s` to `(e₁*s, (1-e₁)*s)`; its inverse adds the
two components. Orthogonality and the sum-to-one identity prove these are inverse ring maps.
6. Apply `lem-weil-pbc-finite-affine-coproduct-spectrum` and
`lem-weil-pbc-scheme-coproduct-family` to this two-factor decomposition. The first
spectrum is open and closed, with image `D(e₁)`, which contains the contracted prime
since `e₁` is not in it. The composite structural morphism is the spectrum of the
projection equivalence; functoriality of `def-weil-affine-spectrum` makes it an isomorphism. -/
theorem transitive_product_inertia_component
    (G : Type u) [Group G] [Finite G]
    (S : Type v) [CommRing S] [MulSemiringAction G S]
    (J : Type w) [Fintype J] (j₀ : J) (e : J → S)
    (he : CompleteOrthogonalIdempotents e)
    (hperm : ∀ (g : G) (j : J), ∃ k : J, g • e j = e k)
    (p : PrimeSpectrum (FixedPoints.subring S G)) (Q : J → PrimeSpectrum S)
    (hQ : ∀ j : J,
      p.asIdeal = (Q j).asIdeal.comap (FixedPoints.subring S G).subtype)
    (hfactor : ∀ j : J, e j ∉ (Q j).asIdeal)
    (hunique : ∀ (j : J) (q : PrimeSpectrum S),
      q.asIdeal.comap (FixedPoints.subring S G).subtype = p.asIdeal →
      e j ∉ q.asIdeal → q = Q j)
    (hpure : ∀ j : J,
      (Ideal.ResidueField.map p.asIdeal (Q j).asIdeal
        (FixedPoints.subring S G).subtype (hQ j)).IsPurelyInseparable) :
    (∀ j k : J, ∃ g : G, g • e j = e k) ∧
    (Q j₀).asIdeal.inertia G = MulAction.stabilizer G (Q j₀).asIdeal ∧
    (Q j₀).asIdeal.inertia G = MulAction.stabilizer G (e j₀) ∧
    ∃ (eI : FixedPoints.subring S ((Q j₀).asIdeal.inertia G))
      (heI : IsIdempotentElem eI),
      (eI : S) = e j₀ ∧
      ∃ (aC : Algebra (FixedPoints.subring S G) heI.Corner)
        (P : @AlgEquiv (FixedPoints.subring S G) (FixedPoints.subring S G)
          heI.Corner _ _ _ _ aC)
        (D : FixedPoints.subring S ((Q j₀).asIdeal.inertia G) ≃+*
          heI.Corner × heI.one_sub.Corner)
        (bI : FixedPoints.subring S G →+*
          FixedPoints.subring S ((Q j₀).asIdeal.inertia G)),
        (∀ b : FixedPoints.subring S G, ((P b).val : S) = e j₀ * (b : S)) ∧
        (∀ r : J → G, r j₀ = 1 → (∀ j : J, r j • e j₀ = e j) →
          ∀ a : heI.Corner, (P.symm a : S) = ∑ j : J, r j • (a.val : S)) ∧
        (∀ r r' : J → G,
          r j₀ = 1 → (∀ j : J, r j • e j₀ = e j) →
          r' j₀ = 1 → (∀ j : J, r' j • e j₀ = e j) →
          ∀ a : heI.Corner,
            (∑ j : J, r j • (a.val : S)) = ∑ j : J, r' j • (a.val : S)) ∧
        (∀ s : FixedPoints.subring S ((Q j₀).asIdeal.inertia G),
          (((D s).1).val : S) = e j₀ * (s : S) ∧
          (((D s).2).val : S) = (1 - e j₀) * (s : S)) ∧
        (∀ b : FixedPoints.subring S G, (bI b : S) = (b : S)) ∧
        IsOpenImmersion (Spec.map (CommRingCat.ofHom
          ((RingHom.fst heI.Corner heI.one_sub.Corner).comp D.toRingHom))) ∧
        IsClosed (Set.range (Spec.map (CommRingCat.ofHom
          ((RingHom.fst heI.Corner heI.one_sub.Corner).comp D.toRingHom)))) ∧
        PrimeSpectrum.comap
          (FixedPoints.subring S ((Q j₀).asIdeal.inertia G)).subtype (Q j₀) ∈
          Set.range (Spec.map (CommRingCat.ofHom
            ((RingHom.fst heI.Corner heI.one_sub.Corner).comp D.toRingHom))) ∧
        Spec.map (CommRingCat.ofHom
            ((RingHom.fst heI.Corner heI.one_sub.Corner).comp D.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom bI) = Spec.map (CommRingCat.ofHom P.toRingHom) ∧
        IsIso (Spec.map (CommRingCat.ofHom P.toRingHom)) := by
  sorry

end RingTheory
