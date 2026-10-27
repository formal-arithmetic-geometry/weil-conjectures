/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Prime decomposition of effective Cartier divisors on locally factorial schemes

Source: Stacks Project, Divisors, Tags 0BCP (lemma-effective-Cartier-divisor-is-a-sum)
and 0BCN (lemma-effective-Cartier-codimension-1), part (2).
(blueprint: lem-sfb-factorial-cartier-prime-decomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- On a Noetherian scheme with factorial domain stalks, every effective Cartier divisor
is a finite product of positive powers of distinct integral effective Cartier ideals.
The ambient local ring at every generic point of each component has dimension one.
The family may be empty: its product is the unit ideal, defining the empty divisor.

Source: Stacks Project, Divisors, Tag 0BCP (lemma-effective-Cartier-divisor-is-a-sum),
including its UFD existence clause, and Tag 0BCN (lemma-effective-Cartier-codimension-1),
part (2). (blueprint: lem-sfb-factorial-cartier-prime-decomposition).

Proof (the accepted stage-1 split):
1. Give the support of E its reduced induced closed structure H using
   [lem-weil-pbc-reduced-induced-closed-subscheme]. By
   [lem-sfb-closed-component-stalk-calculus], H has finitely many distinct integral reduced
   components, covering its support, with the stated ideal-stalk/minimal-prime correspondence.
   Each has a unique generic point by [lem-sc-scheme-sober]. For empty support take no components.
2. At x write A = O_{W,x} and E's stalk ideal as (f), f a nonzerodivisor
   [def-pc-divisor-line-bundle]. The affine reduced-induced description and the component-stalk
   calculus identify H's stalk ideal with radical (f). Radical commutes with localization:
   if (a/s)^n belongs to the localized ideal, choose t outside the prime with t*a^n in the
   ideal; then (t*a)^n is in it, so a/s = (t*a)/(t*s) is in the localized radical.
   The converse follows by taking powers.
3. Factor f in the UFD A as a unit times a product of distinct nonassociated primes q_j
   to positive powers b_j. Its minimal primes are exactly (q_j): any prime over the product
   contains a factor, and distinct prime elements cannot divide one another. The component-stalk
   calculus matches these primes with the components through x, whose stalk ideals are (q_j).
   Components missing x have the unit stalk ideal. All these generators are nonzerodivisors.
4. Apply [lem-sfb-stalk-nonzerodivisor-cartier-spreading] to each integral reduced component.
   Local Noetherianity and step 3 show that its ideal is effective Cartier, including the unit
   generator off the component. Integrality and distinctness are from step 1.
5. At a component's generic point xi_i, no other component contains xi_i, and no proper
   generalization of xi_i lies in the support: irreducible closures and maximality of components,
   with uniqueness of generic points [lem-sc-scheme-sober], give both assertions.
   By [lem-weil-pbc-spec-local-ring-canonical-morphism], the only prime of A_i = O_{W,xi_i}
   containing f is its maximal ideal. Step 3 makes that maximal ideal (q) for a prime q.
   Any nonzero prime P contains a prime factor s of one of its nonzero elements; since s is
   in (q), primality and irreducibility make s associated to q. Thus P = (q), and the only
   primes are (0) and the nonzero maximal ideal, giving ringKrullDim A_i = 1
   [def-weil-pbc-krull-dimension-ring].
6. The local equation at xi_i is a unit times q to a unique positive exponent a_i.
   Two generators of a nonzero principal ideal in a domain differ by a unit: writing
   f = v*g and g = w*f and cancelling f gives v*w = 1. The same applies to prime generators
   of the maximal ideal. Unique factorization therefore makes a_i independent of all choices.
7. At x on component i, the corresponding prime (q_j) of A maps to xi_i, as seen on an
   affine chart and by sobriety. The canonical-morphism theorem identifies A_(q_j) with A_i.
   The two defining ideals localize to their stalks at xi_i by
   [lem-weil-pbc-spec-tilde-stalk-localization]. All other q_k become units there.
   The image of q_j is still prime and nonunit since the localized quotient is a localization
   of the domain A/(q_j), with denominators outside (q_j). Unique factorization and step 6
   give b_j = a_i, so the component multiplicities are constant along the component.
8. Steps 3 and 7 identify E's ideal stalk at every x with the product of the component
   stalk ideals to powers a_i, including the unit factors off the components. Products and
   powers [def-sbc-ideal-sheaf-powers] commute with stalks: represent the finitely many germs
   on a common neighbourhood [def-weil-pbc-module-stalk] and multiply their representatives.
   Equality of all stalk ideals implies equality of ideal sheaves: locally represent a section
   in the other ideal, shrink until its germ equality is section equality, and glue.
   This gives the required product equality; step 5 gives the dimension clause. If E is empty,
   the component-stalk calculus gives unit stalks everywhere, so E is the empty product.
-/
theorem exists_integral_prime_decomposition_of_factorial
    {W : Scheme.{u}} [IsLocallyNoetherian W] [CompactSpace W]
    (hfactorial : ∀ w : W,
      IsDomain (W.presheaf.stalk w) ∧ UniqueFactorizationMonoid (W.presheaf.stalk w))
    (E : W.IdealSheafData) (hE : E.IsInvertible) :
    ∃ (r : ℕ) (D : Fin r → W.IdealSheafData) (a : Fin r → ℕ),
      Function.Injective D ∧
      (∀ i : Fin r, IsIntegral (D i).subscheme ∧ (D i).IsInvertible ∧ 0 < a i) ∧
      E = ∏ i : Fin r, (D i) ^ (a i) ∧
      (∀ (i : Fin r) (ξ : (D i).subscheme), IsGenericPoint ξ Set.univ →
        ringKrullDim (W.presheaf.stalk ((D i).subschemeι ξ)) = 1) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
