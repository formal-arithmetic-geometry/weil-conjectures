module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Generic points and stalks in a reduced affine injective factorization

Source: Stacks Project, Varieties, Tag 09NI, `lemma-points-in-affine`, middle paragraph
(blueprint: lem-trf-reduced-affine-injective-factor-stalk-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- For an injective map of reduced rings, a factorization that is injective on component
generic points induces a bijection on the affine generic points. If the composite of the
two canonical stalk maps is an isomorphism at a point, both factors are isomorphisms.

Source: Stacks Project, Varieties, Tag 09NI, `lemma-points-in-affine`, middle paragraph
(blueprint: lem-trf-reduced-affine-injective-factor-stalk-comparison).

Proof plan, following the eight steps of the node:

1. Identify component generic points of spectra with minimal primes using
   lem-weil-pbc-spec-irreducible-components-minimal-primes. Specialization means inclusion
   of prime ideals. Comparable component generic points of a scheme agree, by maximality
   of components and lem-weil-pbc-scheme-sober. Morphisms preserve specialization.
2. Given a minimal prime Q of B, use lem-weil-pbc-injective-minimal-prime-lift to find a
   prime P of R contracting to Q. A minimal prime inside P exists by
   lem-weil-pbc-prime-contains-minimal-prime and also contracts to Q, by minimality of Q.
3. For a generic point eta of T, choose a minimal prime Q below its image in Y, and lift
   Q to a generic point eta0 of T as in step 2. The images of eta0 and eta in X are
   comparable component generic points, hence equal. Injectivity of the composite on
   generic points gives eta0 = eta. Thus h maps generic points to generic points, is
   surjective by step 2, and is injective because its composite with g is. Lifting generic
   points along h also proves that g maps them injectively into the generic points of X.
4. At t, identify the affine stalks with R_p and B_q, where q is the contraction of p,
   using lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-spec-map-stalk-localization. The map beta induced by h sends b/d to
   u(b)/u(d). Write alpha for the map induced by g. The given isomorphism is beta alpha,
   by lem-weil-pbc-scheme-stalk-map-composition, rather than an unrelated ring isomorphism.
5. The canonical morphisms from the spectra of the local rings have images exactly the
   generalizations of t and x, by lem-weil-pbc-spec-local-ring-canonical-morphism. The
   diagram with f and Spec(beta alpha) commutes: check the closed-point image and its
   normalized stalk map by lem-weil-pbc-morphism-from-spec-local-ring, composition of
   stalk maps, and the Spec-map stalk formula. Since beta alpha is an isomorphism, every
   generalization of x therefore lifts to a generalization of the prescribed t.
6. Given a minimal prime Q of B below q, lift it to eta in T as in step 2. Its image theta
   in X generalizes x. Step 5 lifts theta to z generalizing t. Choose a component generic
   point eta' generalizing z. Its image and theta are comparable component generic points,
   hence equal. Injectivity on generic points gives eta' = eta. Thus the minimal-prime
   lift of Q lies below p, not just somewhere in Spec R.
7. If beta(b/d) = 0, choose s outside p with s u(b) = 0. Every minimal prime Q below q
   lifts by step 6 to a minimal prime P_Q below p. Since s is outside P_Q, primality gives
   b in Q. Every prime of B_q contracts to a prime below q containing such a Q, so b/d
   lies in every prime of B_q. By lem-weil-pbc-zero-locus-eq-iff-radical-eq it is nilpotent;
   lem-weil-pbc-localization-preserves-reduced gives b/d = 0. Apply this to differences
   to obtain injectivity of beta.
8. Surjectivity of beta alpha gives surjectivity of beta, so beta is an isomorphism.
   Injectivity of beta alpha gives injectivity of alpha. For a in B_q, lift beta(a) along
   beta alpha and use injectivity of beta to obtain a preimage of a under alpha. Thus
   alpha is also an isomorphism. If Spec R is empty, R is the zero ring, and injectivity
   forces B to be the zero ring too: the generic bijection is empty and there is no t.
   The finite-generic-point hypothesis is retained as in the node, although the argument
   using injective minimal-prime lifting does not need it. -/
theorem reducedAffineInjectiveFactor_stalkComparison
    (R B : Type u) [CommRing R] [CommRing B] [_root_.IsReduced R] [_root_.IsReduced B]
    (φ : B →+* R) (hφ : Function.Injective φ)
    (X : Scheme.{u}) (g : Spec (CommRingCat.of B) ⟶ X)
    (hfinite : (genericPoints (Spec (CommRingCat.of R))).Finite)
    (hgeneric : Set.MapsTo (Spec.map (CommRingCat.ofHom φ) ≫ g)
      (genericPoints (Spec (CommRingCat.of R))) (genericPoints X))
    (hinjective : Set.InjOn (Spec.map (CommRingCat.ofHom φ) ≫ g)
      (genericPoints (Spec (CommRingCat.of R)))) :
    Set.BijOn (Spec.map (CommRingCat.ofHom φ))
      (genericPoints (Spec (CommRingCat.of R))) (genericPoints (Spec (CommRingCat.of B))) ∧
    Set.MapsTo g (genericPoints (Spec (CommRingCat.of B))) (genericPoints X) ∧
    Set.InjOn g (genericPoints (Spec (CommRingCat.of B))) ∧
    ∀ t : Spec (CommRingCat.of R),
      IsIso (g.stalkMap ((Spec.map (CommRingCat.ofHom φ)) t) ≫
        (Spec.map (CommRingCat.ofHom φ)).stalkMap t) →
      Function.Injective ((Spec.map (CommRingCat.ofHom φ)).stalkMap t).hom ∧
      IsIso (g.stalkMap ((Spec.map (CommRingCat.ofHom φ)) t)) ∧
      IsIso ((Spec.map (CommRingCat.ofHom φ)).stalkMap t) := by
  sorry

end AlgebraicGeometry
