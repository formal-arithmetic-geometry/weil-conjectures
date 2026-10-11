/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Flat integral finitely presented algebra over a Zariski pair

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-flat-integral-isomorphism)

## Main statements

The theorem below states that a flat, integral, finitely presented ring map which
induces an isomorphism modulo an ideal in the Jacobson radical is itself an
isomorphism.  Its proof follows the finite-module reduction, rank-one propagation,
and rank-one algebra-map criterion recorded in the blueprint node.
-/

@[expose] public section

universe u v

namespace RingHom

/--
A flat integral finitely presented algebra over a Zariski pair is an isomorphism
when its reduction modulo the ideal is an isomorphism.

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-flat-integral-isomorphism).
Proof:
1. Finite presentation implies finite type; integrality then makes `S` a finite
   `R`-module (lem-weil-pbc-integral-finite-presentation-finite).
2. Algebra finite presentation and module finiteness make `S` finitely presented
   as a module (lem-weil-pbc-finite-algebra-presentation-module-presentation).
   Flatness (def-weil-pbc-flat-ring-map) makes it finite locally free. The quotient
   isomorphism gives rank one on `V(I)`. The rank is locally constant, and every
   maximal ideal contains `I`, so the closed complement of the rank-one locus
   has no closed point and is empty
   (lem-weil-pbc-zariski-pair-rank-one-propagation).
3. A finite flat algebra of rank one at every prime has bijective structure map
   (lem-weil-pbc-finite-flat-rank-one-algebra-map-bijective).
-/
theorem zariskiPair_flat_integral_finitePresentation_isIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    (hflat : f.Flat)
    (hintegral : f.IsIntegral)
    (hfinitePresentation : f.FinitePresentation)
    (hquotient : Function.Bijective
      (Ideal.quotientMap (Ideal.map f I) f (Ideal.le_comap_map))) :
    Function.Bijective f := by
  sorry

end RingHom
