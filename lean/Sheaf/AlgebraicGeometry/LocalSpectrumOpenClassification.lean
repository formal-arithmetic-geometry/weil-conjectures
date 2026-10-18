/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.AlgebraicGeometry.Limits

/-!
# Opens of a one-dimensional Noetherian local spectrum

Source: Stacks Project, Varieties, Tag 09N8, proof of `lemma-affine`;
Algebra, Tag 00FR; Schemes, Tag 02O0
(blueprint: lem-a1-local-spectrum-open-classification).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An open of the spectrum of a Noetherian local ring of dimension at most one is
the whole spectrum when it contains the closed point; otherwise its space is finite
and discrete and its induced open subscheme is affine.

Source: Stacks Project, Varieties, Tag 09N8, proof of `lemma-affine`
(blueprint: lem-a1-local-spectrum-open-classification).

Proof:
1. Every prime lies in the maximal ideal. If the closed point belongs to W, a basic
   open D(f) around it contained in W has f outside the maximal ideal. Thus f is a
   unit, D(f) is the whole spectrum, and W is the whole spectrum.
2. Assume the closed point is absent. Every prime in W is minimal: a strictly smaller
   prime would give a chain of length two ending at the maximal ideal, contradicting
   `def-weil-pbc-krull-dimension-ring`. The only primes above such a prime are itself
   and the maximal ideal. In dimension zero there are no primes in W.
3. By `lem-weil-pbc-noetherian-finitely-many-minimal-primes` (Stacks Tag 00FR), there
   are finitely many minimal primes, so W is finite.
4. The closure V(p) of each point of W intersects W in that point alone. Singletons
   are therefore closed in W. Their complements are finite unions of closed
   singletons, so singletons are also open and every subset of W is open.
5. Apply `lem-weil-pbc-finite-discrete-scheme-affine` (Stacks Tag 02O0) to the induced
   open subscheme. This includes the empty open subscheme.
-/
theorem localSpectrum_open_classification (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hdim : ringKrullDim A ≤ 1) (W : (Spec (.of A)).Opens) :
    (IsLocalRing.closedPoint A ∈ W → W = ⊤) ∧
      (IsLocalRing.closedPoint A ∉ W →
        Finite W ∧ DiscreteTopology W ∧ IsAffine W.toScheme) := by
  sorry

end AlgebraicGeometry
