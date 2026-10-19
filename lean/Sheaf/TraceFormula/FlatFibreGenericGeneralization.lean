/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.ValuationDomainFibreDimensions
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg

/-!
# Fibre-generic locus of a flat finitely presented morphism

Source: Temkin, Stable Modification, Lemma 3.5.3, printed pp. 20--21
(blueprint: lem-trf-flat-fibre-generic-generalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Over a valuation spectrum, the fibre-generic locus of a flat finitely presented
morphism is stable under generalization.

Source: Temkin, Stable Modification, Lemma 3.5.3, printed pp. 20--21, restricted to the
valuation base in the reviewed DAG node
(blueprint: lem-trf-flat-fibre-generic-generalization).

Proof plan (the eight steps of the node):
1. Choose an affine open `Spec B` containing `x`; it also contains `x'`. Finite
   presentation implies local finite type. By `lem-weil-pbc-lft-affine-pairs`, `B` is
   finite type over `V`. The affine-chart base-change isomorphism identifies its fibre
   at a prime `p` with `Spec (B ⊗[V] κ(p))`. Quotient and localization prime
   correspondences identify fibre primes with primes of `B` contracting to `p`.
2. Component-genericity is local on open neighbourhoods: a larger irreducible closed
   subset stays larger on an open meeting the smaller generic point, by density.
   Thus the prime `q` of `x` is minimal among primes over its contraction `p`.
   If `x'` is not fibre-generic, choose `r < q' ≤ q` contracting to `p'`.
3. Set `A = (V/p')_(p/p')`, with fraction field `κ(p')` and residue field `κ(p)`.
   Total divisibility passes to the prime quotient and to localization, so `A` is
   again a valuation domain, with no rank assumption.
4. For `a = r` and `a = q'`, localize `B/a` at `V` outside `p` to obtain a finite
   type domain `D_a` containing `A`. Its special fibre is the corresponding
   localization of `B/(a+pB)`. By the generic-fibre localization lemma, its generic
   fibre `E_a` is the nonzero domain obtained by localizing `B/a` outside `p'`.
5. The special fibres are closed subsets of the original fibre containing `x`.
   The closure `C` of `x` is a component of each: a larger irreducible subset would
   contradict its maximality as a component of the original fibre. Both are nonempty.
6. Apply `lem-trf-valuation-domain-fibre-dimensions` to `A ⊆ D_r` and `A ⊆ D_q'`.
   Their common special-fibre component `C` gives `dim E_r = dim C = dim E_q'`.
   The finite-type-domain dimension/trdeg theorem makes this a finite integer `d`.
7. The quotient `B/r → B/q'` gives `E_r → E_q'`, a surjection with nonzero prime
   kernel `I`. Nonzeroness follows because the distinct primes `0` and `q'/r` both
   avoid the denominators and remain distinct under the localization correspondence.
8. Lift a maximal-length prime chain of length `d` from `E_q'` through the quotient
   correspondence. Each prime contains `I ≠ 0`; prepend the zero prime of the domain
   `E_r`. This gives a chain of length `d+1`, contradicting `dim E_r = d`.
   Therefore `x'` is fibre-generic. Empty fibres supply no generic points.
-/
theorem stableUnderGeneralization_fibreGeneric
    {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of V))
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {x x' : X}
    (hx : ∃ (s : Spec (CommRingCat.of V)) (z : f.fiber s),
      z ∈ genericPoints (f.fiber s) ∧ f.fiberι s z = x)
    (hxx' : x ∈ closure ({x'} : Set X)) :
    ∃ (s : Spec (CommRingCat.of V)) (z : f.fiber s),
      z ∈ genericPoints (f.fiber s) ∧ f.fiberι s z = x' := by
  sorry

end AlgebraicGeometry
