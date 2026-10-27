/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Sheaf.AlgebraicGeometry.ReducedNormalization
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.AlgebraicGeometry.Gluing

/-! # Lifting component-dominant maps through componentwise normalization

Source: Stacks Project, Morphisms, Tag 035Q, lemma-normalization-normal, part (4), and
Tag 0CDV, lemma-normalization-in-terms-of-components
(blueprint: lem-sfb-component-dominant-normalization-lift).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme

/-- A map from a scheme with integrally closed domain stalks which dominates a target
component on every source component factors uniquely through componentwise normalization.
The source may be empty and need not be quasi-compact or locally Noetherian.
Source: Stacks Project, Morphisms, Tag 035Q(4) and Tag 0CDV
(blueprint: lem-sfb-component-dominant-normalization-lift).

Proof:
1. The domain stalks make Y reduced. By
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme, g factors through X's
   reduction. Reduction preserves the underlying topology, the finite-component hypothesis,
   and component dominance. The reduced induced component schemes, hence their normalizations
   and the coproduct defining reducedNormalization, are unchanged. The reduction inclusion
   is a monomorphism by lem-pc-proper-monomorphism-closed, so factorizations over X and its
   reduction agree. We may therefore assume X reduced.
2. Choose arbitrary affine opens W = Spec B in Y and U = Spec A in X with g(W) contained
   in U. Such W cover Y. By lem-weil-pbc-spec-domain-stalks-function-field, every localization
   of B at a prime is an integrally closed domain. The target hypothesis and
   lem-sfb-normalization-affine-total-fractions identify the normalization over U with the
   spectrum of the integral closure A' of A in Q(A), with its canonical map to Spec A.
3. By lem-weil-pbc-spec-irreducible-components-minimal-primes, a minimal prime q of B gives
   a component of W. By lem-sc-irreducible-components-cover and
   lem-sc-components-open-injection this is the intersection with a component C of Y, and q
   is generic in C. Continuity and component dominance identify the closure of g(q) with
   a component D of X. Its intersection with U is a component of U; thus the contraction of
   q to A is a minimal prime of A.
4. By lem-weil-pbc-reduced-zerodivisors-union-minimal-primes, nonzerodivisors of A map to
   nonzerodivisors of B. The localization equivalence of def-weil-pbc-module-localization
   therefore defines Q(A) to Q(B), sending a/s to g*(a)/g*(s); the fraction formulas verify
   well-definedness and the ring operations, without assuming injectivity of g*.
5. The image of z in A' is integral over B. By
   lem-weil-pbc-normal-ring-integrally-closed-total it comes from B, uniquely since B to Q(B)
   is injective. This yields the ring map A' to B over A and hence the local lift on W.
6. For any other A-algebra map theta from A' to B, write z = a/s in Q(A). The identity
   sz = a holds already in A', so g*(s) theta(z) = g*(a). Since g*(s) is a nonzerodivisor,
   cancellation determines theta(z) uniquely. Thus the local lift is unique.
7. On overlaps refine both the source and target affine opens by affine neighbourhoods.
   The preceding uniqueness calculation holds for every such affine pair, so the local
   lifts agree. Apply lem-weil-pbc-scheme-morphism-gluing on arbitrary open covers to glue
   them and their factorization equations; uniqueness is local on the same cover. For the
   empty source use the empty cover. No finiteness assumption on Y or g enters. -/
theorem existsUnique_lift_reducedNormalization_of_component_dominant
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdominant : ∀ (C : Set Y), C ∈ irreducibleComponents Y →
      ∃ (D : Set X), D ∈ irreducibleComponents X ∧ closure (g '' C) = D) :
    ∃! h : Y ⟶ X.reducedNormalization, h ≫ X.fromReducedNormalization = g := by
  sorry

end AlgebraicGeometry.Scheme
