/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Vanishing of the cotangent complex of a localization

Source: Stacks Project, Cotangent Complex, Tag 08R2, case (3)
(blueprint: lem-trf-localization-cotangent-vanishing).

The cotangent complex is the standard polynomial-resolution construction of
`Algebra.CotangentResolution.cotangentComplex`. Both zero-object vanishing and
vanishing of every cohomology object are stated, for arbitrary multiplicative subsets.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

/-- The full cotangent complex of the canonical localization map is a zero object;
every integer-degree cohomology object vanishes. There is no finiteness assumption
on the multiplicative subset or on the localization map, and the subset may contain zero.
Source: Stacks Project, Cotangent Complex, Tag 08R2, case (3)
(blueprint: lem-trf-localization-cotangent-vanishing).

Proof:
1. Put B = S⁻¹R. Identify B ⊗[R] M with S⁻¹M by (r/s) ⊗ m ↦ rm/s,
   with inverse m/s ↦ (1/s) ⊗ m. The fraction equality of
   lem-weil-pbc-localization-module-exact proves well-definedness: a common
   denominator annihilating the difference becomes a unit. In particular S⁻¹B = B.
   These formulas also apply when zero belongs to S, so B is the zero ring.
2. Localize the standard polynomial resolution P of B over R, supplied by
   lem-trf-cotangent-resolution-coherence, to Q = P ⊗[R] B. Termwise this is
   B[E], since each polynomial has finitely many coefficients and hence a common
   denominator. Its augmentation is surjective, and exact module localization
   (lem-weil-pbc-localization-module-exact) preserves the augmented alternating
   complex's exactness. Thus Q is a polynomial resolution of B over B.
3. The universal derivation of def-weil-pbc-kahler-differentials identifies the
   differential complexes of P over R and Q over B. The forward map sends
   dp ⊗ c to d(p ⊗ 1) ⊗ c; the inverse sends d(p ⊗ b) ⊗ c to dp ⊗ bc.
   The latter comes from the balanced B-derivation p ⊗ b ↦ dp ⊗ b. Leibniz
   and the equality d(p ⊗ b) = b d(p ⊗ 1) show these maps are inverse.
   Both commute with every face and degeneracy, by their formulas on generators.
4. The constant augmented simplicial B-algebra B is a polynomial resolution
   on the empty variable set. Its alternating differential in positive simplicial
   degree is the identity in even degrees and zero in odd degrees, giving only
   H⁰ = B. Every B-derivation of B is zero, so its differential complex is
   termwise zero by def-weil-pbc-kahler-differentials. Resolution comparison
   (lem-trf-cotangent-resolution-coherence) therefore gives L[B/B] = 0.
5. Comparison for Q and the chain isomorphism in step 3 identify L[B/R] with
   L[B/B], hence with zero (Stacks Tags 08QZ and 08R0). By
   def-weil-abstract-derived-category its cohomology is kernel modulo image,
   so it vanishes in every integer degree. Conversely, an acyclic complex maps
   quasi-isomorphically to zero, hence is zero after localization. Thus the
   two asserted vanishing formulations are equivalent. -/
theorem localization_cotangent_vanishing
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : CommRingCat.{u}) (S : Submonoid R) :
    IsZero (cotangentComplex C
      (Arrow.mk (CommRingCat.ofHom (algebraMap R (Localization S))))) ∧
    ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (CommRingCat.of (Localization S))) i).obj
      (cotangentComplex C
        (Arrow.mk (CommRingCat.ofHom (algebraMap R (Localization S)))))) := by
  sorry

end Algebra.CotangentResolution
