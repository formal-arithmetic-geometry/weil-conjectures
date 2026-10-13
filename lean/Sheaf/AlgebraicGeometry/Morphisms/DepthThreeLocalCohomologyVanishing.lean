/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.Algebra.Homology.LocalCohomology

/-! # DepthThreeLocalCohomologyVanishing

Source: Stacks Project, Tags 0AVY and 0BK0.
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Algebraic vanishing of second local cohomology under depth at least three.

Source: Stacks Project, Tag 0AVY, Lemma 47.11.1.
(blueprint: lem-sbc-depth-three-puncture-h-one-local-vanishing)

Proof: Write m for the maximal ideal. Since m is proper, mR is not R, and R
is a finite module over itself. The regular-sequence definition of m-depth
therefore agrees with the depth in Lemma 47.11.1. That lemma identifies depth
with the first degree of nonzero local cohomology. More explicitly, depth is
unchanged on replacing m by a positive power; the Ext groups from R/m^n to R
vanish below depth, and their filtered colimit is local cohomology. Mathlib's
localCohomology uses exactly this colimit of Ext modules. Since 2 < 3 and
3 is at most depth R, every module in the degree-two diagram is zero and
so is its colimit. Its underlying additive group is thus subsingleton. -/
theorem depth_three_local_cohomology_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R) :
    Subsingleton ((localCohomology (IsLocalRing.maximalIdeal R) 2).obj
      ((ModuleCat.of R R : ModuleCat.{u} R))).carrier := by sorry

end AlgebraicGeometry.Scheme
