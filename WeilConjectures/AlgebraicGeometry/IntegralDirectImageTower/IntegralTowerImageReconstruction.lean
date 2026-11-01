/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionComparison
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The zero module has the zero finite scalar presentation on the identity cover.
/-- Normalized compact-support towers, their Tor bounds, and canonical integral reconstruction.
Source: blueprint latest direct-image.proof.md paragraphs (1) and (2).
Proof: reduce M using the normalized reduction theorem. Tower shriek levels and the uniform
bound theorem give finite constructibility and widen each Tor interval by 2d. Each transition
is the finite coefficient direct-image comparison composed with direct image of the input
transition, hence invertible. Complete compactification/limit realization commutes the two
separately derived factors with the scalar-restricted strict inverse limit: the proper factor
is a right adjoint and quasi-compact open extension is exact and preserves products. The
input is complete by the integral-model criterion. Tower reconstruction gives integral
constructibility of the limit. The normalized equivalence identifies its reduction with
the original normalized strict tower. The actual ordinary and derived adjunction
normalizations identify this isomorphism with the constructed proper/open mate, rather than
only its evaluations. Its inverse limit after the completion unit is reconstruction, hence
invertible. Transport constructibility across that isomorphism. The empty-source image and
the zero input are zero, so the assertions hold also in these cases for ordered Tor intervals.
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
-- The ordered-interval hypothesis is essential: the private counterexample above
-- disproves the former clause without a ≤ b, already on the constructible zero input.
end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
