/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Site comparison for the clopen projection and compositors

Source: Stacks Project, Tags 09AF and 0F7B.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Functor

-- These mate-transport calculations are the ordinary-sheaf part of the proof in
-- WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence,
-- with no tensor or derived functors.

-- Restricting either canonical clopen projector gives the open-adjunction unit.
namespace EtaleProjection

open AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

end EtaleProjection

-- The adjunction detects maps into direct image, hence into clopen extension by zero.

-- Invert the existing coherence squares and retain the specified equality transports.

-- Paste the projection square and the two outgoing compositor squares.

attribute [local irreducible] upperStar Etale.upperStar comparisonUpperStar
  openImmersionLowerShriek Etale.openImmersionLowerShriek

end AlgebraicGeometry.ProEtale
