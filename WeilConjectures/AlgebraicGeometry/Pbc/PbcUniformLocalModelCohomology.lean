/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
/-! # Common cohomological bounds from integral local models

Source: uniform triangulation supplement, step 2. The lower bound is reused from the
levelwise truncation theorem, applied at the common upper bound.
(blueprint: lem-weil-pbc-uniform-local-model-cohomology). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

end AlgebraicGeometry.Scheme
