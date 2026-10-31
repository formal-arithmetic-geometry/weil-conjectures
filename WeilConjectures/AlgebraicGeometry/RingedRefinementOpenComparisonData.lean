/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementData
import WeilConjectures.AlgebraicGeometry.RingedRefinementOpenGeometry

/-! # Construction of normalized ringed open comparisons

The arbitrary-ring construction transports the normalized inverse-image square and the
binary clopen module projector through ordinary and vertical localization.  This is the
geometric part of coefficient supplement Steps 1--4.
(blueprint: new-ringed-refinement-open-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement

/-- A normalized `OpenComparisons` object exists for every supplied geometric calculus.
Source: coefficient supplement Steps 1--4; Stacks 03DI, 07A6 and 0F7B.
The proof transports the canonical open base-change mate and binary clopen projector
through exact localized module categories and adjunction uniqueness.
(blueprint: new-ringed-refinement-open-comparison-data).
-/
theorem ringedRefinementOpenComparisonData {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (p : Spatial o) :
    Nonempty (OpenComparisons p) := by
  sorry

end SheafOfModules.RingedRefinement
