/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Bounded.BoundedFinitePseudoCoherentModel
import WeilConjectures.AlgebraicGeometry.Relative.RelativeCompletedModuleRealizationExact
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerAlgebraicDerivedPresentation
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Reconstruction of a lisse normalized tower

Source: Stacks Tags 09BV, 09AV, and bounded finite truncations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
