/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.SixFunctors.Etale.Derived.ClopenTransfer
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Open counit compatibility for the standard affine-line exchange
Source: blueprint sk-prop-an, Step 5(b), detailed trace proof step 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
