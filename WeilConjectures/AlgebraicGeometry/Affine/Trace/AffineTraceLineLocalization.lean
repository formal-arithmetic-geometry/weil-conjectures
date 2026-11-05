/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Tensor.TensorProjectionAdjunct
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The affine-line localization triangle in normalized projective coordinates
Source: blueprint sk-prop-an, Step 5(b), detailed affine-space trace steps 2, 3 and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Restricting an inverse-image unit along a section is invertible.

-- Change only the first coordinate, keeping the normalized trace unchanged.

end AlgebraicGeometry.Etale
