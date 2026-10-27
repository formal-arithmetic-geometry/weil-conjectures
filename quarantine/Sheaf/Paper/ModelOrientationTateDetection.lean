/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.DegreeZeroDerivedMapGluing

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Shifted finite Tate powers are rank-one degree-zero objects after shift removal,
and their automorphisms are detected on any Zariski cover.
Source: model descent Step 8; Stacks 06XS, 03EM, 04TQ
(blueprint: lem-pur-model-orientation-tate-detection).

Proof: the structure morphism to k makes the coefficient prime invertible on X.
The finite Tate line is locally free of rank one. Tensor its local basis r
times (use the coefficient unit for r=0). Tensor with each such line is exact, so
ordinary tensor powers compute derived tensor powers. The even shifts add to 2r;
removing that shift leaves the corresponding locally free sheaf in degree zero.
For an arbitrary Zariski covering, exact restriction preserves this concentration.
Apply degreeZeroDerivedMapGluing with this sheaf as both endpoints: the restriction
map on endomorphisms is injective. The inverse shifts identify endomorphisms before
and after shift removal, compatibly with restriction. Apply Iso.ext to obtain
injectivity for automorphisms. Degree-zero gluing includes the empty cover, so
no nonemptiness hypothesis is needed. -/
theorem model_orientation_tate_detection (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (r : ℕ) :
    ModelOrientationDetection.{u, w} P X r := by sorry

end WeilConjectures.PurityFiniteSetting
