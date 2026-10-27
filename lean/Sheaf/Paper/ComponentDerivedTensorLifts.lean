/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.ComponentDerivedSquareData
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Tensor descent for an ordinary component square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- Exact component inverse images have normalized derived tensors, and their specified
square respects them. Source: HRS Section 3, construction (4.1); Stacks 07A4 and 0FPI
(blueprint: lem-zl-component-derived-tensor-lifts).

Proof: every edge is an actual geometric inverse image with coefficient transport
along an isomorphism. Such module inverse images preserve colimits and flat objects:
their right adjoints are restriction with the transported module action, and the
projection formula identifies tensoring by a pulled-back flat object with the exact
source tensor. Apply termwise pullback to flat-term K-flat representatives. Preservation
of coproducts identifies the total tensor of their images with the image of their
total tensor. Exactness preserves quasi-isomorphisms, giving the canonical invertible
derived tensor and coefficient-unit comparisons.

Descend the pentagon, unit and symmetry equations from those of the ordinary pullback;
the comparison with localization is monoidal by construction. Exact-functor
localization is triangulated. For the square, its ordinary comparison is the mate of
the restriction comparison, hence monoidal for the adjunction-normalized tensor maps.
Its coefficient equation gives the module-unit compatibility. Apply these equations
termwise and descend them along localization. With the canonical composition maps
inserted, the resulting two equations are precisely `Square.monoidal` for `Square.theta`.
The localization equation uniquely fixes each derived tensor structure, so the edge
structures may be chosen simultaneously and the argument applies to the supplied
ordinary system. No boundedness, discreteness or henselian hypothesis is used. -/
theorem component_derived_tensor_lifts
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinarySystem Λ) :
    Nonempty (TensorSystem Λ s) := by sorry

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
