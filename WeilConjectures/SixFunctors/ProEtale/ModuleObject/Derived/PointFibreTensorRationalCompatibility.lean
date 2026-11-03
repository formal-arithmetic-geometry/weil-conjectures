/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar

/-! # Rational point-fibre tensor and unit compatibility

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-prop-scalar-six/det-prop-scalar-six-tensor-hom.proof.md`, clause (1),
  specialized to the geometric point (blueprint: def-sf-point-fibre-tensor-rational-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A condensed scalar-six ring is rational when it is isomorphic to a finite
subextension coefficient ring or to the finite-subextension-valued algebraic closure ring.
Source: the rational coefficient alternatives in the scalar-six point setting
(blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def IsRationalCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Λ ≅ (Coefficient.rational E).bundled.{u} ell)) ∨
    Nonempty (Λ ≅ Coefficient.closure.bundled.{u} ell)

end AlgebraicGeometry.ProEtale.CondensedRing
