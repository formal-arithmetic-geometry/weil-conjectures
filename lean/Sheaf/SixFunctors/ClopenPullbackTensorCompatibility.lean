/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData

/-! # Cartesian tensor square for normalized open base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

/-- Tensor compatibility of the Cartesian pullback compositor.
Source: Stacks 07A4 and 0D6D.
(blueprint: lem-sf-clopen-pullback-tensor-compatibility).

Proof: on flat-term K-flat representatives use theta_model and the representative
equations of all four tensor comparisons. After cancelling their representative
isomorphisms, both sides are totalizations of the same ordinary tensor square.
That square follows on pure tensors from the ordinary adjunction-mate
normalization of theta and the pure-unit formulas. Sheafification and balancing
extend the calculation to module sheaf maps. No interchange of the two degrees
occurs, so the signed differentials agree. Two-variable resolving descent extends
the equation to arbitrary unbounded derived objects. -/
theorem pullback_tensor_compatibility {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (_a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (X Y : Der d.R) :
    o.gUPull.derived.map (o.tensorComparison.comparison.inv.app (X, Y)) ≫
        o.theta.inv.app (o.tensorX.functor.obj (X, Y)) ≫
        o.opens.jStar'.map (v.tensorP.comparison.hom.app (X, Y)) =
      v.tensorQ.comparison.hom.app (o.opens.jStar.obj X, o.opens.jStar.obj Y) ≫
        o.tensorU'.functor.map
          (Prod.mkHom (o.theta.inv.app X) (o.theta.inv.app Y)) ≫
        v.tensorB.tensorComparison.comparison.inv.app
          (o.gPull.derived.obj X, o.gPull.derived.obj Y) := by
  sorry

end SheafOfModules.ClopenComparisonTensorSquare
