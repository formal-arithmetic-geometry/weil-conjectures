/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData

/-! # Scalar cup on resolution classes

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar Ext cup is represented by the paired cycle of a module resolution.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV, resolution cup comparison.
(blueprint: new-sc-scalar-cup-resolution-class-compatibility).

Proof: Choose injective comparisons for the three acyclic resolutions and use the
cocycle formula defining `moduleExtEquiv`. Evaluation at the unit identifies the
scalar Ext representatives with the section cycles. Exact restriction of scalars
carries the signed Yoneda tensor construction to the sectionwise tensor pairing;
the coefficient map sends pure tensors to `D.pair`. The Leibniz equation gives the
paired target cycle, and the comparison maps identify its class with the target
`D.class`. Naturality and homotopy independence remove the chosen comparisons.
The argument includes degree zero, zero coefficients, and empty schemes.
-/
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      D.target.class (p + q) c := by
  sorry

end AlgebraicGeometry.Scheme.Modules
