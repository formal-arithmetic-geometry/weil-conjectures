/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Restricting module sheaves to a field preserves injectives

Source: Stacks Project, Cohomology, Tag 02N5; Modules, Tag 02N4;
Homology, Tag 015Z.
(blueprint: lem-sc-field-scalar-restriction-injectives).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Field restriction of module sheaves preserves injective objects.

Source: Stacks Project, Cohomology, Tag 02N5; Modules, Tag 02N4;
Homology, Tag 015Z.
(blueprint: lem-sc-field-scalar-restriction-injectives).

Proof: Write O for R and let k act through α on global sections and hence on every
open by restriction. The left adjoint to the displayed functor sends a sheaf V of
k-vector spaces to the sheafification of U ↦ O(U) ⊗[k] V(U). Its restriction maps
send a ⊗ v to a|W ⊗ v|W. The tensor universal property gives the adjunction on
presheaves, and the sheafification adjunction gives it on sheaves. At a point x,
this left adjoint has stalk O_x ⊗[k] V_x: tensor and stalks commute with the
filtered colimits of sections. Tensoring over a field is exact, so this left
adjoint preserves monomorphisms, as tested on stalks. Given a monomorphism of
k-sheaves and a map to the restricted injective module sheaf, transpose the map,
extend it across the resulting module-sheaf monomorphism by injectivity, and
transpose back. This proves injectivity of its restriction. The empty space and
zero ring sheaf cause no exception; there are no points to test in the former
case and all module sheaves are zero in the latter. No Ext assertion is used. -/
theorem fieldScalarRestriction_preservesInjectives
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    Functor.PreservesInjectiveObjects
      (forgetToSheafModuleCat.{u} R (op ⊤) isTerminalTop.op ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars α)) := by sorry

end SheafOfModules
