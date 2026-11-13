/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.FieldScalarExtensionAdjunction
import WeilConjectures.AlgebraicGeometry.FieldScalarExtensionMono

/-! # Restricting module sheaves to a field preserves injectives

## References

* Stacks Project, Tags 02N5, 02N4 and 015Z
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Field restriction of module sheaves preserves injective objects
(Stacks, Tags 02N5, 02N4, 015Z). -/
theorem fieldScalarRestriction_preservesInjectives
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    Functor.PreservesInjectiveObjects
      (forgetToSheafModuleCat.{u} R (op ⊤) isTerminalTop.op ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars α)) := by
  have := fieldScalarExtension_preservesMonomorphisms X R α
  obtain ⟨adj⟩ := nonempty_fieldScalarExtensionAdjunction X R α
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end SheafOfModules
