/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions

/-! # The canonical braiding for scalar module categories

The sheaf braiding and the braiding inherited from the symmetric structure are
canonically definitionally equal. This wrapper supplies their identification explicitly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

/-- The existing braiding on modules over a pulled-back scalar ring.
Source: `CategoryTheory.Mod.braidedCategory` and `isCommMonObj_condensedRingObj`.
Use the braiding inherited from the symmetric sheaf structure, identify the existing
commutativity proof by definitional equality, and apply the existing relative tensor braiding.
The returned data are that braiding, with no new choice of tensor product or comparison.
(blueprint: def-sbc-scalar-module-braiding)
-/
@[instance_reducible]
def scalarModuleBraidedCategory (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    BraidedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) := by
  letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  haveI : IsCommMonObj (condensedRingObj Λ.X X) := by
    with_unfolding_all
      exact isCommMonObj_condensedRingObj Λ.X X
  with_unfolding_all
    exact CategoryTheory.Mod.braidedCategory

end AlgebraicGeometry.Scheme
