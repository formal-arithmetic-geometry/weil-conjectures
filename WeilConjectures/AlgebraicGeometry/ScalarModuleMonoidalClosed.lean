/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions

/-! # The canonical closed structure for scalar module categories

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

/-- The existing closed structure on modules over a pulled-back scalar ring.
Source: `CategoryTheory.Mod.monoidalClosed` and `isCommMonObj_condensedRingObj`.
Use the braiding inherited from the symmetric sheaf structure, transfer the already-proved
commutativity of the pulled-back ring by definitional equality, and apply the existing module
closed-structure construction. The resulting data are precisely that construction, with no
new choice of an internal hom or an adjunction.
(blueprint: def-sbc-scalar-module-monoidal-closed)
-/
@[instance_reducible]
def scalarModuleMonoidalClosed (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    MonoidalClosed (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) := by
  letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  haveI : IsCommMonObj (condensedRingObj Λ.X X) := by
    with_unfolding_all
      exact isCommMonObj_condensedRingObj Λ.X X
  with_unfolding_all
    exact CategoryTheory.Mod.monoidalClosed

end AlgebraicGeometry.Scheme
