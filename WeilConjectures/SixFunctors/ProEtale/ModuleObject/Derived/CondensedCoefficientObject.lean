/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

/-! # The constant condensed coefficient object

Source: latest blueprint, constant coefficient convention
(blueprint: def-weil-constant-coefficient-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The regular module over Lambda_X, placed in degree zero and localized.
Source: constant coefficient convention (blueprint: def-weil-constant-coefficient-objects). -/
def constantCoefficientObject
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X))

end AlgebraicGeometry.ProEtale.CondensedRing
