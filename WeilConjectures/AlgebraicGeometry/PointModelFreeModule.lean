/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData

/-! # Typed constructions for discrete point models

These are the existing constructions, with their module categories recorded in the type.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- The actual finite free point module, with its point-module category fixed. -/
def pointModelFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (n : ℕ) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ := Mod.finiteFree Λ n

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
