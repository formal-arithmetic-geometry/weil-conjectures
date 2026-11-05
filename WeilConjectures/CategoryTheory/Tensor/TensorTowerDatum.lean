/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-! # Data and component equation for a tensor scalar tower -/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false

universe u v
namespace CategoryTheory

namespace TensorTowerDatum
variable {C D E : Type u}

/-- The actual component equality, with all its category data held in a single record.
Source: the tensor clause of scalarOperationsOrdinary_tower.
(blueprint: def-weil-tensor-tower-datum). -/
@[irreducible] def Coherent (d : TensorTowerDatum.{u, v} C D E) : Prop :=
  letI := d.catC
  letI := d.catD
  letI := d.catE
  ∀ X Y : C,
    d.G.map (d.p.hom.app (X, Y)) ≫ d.q.hom.app (d.F.obj X, d.F.obj Y) ≫
      d.B.map (Prod.mkHom (d.a.hom.app X) (d.a.hom.app Y)) =
    d.a.hom.app (d.U.obj (X, Y)) ≫ d.r.hom.app (X, Y)

end TensorTowerDatum
end CategoryTheory
