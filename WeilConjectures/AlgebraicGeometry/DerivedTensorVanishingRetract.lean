/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.CategoryTheory.Retract
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal

/-! # Derived tensor cohomology vanishing passes to retracts

## References

* Stacks Project, Tag 08CK
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Vanishing of one derived tensor cohomology group passes to a retract (Stacks, Tag 08CK). -/
theorem schemeDerivedTensorCohomologyVanishes_of_retract (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E K : schemeDerivedCategory X) (r : Retract E K)
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ)
    (hK : schemeDerivedTensorCohomologyVanishes X K G i) :
    schemeDerivedTensorCohomologyVanishes X E G i := by
  apply (tensor_vanishes_iff X E G i).2
  have hz := (tensor_vanishes_iff X K G i).1 hK
  let F := tensorRight ((DerivedCategory.singleFunctor _ 0).obj G) ⋙
    DerivedCategory.homologyFunctor _ i
  let s := r.map F
  apply (IsZero.iff_id_eq_zero _).2
  exact s.retract.symm.trans (by rw [hz.eq_of_src s.r 0, comp_zero])

end AlgebraicGeometry
