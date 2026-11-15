/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherent, quasi-coherent and finite-type modules

The public coherence import exposes `RingedSpace.IsCoherent`, the finite-type
and finite-type-kernel condition of Tag 01BV. Mathlib supplies
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. The conjunction
`Scheme.Modules.IsQuasiCoherentFiniteType` does not replace the coherence predicate.

## References

* Stacks Project, Tags 01BV, 01B5, 01BE and 01IA
-/

@[expose] public section
set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A sheaf of modules is quasi-coherent and of finite type. -/
def Scheme.Modules.IsQuasiCoherentFiniteType {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F

end AlgebraicGeometry
