/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherent modules of finite type

Source: Stacks Project, Modules on Schemes, Tags 01B5 and 01BE
(blueprint: pqf-def-coherent).
-/

@[expose] public section
set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A sheaf of modules is quasi-coherent and of finite type.
Source: Stacks Project, Modules on Schemes, Tags 01B5 and 01BE
(blueprint: pqf-def-coherent). -/
def Scheme.Modules.IsQuasiCoherentFiniteType {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F

end AlgebraicGeometry
