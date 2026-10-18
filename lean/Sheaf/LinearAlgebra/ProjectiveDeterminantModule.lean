/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# The determinant module as the exterior-algebra socle

Source: Stacks Project, More on Algebra, section Determinants, Remark
`remark-determinant-as-socle`, preceding Tag 0FJB.
(blueprint: def-trf-projective-determinant-module)

For finite projective modules the socle is the line obtained by gluing local top exterior
powers. This construction also makes sense without finiteness or projectivity; its line
properties are asserted only under those hypotheses.
-/

@[expose] public section

set_option autoImplicit false
universe u v w z

namespace Module

/-- The determinant of a finite projective module, realized as the annihilator of its
vectors inside its exterior algebra. There is no rank choice and no choice of free cover.
Source: Stacks Project, More on Algebra, `remark-determinant-as-socle` before Tag 0FJB.
(blueprint: def-trf-projective-determinant-module) -/
def determinantModule (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, LinearMap.ker (LinearMap.mulRight R (ExteriorAlgebra.ι R m))

end Module

namespace ExteriorAlgebra

/-- The exterior-algebra map induced by a coefficient extension and a compatible linear
map of modules. In particular this is the canonical map used on localization charts.
Source: Stacks Project, More on Algebra, determinant construction preceding Tag 0FJB;
Algebra, Tag 0C6F, exterior algebras and localization.
(blueprint: def-trf-projective-determinant-module) -/
def scalarExtensionMap {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] {M : Type w} {N : Type z} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A N :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι A).restrictScalars R).comp f,
      fun m ↦ ExteriorAlgebra.ι_sq_zero (R := A) (f m)⟩

end ExteriorAlgebra
