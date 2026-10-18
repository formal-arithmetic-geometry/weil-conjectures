/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Scalar extension on finite-dimensional coefficient complexes

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: def-weil-finite-dimensional-complex-scalar-extension).

## Main definitions

* `fieldDerivedScalarExtension`: exact termwise scalar extension descended to D(K).
* `pointFdScalarExtension`: its restriction to bounded finite-dimensional cohomology.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L : Type u} [Field K] [Field L]

/-- The existing scalar-extension adjunction gives additivity.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension). -/
noncomputable instance fieldExtendScalarsAdditive (f : K →+* L) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

/-- A vector space is free and hence flat, so scalar extension preserves finite limits.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension). -/
noncomputable instance fieldExtendScalarsLimits (f : K →+* L) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (letI := f.toAlgebra; inferInstanceAs (Module.Flat K L))

/-- Scalar extension preserves colimits by its existing adjunction.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension). -/
noncomputable instance fieldExtendScalarsColimits (f : K →+* L) :
    PreservesColimits (ModuleCat.extendScalars.{u, u, u} f) :=
  (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits

/-- Termwise scalar extension descended through localization at quasi-isomorphisms.
Its comparison on complexes is `Functor.mapDerivedCategoryFactors` and its shift and
triangulated structures are the existing exact-functor structures.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension). -/
noncomputable abbrev fieldDerivedScalarExtension (f : K →+* L) :
    DerivedCategory (ModuleCat.{u} K) ⥤ DerivedCategory (ModuleCat.{u} L) :=
  (ModuleCat.extendScalars f).mapDerivedCategory

/-- Restriction is possible because exact scalar extension commutes with cohomology.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension).
Proof: compute on a representing complex. Flatness preserves its kernels and images,
so its cohomology is the scalar extension of the original cohomology. Tensoring a
finite-dimensional space preserves finite dimensionality, and tensoring zero gives zero;
the same finite support works. -/
theorem fieldDerivedScalarExtension_preserves (f : K →+* L)
    (C : DerivedCategory (ModuleCat.{u} K)) (hC : pointFiniteDimensional K C) :
    pointFiniteDimensional L ((fieldDerivedScalarExtension f).obj C) := by
  sorry

/-- The transition functor on the specified full subcategories, with actual derived
scalar extension as its underlying functor.
Source: blueprint order 1509 (blueprint: def-weil-finite-dimensional-complex-scalar-extension). -/
noncomputable def pointFdScalarExtension (f : K →+* L) :
    (pointFiniteDimensional K).FullSubcategory ⥤ (pointFiniteDimensional L).FullSubcategory :=
  (pointFiniteDimensional L).lift
    ((pointFiniteDimensional K).ι ⋙ fieldDerivedScalarExtension f)
    (fun C ↦ fieldDerivedScalarExtension_preserves f C.obj C.property)

end DerivedCategory
