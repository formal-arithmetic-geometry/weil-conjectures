/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator

/-! # Perfect generation over an affine base

Source: literature/stacks-project/perfect.tex, Tags 06Z0 and 09IS
(blueprint: lem-pc-perfect-generation-affine-base).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If `X` is affine (`X ≅ Spec(A)`, `A = Γ(X, 𝒪_X)`), the structure sheaf is perfect
and generates the quasi-coherent derived category.
Source: Stacks Project, perfect.tex, Tags 06Z0 and 09IS
(blueprint: lem-pc-perfect-generation-affine-base).

Proof. Use the affine equivalence between the derived category of modules over `A`
and the quasi-coherent derived category of `X`; it sends `A[n]` to `𝒪_X[n]` and
preserves zero objects and Hom groups. The free rank-one module is strictly perfect,
and maps from its shifts detect all cohomology groups, hence detect zero objects.
Transport this criterion across the equivalence. -/
theorem perfectGeneration_affine_base (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    schemeDerivedQCohProperty X
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ∧
      Scheme.IsPerfect X
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ∧
      ∀ E : schemeDerivedQCohCategory X,
        IsZero E.obj ↔
          ∀ n : ℤ,
            Subsingleton
              (((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
                (SheafOfModules.unit (moduleRings X.toRingedSpace)))⟦n⟧ ⟶ E.obj) := by
  sorry

end AlgebraicGeometry
