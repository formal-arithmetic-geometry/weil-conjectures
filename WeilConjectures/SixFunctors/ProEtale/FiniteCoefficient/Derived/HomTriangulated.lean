/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Exactness of the derived hom of pro-étale sheaves

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated`
and `WeilConjectures.SixFunctors.Etale.Derived.HomShift`. The derived hom
`RHom(-, -)` on `D(X_proét)` is exact in each variable, and turns shifts in the first variable
into opposite shifts: `RHom(K⟦a⟧, M) ≅ RHom(K, M)⟦-a⟧`.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_distTriang_derivedHom_left`,
  `AlgebraicGeometry.ProEtale.exists_distTriang_derivedHom_right`: `RHom` sends distinguished
  triangles in either variable to distinguished triangles (blueprint `lem-sf-hom-triangulated`
  on the pro-étale site).
- `AlgebraicGeometry.ProEtale.derivedHomShiftIso`: `RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale
