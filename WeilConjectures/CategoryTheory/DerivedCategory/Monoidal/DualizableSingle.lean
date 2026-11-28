/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Dualizable objects placed in degree zero are dualizable in `D(A)`

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions. A dualizable object `X` of `A`, placed in degree `0`, is dualizable in the derived
category `D(A)`: the complex `X[0]` is a bounded complex of dualizable objects.

## Main results

- `DerivedCategory.isDualizable_singleFunctor_obj`: `X[0]` is dualizable in `D(A)` for every
  dualizable `X`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- A dualizable object `X` of `A`, placed in degree `0`, is dualizable in `D(A)`: the complex
`X[0]` is a bounded complex of dualizable objects (`DerivedCategory.isDualizable_Q_obj`). -/
theorem isDualizable_singleFunctor_obj {X : A} (hX : IsDualizable X) :
    IsDualizable ((singleFunctor A 0).obj X) := by
  refine (isDualizable_Q_obj ((HomologicalComplex.single A (.up ℤ) 0).obj X) 0 0
    fun n ↦ ?_).of_iso ((singleFunctorIsoCompQ A 0).app X).symm
  by_cases hn : n = 0
  · subst hn
    exact hX.of_iso (HomologicalComplex.singleObjXSelf _ 0 X).symm
  · exact IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ 0 X n hn)

end DerivedCategory
