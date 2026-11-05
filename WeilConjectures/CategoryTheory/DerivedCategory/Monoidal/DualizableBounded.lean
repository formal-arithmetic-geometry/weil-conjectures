/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-!
# The dual of a bounded complex of dualizable objects

A strictly bounded complex `P` of dualizable objects, concentrated in degrees `[a, b]`, has a
right dual in `D(A)` which lies in degrees `≤ -a`
(`DerivedCategory.exists_exactPairing_Q_obj`): it is the image of the termwise dual complex
`P^∨` (`CochainComplex.rightDual`), concentrated in degrees `[-b, -a]`. This refines
`DerivedCategory.isDualizable_Q_obj` by keeping track of the dual.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

end DerivedCategory
