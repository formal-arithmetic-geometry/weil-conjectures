/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ConstantTensorTensorComparison

/-!
# The constant-tensor comparison as a transpose

The constant-tensor comparison is the transpose under `c_W ⊣ RΓ_W` of the monoidal comparison
followed by the counit (`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap_eq_homEquiv`).
Kept in its own file because the kernel needs a lot of memory to check it.
-/


@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (W : Scheme.{u})
  [(constantSheaf W.smallEtaleTopology A).PreservesFlat]


/-- The constant-tensor comparison is the transpose of the monoidal comparison followed by the
counit. -/
lemma derivedConstantSheafProjectionMap_eq_homEquiv
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M = (derivedConstantSheafAdjunction A W).homEquiv _ _
      (derivedConstantSheafTensorComparison A W _ M ≫
        (derivedConstantSheafAdjunction A W).counit.app K ▷ _) :=
  rfl


end Coefficients

end Etale

end AlgebraicGeometry
