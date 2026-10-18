/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant

/-!
# The constant-tensor comparison is a projection map

For a scheme `W` and a coefficient category `A`, the constant-tensor comparison
`RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` (`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap`,
whose instance at `A = ModuleCat Λ` is `AlgebraicGeometry.Etale.constantProjectionMap`, blueprint
`pur7710-def-constant-projection`) is the projection map of the adjunction `c_W ⊣ RΓ_W`
(`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap_eq`,
`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`). The comparisons are kept in their own
file because the kernel needs a lot of memory to check them.
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

/-- The monoidal comparison of constant complexes is the tensor comparison
`CategoryTheory.Functor.mapDerivedCategoryTensorComparison` of the functor induced by the
constant sheaf functor. -/
lemma derivedConstantSheafTensorComparison_eq (M N : DerivedCategory A) :
    derivedConstantSheafTensorComparison A W M N =
      ((Functor.mapDerivedCategoryTensorComparison
        (constantSheaf W.smallEtaleTopology A)).app M).app N := by
  rw [Functor.mapDerivedCategoryTensorComparison_app_app]
  rfl

/-- The constant-tensor comparison is the transpose of the monoidal comparison followed by the
counit. -/
lemma derivedConstantSheafProjectionMap_eq_homEquiv
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M = (derivedConstantSheafAdjunction A W).homEquiv _ _
      (derivedConstantSheafTensorComparison A W _ M ≫
        (derivedConstantSheafAdjunction A W).counit.app K ▷ _) :=
  rfl

/-- The constant-tensor comparison `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` is the projection map of
the adjunction `c_W ⊣ RΓ_W` (`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`). -/
lemma derivedConstantSheafProjectionMap_eq (K : DerivedCategory (Sheaf W.smallEtaleTopology A))
    (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M =
      (Functor.mapDerivedCategoryProjectionMap (derivedConstantSheafAdjunction A W) K).app M :=
  (derivedConstantSheafProjectionMap_eq_homEquiv A W K M).trans
    (Functor.homEquiv_comp_counit_eq_mapDerivedCategoryProjectionMap_app
      (derivedConstantSheafAdjunction A W) (derivedConstantSheafTensorComparison A W)
      (derivedConstantSheafTensorComparison_eq A W) K M)

end Coefficients

end Etale

end AlgebraicGeometry
