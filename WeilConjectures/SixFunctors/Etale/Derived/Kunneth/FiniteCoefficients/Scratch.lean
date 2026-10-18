/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Constant complexes, the constant-tensor comparison and the Künneth morphism

For a commutative ring `Λ` (in the blueprint `Λ = 𝒪_E/ϖⁿ` or a finite field `𝔽_{ℓ^r}`) and a
scheme `W`, the constant complex functor `c_W : D(Mod_Λ) ⥤ D(W_ét, Λ)` is left adjoint to the
derived sections `RΓ_W` (`AlgebraicGeometry.Etale.constantComplexAdjunction`), and comes with a
monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N`
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`), the derived comonoidal structure of
the exact monoidal constant sheaf functor. With these we define

- `AlgebraicGeometry.Etale.constantProjectionMap` (`pur7710-def-constant-projection`):
  `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)`;
- `AlgebraicGeometry.Etale.globalSectionsKunnethMap` (`pur7710-def-kunneth-map`) and
  `AlgebraicGeometry.Etale.globalSectionsKunnethMapFiniteField`
  (`pur7710-def-kunneth-map-field`): `RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable (A : Type (u + 1)) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (W : Scheme.{u})
  [(constantSheaf W.smallEtaleTopology A).Monoidal]
  [(constantSheaf W.smallEtaleTopology A).PreservesFlat]
  [PreservesFiniteLimits (constantSheaf W.smallEtaleTopology A)]

noncomputable def testG (M N : DerivedCategory A) :
    (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj (M ⊗ N) ⟶
      ((-⊗ᴸ-(W)[A]).obj ((constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M)).obj
        ((constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj N) :=
  let F := constantSheaf W.smallEtaleTopology A
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  e.inv.app (M ⊗ N) ≫ (F.leftDerivedTensorComparison.app M).app N ≫
    ((-⊗ᴸ-(W)[A]).map (e.hom.app M)).app _ ≫ ((-⊗ᴸ-(W)[A]).obj _).map (e.hom.app N)

end Generic

end Etale

end AlgebraicGeometry
