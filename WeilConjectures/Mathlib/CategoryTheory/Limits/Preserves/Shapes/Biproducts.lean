/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Data.Finite.Prod

/-!
# Underlying types of binary biproducts

If the forgetful functor of a concrete preadditive category preserves binary products, the
underlying type of a binary biproduct is the product of the underlying types
(`CategoryTheory.Limits.biprod.toTypeEquiv`); in particular a binary biproduct of objects
with finite underlying types has finite underlying type.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [HasBinaryBiproducts A]
  {FA : A → A → Type v} {CA : A → Type v} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{v} A FA] [PreservesFiniteProducts (CategoryTheory.forget A)]

/-- The underlying type of a binary biproduct is the product of the underlying types, if the
forgetful functor preserves binary products:
`ToType (M ⊞ N) ≃ ToType (M ⨯ N) ≃ ToType M ⨯ ToType N ≃ ToType M × ToType N`. -/
noncomputable def biprod.toTypeEquiv (M N : A) : ToType (M ⊞ N) ≃ ToType M × ToType N :=
  ((CategoryTheory.forget A).mapIso (biprod.isoProd M N) ≪≫
    PreservesLimitPair.iso (CategoryTheory.forget A) M N ≪≫
    Types.binaryProductIso _ _).toEquiv

instance (M N : A) [Finite (ToType M)] [Finite (ToType N)] : Finite (ToType (M ⊞ N)) :=
  .of_equiv _ (biprod.toTypeEquiv M N).symm

end CategoryTheory.Limits
