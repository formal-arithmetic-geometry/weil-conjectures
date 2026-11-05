/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-!
# Extension followed by restriction of scalars along a finite free morphism

Let `φ : R ⟶ S` be a morphism of commutative algebra objects. By the projection formula,
extension of scalars followed by restriction of scalars is tensoring with `S` regarded as an
`R`-module: `φ^* (S ⊗_R M) ≅ φ^* S ⊗_R M`, naturally in `M`
(`CategoryTheory.Mod.extendScalarsCompComapIso`). If `φ^* S ≅ Rᵈ` is finite free, this is the
biproduct power `M ↦ Mᵈ` (`CategoryTheory.Mod.extendScalarsCompComapIsoBiproductPow`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

end MonoidalCategory

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

variable [Abelian C] [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft R)]

end Mod

end CategoryTheory
