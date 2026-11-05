/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Extending statements from a property of objects to its localizing closure

Let `C` be a pretriangulated category and `P : ObjectProperty C`, with localizing closure
`Loc(P) = P.localizingClosure` (`WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure`).
The arguments of the blueprint which extend a statement from `P` to `Loc(P)` ("the objects
satisfying it form a localizing subcategory containing `P`") are collected here. They only need
the functors involved to be triangulated and to preserve the coproducts of objects of `Loc(P)`
(`CategoryTheory.Functor.PreservesCoproductsOn`), not all coproducts: for instance the proper
direct image preserves direct sums on `Loc(Dctf)` but not on the whole derived category.

## Main results

- `CategoryTheory.NatTrans.isIso_app_of_localizingClosure` (blueprint
  `sk-lem-sf-determination`): a natural transformation of triangulated functors, compatible with
  the shifts, between functors preserving the coproducts of objects of `Loc(P)`, which is an
  isomorphism on the objects of `P`, is an isomorphism on `Loc(P)`.
- `CategoryTheory.NatTrans.isIso_app_app_of_localizingClosure`: the same in two variables, for
  natural transformations of bifunctors (the argument of the projection formula).
- `CategoryTheory.ObjectProperty.localizingClosure_map`: a triangulated functor preserving the
  coproducts of objects of `Loc(P)` and mapping `P` into `Loc(Q)` maps `Loc(P)` into `Loc(Q)`.
- `CategoryTheory.ObjectProperty.localizingClosure_map₂`: the same for bifunctors which are
  triangulated and preserve coproducts in each variable (the argument of the tensor closure).
-/

@[expose] public section

universe w

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]

end Functor

variable {C D : Type*} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category.{w} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace ObjectProperty

variable {C' : Type*} [Category.{w} C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ (n : ℤ), (shiftFunctor C' n).Additive] [Pretriangulated C']

end ObjectProperty

namespace NatTrans

variable {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ]

variable {C' : Type*} [Category.{w} C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ (n : ℤ), (shiftFunctor C' n).Additive] [Pretriangulated C']

end NatTrans

end CategoryTheory
