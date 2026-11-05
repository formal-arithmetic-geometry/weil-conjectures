/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.CategoryTheory.Triangulated.IdempotentCompleteOfCoproducts

/-!
# Formal properties of the localizing closure

Let `P` be a property of objects of a pretriangulated category `C` whose `Hom`-types live in
`Type v`, and `Loc(P)` its localizing closure (`CategoryTheory.ObjectProperty.localizingClosure`).

* If `C` has coproducts indexed by `Type v`, then `Loc(P)` is idempotent complete
  (`CategoryTheory.ObjectProperty.isIdempotentComplete_localizingClosure`, blueprint
  `det-brown-hypotheses-ambient`).
* If `P` is stable under shifts, the objects of `P` detect zero objects of `Loc(P)`
  (`CategoryTheory.ObjectProperty.isZero_of_forall_eq_zero_localizingClosure`, blueprint
  `det-brown-hypotheses-generation`): the objects `M` with `Hom(M, Y⟦n⟧) = 0` for all `n` form
  a localizing subcategory.
* So, for `P` stable under shifts, `P` compactly generates `Loc(P)` as soon as it is essentially
  small and its objects are compact in `Loc(P)`
  (`CategoryTheory.ObjectProperty.CompactlyGeneratesLocalizingClosure.of_isStableUnderShift`).
* A triangulated functor `Φ : C₁ ⥤ C₂` mapping `P₁` into `Loc(P₂)`, whose restriction to
  `Loc(P₁)` preserves coproducts, maps `Loc(P₁)` into `Loc(P₂)`
  (`CategoryTheory.ObjectProperty.localizingClosure_obj_of_le`, the argument of blueprint
  `sk-prop-proper-image-localizing`).
-/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits Pretriangulated Category ZeroObject

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

variable {P}

end

section Map

variable {C₁ : Type u₁} [Category.{v} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (Φ : C₁ ⥤ C₂) [Φ.CommShift ℤ]
  [Φ.IsTriangulated]

end Map

end CategoryTheory.ObjectProperty
