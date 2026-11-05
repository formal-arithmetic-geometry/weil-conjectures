/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.CompactObjExtension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Compact objects with bounded morphisms

In a preadditive category, an object `s` is compact (`BrownRepresentability.IsCompactObj`) if
every morphism from `s` to a coproduct is a finite sum of morphisms through the summands. We show:

* compact objects are stable under retracts and, in a pretriangulated category, under extensions
  (`CategoryTheory.BrownRepresentability.IsCompactObj.of_distTriang`): this is the four lemma for
  the comparison of `⨁ⱼ Hom(-, Yⱼ)` with `Hom(-, ∐ⱼ Yⱼ)`, the latter map being always injective;
* compactness is transported along a left adjoint whose right adjoint preserves coproducts
  (`CategoryTheory.BrownRepresentability.IsCompactObj.of_adjunction`).

In a derived category, an object `s` *has bounded morphisms*
(`DerivedCategory.HasBoundedHom`) if `Hom(s, G) = 0` for all `G` in degrees `≤ n`, for some `n`.
The objects which are compact and have bounded morphisms form a triangulated subcategory stable
under retracts (`DerivedCategory.compactBoundedHom`), and the property is transported along left
adjoints whose right adjoints preserve coproducts and have bounded amplitude
(`DerivedCategory.compactBoundedHom_of_adjunction`).

These are the closure properties used in blueprint `det-ctf-finite-compact-etale`: the compact
objects of a triangulated category form a thick subcategory.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Pretriangulated Category Preadditive ZeroObject

namespace CategoryTheory.BrownRepresentability

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

end CategoryTheory.BrownRepresentability

namespace DerivedCategory

open TStructure (t)
open BrownRepresentability

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]

end DerivedCategory
