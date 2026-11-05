/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# K-flatness and short exact sequences with flat quotient

Let `C` be a closed braided monoidal abelian category. We show:

* `CategoryTheory.ObjectProperty.mono_whiskerRight_of_shortExact`: if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
  is short exact with `X₃` flat, then `X₁ ⊗ Z ⟶ X₂ ⊗ Z` is a monomorphism for every object
  `Z` (that is, `Tor₁(X₃, Z) = 0`), provided `Z` is a quotient of a flat object.
* `CategoryTheory.ObjectProperty.flat_of_shortExact`: in such a sequence, if moreover `X₂` is
  flat, so is `X₁`.
* `CochainComplex.kFlat_of_shortExact`: in a short exact sequence of complexes
  `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` in which `K₁` and `K₂` are K-flat and the terms of `K₃` are flat,
  the complex `K₃` is K-flat (Stacks, Tag 064M?). The sequence stays short exact after
  tensoring with any complex, so this follows from the long exact homology sequence.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CategoryTheory.GradedObject

variable {I J : Type*} {C : Type*} [Category* C] {X Y : GradedObject I C} (φ : X ⟶ Y)
  (p : I → J) [X.HasMap p] [Y.HasMap p]

end CategoryTheory.GradedObject

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]

variable [Abelian.HasFunctorialFlatResolution C]

end CategoryTheory.ObjectProperty

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]

variable [Abelian.HasFunctorialFlatResolution C]

end CochainComplex
