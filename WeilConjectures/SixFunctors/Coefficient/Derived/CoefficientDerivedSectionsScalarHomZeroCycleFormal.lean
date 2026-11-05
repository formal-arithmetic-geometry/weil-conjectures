/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Global elements of the enriched adjunction map

A formal computation: the image of a global element `τ : U ⟶ Hom(P, G M)` under the
enriched adjunction map followed by a sections comparison is the transpose of an explicit
map out of a tensor product, once the scalar unit is known on the global unit class.

Source: Stacks Project, Tags 08J9 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
universe a b c d v w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

end WeilConjectures
