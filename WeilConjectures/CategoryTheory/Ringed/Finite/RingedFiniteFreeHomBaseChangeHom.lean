/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
/-! # The internal-Hom transpose component of finite-free base change.

The finite-free hypothesis and the normalized strong tensor comparison determine the
transpose uniquely; the proof is the restriction-of-scalars finite-biproduct argument
from Stacks Tags 08J9 and 08JA.
(blueprint: lem-sf-ringed-finite-free-hom-base-change)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

section Matrices
variable {A : Type*} [Category A] [HasZeroMorphisms A]

end Matrices

section Products
universe u
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  {H : Aᵒᵖ × A ⥤ A} (AR : WeilConjectures.CoefficientClosedStructure H)

end Products

section Naturality
universe u₁ v₁ u₂ v₂
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {K : Bᵒᵖ × B ⥤ B}
  (AR : WeilConjectures.CoefficientClosedStructure H)
  (AS : WeilConjectures.CoefficientClosedStructure K)
  (T : A ⥤ B) (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)

end Naturality

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

end Site
end CategoryTheory
