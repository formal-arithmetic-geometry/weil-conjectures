/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# Adjoints through conjugate isomorphisms

For conjugate natural transformations `α : L₂ ⟶ L₁` and `R₁ ⟶ R₂` of two adjunctions, the
adjunction bijections intertwine (`CategoryTheory.homEquiv_comp_conjugateEquiv_app`).
In a square of adjunctions (extension of scalars horizontally, pullback and pushforward
vertically), this computes the adjoint of a morphism out of a pulled back extension of scalars
through the conjugate isomorphism `Adjunction.pullIsoOfComapIso`
(`CategoryTheory.Adjunction.homEquiv_homEquiv_pullIsoOfComapIso_inv`): it is the adjoint of the
corresponding morphism out of the extension of scalars of the pullback, followed by the
isomorphism of restrictions of scalars of pushforwards.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)

end CategoryTheory.Adjunction
