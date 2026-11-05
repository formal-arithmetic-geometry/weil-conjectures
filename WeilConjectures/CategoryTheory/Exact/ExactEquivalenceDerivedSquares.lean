/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Derived squares under exact equivalences

Source: Stacks Tags 05RR and 0941.
(blueprint: lem-derived-exact-equivalence-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section KanSquare
variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* H₁] [Category* H₂]
  (P : C₁ ≌ C₂) (E : D₁ ≌ D₂) (G : H₁ ≌ H₂)
  (L : C₁ ⥤ D₁) (L' : C₂ ⥤ D₂)
  (F : C₁ ⥤ H₁) (F' : C₂ ⥤ H₂)
  (K : D₁ ⥤ H₁) (K' : D₂ ⥤ H₂)
  (ε : L ⋙ K ⟶ F) (ε' : L' ⋙ K' ⟶ F')
  (eL : L ⋙ E.functor ≅ P.functor ⋙ L')
  (eF : F ⋙ G.functor ≅ P.functor ⋙ F')

end KanSquare
attribute [local irreducible] kanSquareIso kanSquareCounit kanSquarePostCounit

section LeftKanSquare
variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* H₁] [Category* H₂]
  (P : C₁ ≌ C₂) (E : D₁ ≌ D₂) (G : H₁ ≌ H₂)
  (L : C₁ ⥤ D₁) (L' : C₂ ⥤ D₂)
  (F : C₁ ⥤ H₁) (F' : C₂ ⥤ H₂)
  (K : D₁ ⥤ H₁) (K' : D₂ ⥤ H₂)
  (ε : F ⟶ L ⋙ K) (ε' : F' ⟶ L' ⋙ K')
  (eL : L ⋙ E.functor ≅ P.functor ⋙ L')
  (eF : F ⋙ G.functor ≅ P.functor ⋙ F')

end LeftKanSquare
attribute [local irreducible] leftKanSquareIso leftKanSquareCounit leftKanSquarePostCounit

section CochainDerived
variable {B H : Type*} [Category* B] [Category* H] [Abelian B] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory H]
  (F : B ⥤ H) [F.Additive] (LF : DerivedCategory B ⥤ DerivedCategory H)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

end CochainDerived

attribute [local irreducible] derivedCochainCounit derivedCochainComparisonFactors

end CategoryTheory
