/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Cancelling the restricted homotopy counit comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Keep constructed functors abstract; expose only category aliases to implicit unification.
attribute [local irreducible] singleComplexOpenPullbackIso Functor.mapHomotopyCategory
  Functor.mapDerivedCategory openPinnedHomotopyTensorRestrictionIso
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory

private theorem remove_mapped_identity
    {C D : Type*} [Category C] [Category D] (F : D ⥤ C) (M : D)
    {A B E H : C} (s₁ : A ⟶ B) (s₂ : B ⟶ E) (s₃ : E ⟶ H)
    {J : C} (s₄ : H ⟶ J) (s₅ : J ⟶ F.obj M) :
    s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ F.map (𝟙 M) = s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ := by
  rw [F.map_id, Category.comp_id]

private theorem cancel_restriction_counit
    {C : Type*} [Category C] {A B D E H J K N : C}
    (k : A ≅ B) (s : A ⟶ D) (e : D ⟶ E) (b : E ⟶ H)
    (t : H ≅ J) (d : B ⟶ J) (v : E ⟶ K) (z : K ⟶ N)
    (q : H ⟶ N)
    (hc : s ≫ e ≫ b ≫ t.hom = k.hom ≫ d)
    (hn : v ≫ z = b ≫ q) :
    k.inv ≫ s ≫ e ≫ v ≫ z = d ≫ t.inv ≫ q := by
  have h := congrArg (fun a ↦ k.inv ≫ a ≫ t.inv) hc
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] at h
  simp only [hn]
  rw [reassoc_of% h]

set_option linter.unusedVariables false in
-- Preserve the existing unused F₀ and a bindings in the public statement.
end AlgebraicGeometry
