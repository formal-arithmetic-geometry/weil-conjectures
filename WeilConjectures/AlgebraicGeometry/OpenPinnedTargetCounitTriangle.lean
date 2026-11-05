/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem targetOpenFactor
    {C : Type*} [Category C] {A B D E : C}
    (i : B ⟶ A) [Epi i] (h : A ⟶ B) (ε : A ⟶ D) (r : B ⟶ E)
    (v : D ⟶ E) (vi : E ⟶ D)
    (hih : i ≫ h = 𝟙 B) (hε : i ≫ ε = r ≫ vi) (hv : vi ≫ v = 𝟙 E) :
    h ≫ r = ε ≫ v := by
  apply (cancel_epi i).mp
  rw [← Category.assoc, hih, Category.id_comp, ← Category.assoc, hε,
    Category.assoc, hv, Category.comp_id]

private theorem targetTriangleAlgebra
    {C : Type*} [Category C] {A B D E F G H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E)
    (l : A ⟶ F) (n : F ⟶ D) (m : F ⟶ G) (e : G ⟶ E)
    (c : A ⟶ H) (ε : H ⟶ I) (h : G ⟶ I) (t : I ⟶ E)
    (hn : a ≫ b = l ≫ n) (ho : n ≫ d = m ≫ e)
    (hc : c ≫ ε = l ≫ m ≫ h) (ht : h ≫ t = e) :
    a ≫ b ≫ d = c ≫ ε ≫ t := by
  calc
    a ≫ b ≫ d = (a ≫ b) ≫ d := by simp only [Category.assoc]
    _ = (l ≫ n) ≫ d := by rw [hn]
    _ = l ≫ (m ≫ e) := by rw [Category.assoc, ho]
    _ = l ≫ m ≫ (h ≫ t) := by rw [ht]
    _ = (l ≫ m ≫ h) ≫ t := by simp only [Category.assoc]
    _ = c ≫ ε ≫ t := by rw [← hc, Category.assoc]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Termwise comparison for restricting the target of a composite tensor pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle). -/
def openPinnedHomotopyTargetCompositionIso
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens) :
    (Scheme.Modules.tensorPullback (U'.ι ≫ k)).mapHomotopyCategory (.up ℤ) ≅
      (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact (Functor.mapHomotopyCategoryCompIso
    (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm)
    (.up ℤ)).symm

-- Compare the chosen functors through their interfaces, without expanding sheaf data.
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

end AlgebraicGeometry
