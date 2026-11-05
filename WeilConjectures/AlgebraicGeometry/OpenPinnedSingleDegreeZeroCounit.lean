/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors

/-! # Restriction of the pinned single tensor counit
Source: Stacks Project, Tags 08DW, 08IB and 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The degree-zero counit selected by the pullback composition structure.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/
def openPinnedSingleDegreeZeroCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) :
    (derivedPullback k).obj ((DerivedCategory.singleFunctor.{w} _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor.{w} _ 0).obj ((Scheme.Modules.tensorPullback k).obj M) :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) 0).hom.app M))

private theorem assembleCounitSquare
    {C : Type*} [Category C] {A B C₀ D E F G H I J : C}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D) (d : D ⟶ E)
    (e : C₀ ⟶ F) (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ E)
    (i : A ⟶ I) (j : I ⟶ G) (k : I ⟶ J) (l : J ⟶ H) (s : A ⟶ J)
    (hT : c ≫ d = e ≫ f ≫ g ≫ h)
    (hc : a ≫ b ≫ e ≫ f = i ≫ j)
    (hn : k ≫ l = j ≫ g) (hR : i ≫ k = s) :
    a ≫ (b ≫ c) ≫ d = s ≫ l ≫ h := by
  calc
    a ≫ (b ≫ c) ≫ d = a ≫ b ≫ e ≫ f ≫ g ≫ h := by
      rw [Category.assoc, hT]
    _ = (a ≫ b ≫ e ≫ f) ≫ g ≫ h := by simp only [Category.assoc]
    _ = i ≫ j ≫ g ≫ h := by rw [hc, Category.assoc]
    _ = i ≫ k ≫ l ≫ h := by rw [← Category.assoc j, ← hn, Category.assoc]
    _ = s ≫ l ≫ h := by rw [← Category.assoc i, hR]

end AlgebraicGeometry
