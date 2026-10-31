/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-! # The degree-zero exchange equation

This transparent proposition records the ordinary/derived exchange equation with
its four specified single-complex comparisons. It fixes the generic category
instances before specializing to categories of module sheaves.

Source: Stacks Project, Derived Categories, Tags 070K and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions C]

/-- Compatibility of exchange with the specified degree-zero comparisons.
All four comparisons are explicit data; this definition asserts exactly the displayed
equality, and does not assume any comparison or exchange is invertible.
Source: Stacks Project, Derived Categories, Tags 070K and 09T5
(blueprint: def-sf-derived-degree-zero-exchange-equation). -/
def DerivedDegreeZeroExchangeEquation
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ⟶ H ⋙ J)
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (cF : ∀ M : A,
      DerivedCategory.Q.obj ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ⟶
        F.rightDerivedFunctor.obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)))
    (cJ : ∀ M : C,
      DerivedCategory.Q.obj ((HomologicalComplex.single D (.up ℤ) 0).obj (J.obj M)) ⟶
        J.rightDerivedFunctor.obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj M)))
    (pG : ∀ M : B,
      G.mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single B (.up ℤ) 0).obj M)) ≅
        DerivedCategory.Q.obj ((HomologicalComplex.single D (.up ℤ) 0).obj (G.obj M)))
    (pH : ∀ M : A,
      H.mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≅
        DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj (H.obj M)))
    (M : A) : Prop :=
  G.mapDerivedCategory.map (cF M) ≫
      δ.app (DerivedCategory.Q.obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≫
      J.rightDerivedFunctor.map (pH M).hom =
    (pG (F.obj M)).hom ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (e.app M)) ≫
      cJ (H.obj M)

end CategoryTheory
