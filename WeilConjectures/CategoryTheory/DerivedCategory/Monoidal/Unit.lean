/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal

/-!

# The monoidal unit of the derived category

For a monoidal abelian category `C` whose derived category `D(C)` carries the derived monoidal
structure (`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`), the monoidal
unit of `D(C)` is the unit object of `C` placed in degree `0`
(`DerivedCategory.singleFunctorObjUnitIso`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace DerivedCategory

/-- The monoidal unit of `D(C)` is the unit object of `C` placed in degree `0`: the unit of the
monoidal category of complexes is `𝟙_ C` in degree `0`, and the unit comparison of the
localization `Qh : K(C) ⥤ D(C)` is an isomorphism. -/
noncomputable def singleFunctorObjUnitIso :
    (singleFunctor C 0).obj (𝟙_ C) ≅ 𝟙_ (DerivedCategory C) :=
  have : IsIso (Functor.LaxMonoidal.ε (Qh (C := C))) :=
    inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh
      (HomotopyCategory.quasiIso C (.up ℤ)))))
  (singleFunctorIsoCompQ C 0).app _ ≪≫ (quotientCompQhIso C).symm.app _ ≪≫
    Qh.mapIso ((Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ))).symm :
        (HomotopyCategory.quotient C (.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ≅ _) ≪≫
    (asIso (Functor.LaxMonoidal.ε Qh)).symm

end DerivedCategory
