module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro

@[expose] public section

universe wA wB vA vB uA uB
open CategoryTheory CategoryTheory.Limits

/-- Pointwise essentially constant systems assemble into derived functors.
Source: Stacks Project, Derived Categories, Definition 05S9 and Lemma 05SA.
(blueprint: new-everywhere-defined-derived-functors)

The construction chooses the representing values supplied by the hypotheses and
uses the universal comparison maps to define the functors on the localized
categories; functoriality is the content of Lemma 05SA. -/
theorem exists_everywhere_defined_derived_functors
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (hR : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram D X)
    (hL : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      let D := MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory A, IsEssentiallyConstantProDiagram D X) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (LG : DerivedCategory B ⥤ DerivedCategory A)
      (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF)
      (α : DerivedCategory.Qh ⋙ LG ⟶
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) := by
  sorry

end
