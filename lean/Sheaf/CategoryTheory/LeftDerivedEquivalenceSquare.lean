/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4, SHEAF group V1
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Left derived functors under exact equivalences

Source: Stacks Project, Tags 05RR and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace LeftDerivedEquivalenceSquare

private theorem rightKanExtension_precomp
    {C₀ C₁ D H : Type*} [Category* C₀] [Category* C₁] [Category* D] [Category* H]
    (P : C₀ ⥤ C₁) (L : C₁ ⥤ D) (F : C₁ ⥤ H) (K : D ⥤ H)
    (ε : L ⋙ K ⟶ F) [K.IsRightKanExtension ε]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Full]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Faithful] :
    K.IsRightKanExtension
      ((CategoryTheory.Functor.associator P L K).hom ≫
        CategoryTheory.Functor.whiskerLeft P ε) := by
  let G := CategoryTheory.Functor.RightExtension.precomp L F P
  have : G.IsEquivalence := by
    dsimp only [G, CategoryTheory.Functor.RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  dsimp [G, CategoryTheory.Functor.RightExtension.precomp,
    CategoryTheory.Functor.RightExtension.mk,
    CategoryTheory.Functor.whiskeringLeft]
  simp only [Category.id_comp, Category.comp_id]

private theorem rightKanExtension_postcomp
    {C D H H' : Type*} [Category* C] [Category* D] [Category* H] [Category* H']
    (L : C ⥤ D) (F : C ⥤ H) (K : D ⥤ H) (ε : L ⋙ K ⟶ F)
    [K.IsRightKanExtension ε] (e : H ≌ H') :
    (K ⋙ e.functor).IsRightKanExtension
      ((CategoryTheory.Functor.associator L K e.functor).inv ≫
        CategoryTheory.Functor.whiskerRight ε e.functor) := by
  let G := CategoryTheory.Functor.RightExtension.postcompose₂ L F e.functor
  have : G.IsEquivalence := by
    let α :
        (CategoryTheory.Functor.whiskeringRight D H H').obj e.functor ⋙
            (CategoryTheory.Functor.whiskeringLeft C D H').obj L ≅
          (CategoryTheory.Functor.whiskeringLeft C D H).obj L ⋙
            (CategoryTheory.Functor.whiskeringRight C H H').obj e.functor :=
      NatIso.ofComponents (fun (X : D ⥤ H) ↦
      (CategoryTheory.Functor.associator L X e.functor).symm) (by
        intro X Y f
        ext Z
        simp)
    change (CostructuredArrow.map₂ α.hom (𝟙 _)).IsEquivalence
    apply CostructuredArrow.isEquivalenceMap₂
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  exact ⟨⟨IsTerminal.ofIso h
    (CategoryTheory.Functor.RightExtension.postcompose₂ObjMkIso e.functor ε)⟩⟩

private theorem rightKanExtension_iso1
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {L L' : C ⥤ D} (e : L ≅ L') (F : C ⥤ H) (K : D ⥤ H)
    (ε : L ⋙ K ⟶ F) [K.IsRightKanExtension ε] :
    K.IsRightKanExtension
      ((CategoryTheory.Functor.isoWhiskerRight e K).inv ≫ ε) := by
  let G := (CategoryTheory.Functor.rightExtensionEquivalenceOfIso₁ e F).functor
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  change (𝟙 _ ≫ K.map (e.inv.app X) ≫ ε.app X) =
    K.map (e.inv.app X) ≫ ε.app X
  rw [Category.id_comp]

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

private def kanSquareCounit : L ⋙ (E.functor ⋙ K') ⟶ P.functor ⋙ F' :=
  (CategoryTheory.Functor.associator _ _ _).inv ≫
    CategoryTheory.Functor.whiskerRight eL.hom K' ≫
      (CategoryTheory.Functor.associator _ _ _).hom ≫
        CategoryTheory.Functor.whiskerLeft P.functor ε'

private def kanSquarePostCounit : L ⋙ (K ⋙ G.functor) ⟶ F ⋙ G.functor :=
  (CategoryTheory.Functor.associator _ _ _).inv ≫
    CategoryTheory.Functor.whiskerRight ε G.functor

private theorem kanSquare_universal [K'.IsRightKanExtension ε'] :
    (E.functor ⋙ K').IsRightKanExtension (kanSquareCounit P E L L' F' K' ε' eL) := by
  have := rightKanExtension_precomp P.functor L' F' K' ε'
  exact (CategoryTheory.Functor.isRightKanExtension_iff_postcomp₁
    E.functor eL _).mp inferInstance

private def kanSquareIso [K.IsRightKanExtension ε] [K'.IsRightKanExtension ε'] :
    K ⋙ G.functor ≅ E.functor ⋙ K' := by
  have hpost : (K ⋙ G.functor).IsRightKanExtension
      (kanSquarePostCounit G L F K ε) := rightKanExtension_postcomp L F K ε G
  have := kanSquare_universal P E L L' F' K' ε' eL
  exact CategoryTheory.Functor.rightKanExtensionUniqueOfIso _
    (kanSquarePostCounit G L F K ε) eF _
      (kanSquareCounit P E L L' F' K' ε' eL)

end KanSquare
section
variable {B H : Type*} [Category* B] [Category* H] [Abelian B] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory H]
  (F : B ⥤ H) [F.Additive] (LF : DerivedCategory B ⥤ DerivedCategory H)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

private theorem cochainCounit_universal
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] :
    LF.IsRightKanExtension (derivedCochainCounit F LF ε) := by
  have := CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension LF ε
    (HomotopyCategory.quasiIso B (.up ℤ))
  have := rightKanExtension_precomp (HomotopyCategory.quotient B (.up ℤ))
    DerivedCategory.Qh _ LF ε
  have h := rightKanExtension_iso1 (DerivedCategory.quotientCompQhIso B) _ LF
    ((CategoryTheory.Functor.associator _ _ _).hom ≫
      CategoryTheory.Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) ε)
  exact (CategoryTheory.Functor.isRightKanExtension_iff_of_iso₂ _
    (derivedCochainCounit F LF ε) (derivedCochainComparisonFactors F).symm (Iso.refl _) (by
      simp only [derivedCochainCounit, Iso.symm_hom,
        Iso.refl_hom, CategoryTheory.Functor.whiskerLeft_id', Category.id_comp,
        Category.assoc])).mp h

end

/-- An ordinary square of additive functors under equivalences induces a square
of their arbitrary total left derived functors, in independent localization universes.
Source: Stacks Project Tags 05RR and 0941
(blueprint: lem-zl-left-derived-equivalence-square).

Proof: precomposition and postcomposition by equivalences give equivalences on
categories of right Kan extensions. Precompose the homotopy-category universal
counits with the homotopy quotient, and use its fully faithful precomposition
functor to retain universality. The localization factorizations for the two exact
equivalences identify the two resulting extension problems. Uniqueness of their
terminal objects gives the displayed isomorphism. -/
theorem comparison
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε' : DerivedCategory.Qh ⋙ LF' ⟶
      L'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))]
    [LF'.IsLeftDerivedFunctor ε' (HomotopyCategory.quasiIso B' (.up ℤ))]
    (e : L ⋙ G.functor ≅ E.functor ⋙ L') :
    Nonempty (LF ⋙ G.mapDerivedCategory.functor ≅
      E.mapDerivedCategory.functor ⋙ LF') := by
  let εc := derivedCochainCounit L LF ε
  let εc' := derivedCochainCounit L' LF' ε'
  have : LF.IsRightKanExtension εc := cochainCounit_universal L LF ε
  have : LF'.IsRightKanExtension εc' := cochainCounit_universal L' LF' ε'
  let P := E.mapHomologicalComplex (.up ℤ)
  let ED := E.mapDerivedCategory
  let GD := G.mapDerivedCategory
  let eF : (L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ GD.functor ≅
      P.functor ⋙ (L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    CategoryTheory.Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft _ G.functor.mapDerivedCategoryFactors ≪≫
        (CategoryTheory.Functor.associator _ _ _).symm ≪≫
          CategoryTheory.Functor.isoWhiskerRight
            (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (L ⋙ G.functor)) (.up ℤ) ≪≫
              NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
              (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (E.functor ⋙ L')) (.up ℤ)).symm) DerivedCategory.Q ≪≫
            CategoryTheory.Functor.associator _ _ _
  exact ⟨kanSquareIso P ED GD DerivedCategory.Q DerivedCategory.Q _ _ LF LF' εc εc'
    E.functor.mapDerivedCategoryFactors eF⟩

end LeftDerivedEquivalenceSquare
end CategoryTheory
