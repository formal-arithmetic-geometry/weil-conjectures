/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! K-flat representatives for an adjunction with exact right adjoint. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
namespace CategoryTheory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C] [HasExactColimitsOfShape ℤ C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private local instance rightDerivedExact :
    U.mapDerivedCategory.IsRightDerivedFunctor U.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso D (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ U.mapDerivedCategoryFactorsh

private local instance leftDerivedExactComp :
    (E.leftDerivedFunctor ⋙ U.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight E.leftDerivedFunctorCounit U.mapDerivedCategory)
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
  (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
    |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure _
      (fun P ↦ E.derives_kFlat.isIso_of_isLeftDerivedFunctor _ P) _

private local instance rightDerivedExactComp :
    (U.mapDerivedCategory ⋙ E.leftDerivedFunctor).IsRightDerivedFunctor
      (Functor.whiskerRight U.mapDerivedCategoryFactorsh.inv E.leftDerivedFunctor ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso D (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (asIso (Functor.whiskerRight U.mapDerivedCategoryFactorsh.inv E.leftDerivedFunctor ≫
      (Functor.associator _ _ _).hom)).symm

private noncomputable def exactDerivedAdjunction (adj : E ⊣ U) :
    E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
  (adj.mapHomotopyCategory (.up ℤ)).derived
    (HomotopyCategory.quasiIso C (.up ℤ))
    (HomotopyCategory.quasiIso D (.up ℤ))
    E.leftDerivedFunctorCounit U.mapDerivedCategoryFactorsh.inv

private theorem derived_unit_cochain (adj : E ⊣ U) (X : CochainComplex C ℤ) :
    let b := exactDerivedAdjunction E U adj
    let q₀ := (DerivedCategory.quotientCompQhIso C).app X
    let q₁ := (DerivedCategory.quotientCompQhIso D).app
      ((E.mapHomologicalComplex (.up ℤ)).obj X)
    let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
    b.unit.app (DerivedCategory.Q.obj X) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.inv ≫ ε ≫ q₁.hom) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
  let b := exactDerivedAdjunction E U adj
  let q₀ := (DerivedCategory.quotientCompQhIso C).app X
  let q₁ := (DerivedCategory.quotientCompQhIso D).app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  let q₂ := (DerivedCategory.quotientCompQhIso C).app
    ((U.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj X))
  let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  let d := E.leftDerivedFunctor.map q₀.inv ≫ ε ≫ q₁.hom
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    E.leftDerivedFunctorCounit U.mapDerivedCategoryFactorsh.inv
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have ht : b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) := by
    rw [← Category.assoc]
    erw [hfac]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hu := U.mapDerivedCategoryFactorsh_hom_app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hquot : DerivedCategory.Qh.map
      ((U.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj X)) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hquot] at hu
  erw [Category.comp_id] at hu
  have hu' : U.mapDerivedCategory.map q₁.hom ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) =
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
    have h := congrArg (fun z ↦ z ≫ q₂.hom) hu
    change U.mapDerivedCategoryFactorsh.hom.app
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom =
      (U.mapDerivedCategory.map q₁.hom ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.inv) ≫ q₂.hom at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h.symm
  change b.unit.app (DerivedCategory.Q.obj X) ≫ U.mapDerivedCategory.map d = _
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((E.mapHomologicalComplex (.up ℤ)).obj X))).mp
  apply (cancel_epi q₀.hom).mp
  have hn := b.unit.naturality q₀.hom
  change q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) =
    b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) at hn
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app X)
  have hd : E.leftDerivedFunctor.map q₀.hom ≫ d = ε ≫ q₁.hom := by
    change (E.leftDerivedFunctor.mapIso q₀).hom ≫
      ((E.leftDerivedFunctor.mapIso q₀).inv ≫ ε ≫ q₁.hom) = _
    exact Iso.hom_inv_id_assoc _ _
  have hdnat : q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫
      U.mapDerivedCategory.map d =
    b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom := by
    calc
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) ≫
          U.mapDerivedCategory.map d := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ U.mapDerivedCategory.map d) hn
      _ = _ := by
        rw [← U.mapDerivedCategory.map_comp, hd, Functor.map_comp]
  calc
    _ = b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom ≫
          U.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
        U.mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj X)) hdnat
    _ = b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫
        U.mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
      exact congrArg (fun z ↦ b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫ z) hu'
    _ = DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q₂.hom) ht
    _ = q₀.hom ≫ DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) := by
      erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      exact hq
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]

end CategoryTheory
