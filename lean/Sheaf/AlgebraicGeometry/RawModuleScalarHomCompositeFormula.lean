/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation

/-! # The bundled scalar Hom composite

Source: Stacks Project, Tags 03FD and 03Q8, the explicit scalar map.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem map_three_factors
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z T : C} {P Q : D}
    (c : P ⟶ F.obj X) (b : F.obj T ⟶ Q)
    (m : X ⟶ Y) (z : Y ⟶ Z) (t : Z ⟶ T) (x : X ⟶ T)
    (h : x = m ≫ z ≫ t) :
    c ≫ F.map x ≫ b = c ≫ F.map m ≫ F.map z ≫ F.map t ≫ b := by
  rw [h, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

private theorem raw_triangle_whisker
    {C C' D E D' E' : Type*}
    [Category C] [Category C'] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (L : C ⥤ C') (H : C' ⥤ D) (H' : C' ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C)
    {K : D'} {K' : E'} (z : A.obj (H.obj (L.obj U)) ⟶ K) (s : F.obj K ⟶ K') :
    rawTriangleMap (L ⋙ H) (L ⋙ H') P A B F (Functor.whiskerLeft L c) e U z s =
      rawTriangleSource H H' P A B F c e (L.obj U) ≫ F.map z ≫ s := by
  simp only [rawTriangleMap, rawTriangleSource, Functor.comp_obj,
    Functor.whiskerLeft_app, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
/-- Expand the scalar map on a raw module pullback, retaining all module factors.
Source: Stacks Project, Tags 03FD and 03Q8, raw-map expansion.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).

Proof: Evaluate rawModuleAbelianHomMap as its defining additive composite:
derived scalar forgetting on Hom groups, right composition by its coefficient
morphism b, and left composition by its source morphism c. The definitions of
scalarCoefficientFactor and scalarSourceFactor identify b and c with the displayed
factors. Apply rawModuleScalar_pullback_module_formula to the raw pullback input,
inside the derived scalar-forgetting map. This replaces that input with the
module source factor, the derived module inverse image of z, and the module
coefficient factor. Distribute scalar forgetting by Functor.map_comp,
but do not use either scalar source coherence or inverse-comparison naturality.
The equality holds for zero classes, q = 0, identity f, and zero coefficients.
-/
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rw [rawModuleScalarHom_evaluate]
  apply map_three_factors
  exact raw_triangle_whisker (freeSheaf Λ S)
    (upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k))
    (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k))
    (upperStar (ModuleCat.{u + 1} Λ) f.left)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w])).hom
    ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).inv
    U z (moduleCoefficientFactor Λ G (q : ℤ) A B f)

end AlgebraicGeometry.Etale
