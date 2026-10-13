/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
import Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare
import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import Sheaf.AlgebraicGeometry.RawModuleScalarMapFormula
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas

/-! # Naturality of the fixed raw scalar comparison

Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
(blueprint: lem-sbc-raw-module-abelian-hom-map-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem scalar_comparison_pasting
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (M : C₀ ⥤ C₁) (VA : C₁ ⥤ D₁) (VB : C₀ ⥤ D₀) (H : D₀ ⥤ D₁)
    (e : M ⋙ VA ≅ VB ⋙ H) {L F : C₀} {X Y : C₁} {P Q : D₁} {R T : D₀}
    (cA : P ⟶ VA.obj X) (cB : R ⟶ VB.obj L)
    (bA : VA.obj Y ⟶ Q) (bB : VB.obj F ⟶ T)
    (mS : X ⟶ M.obj L) (mT : M.obj F ⟶ Y)
    (aS : P ⟶ H.obj R) (aT : H.obj T ⟶ Q)
    (hs : cA ≫ VA.map mS = aS ≫ H.map cB ≫ e.inv.app L)
    (ht : e.inv.app F ≫ VA.map mT ≫ bA = H.map bB ≫ aT) (z : L ⟶ F) :
    cA ≫ VA.map (mS ≫ M.map z ≫ mT) ≫ bA =
      aS ≫ H.map (cB ≫ VB.map z ≫ bB) ≫ aT := by
  have hn := e.inv.naturality z
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc cA (VA.map mS), hs]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ht]


set_option backward.isDefEq.respectTransparency true in
/-- The concrete scalar comparison commutes with the five-factor raw pullback.
Source: Stacks Project, Tags 03FD and 03Q8, with the inverse-image adjunction of 03D7.
(blueprint: lem-sbc-raw-module-abelian-hom-map-naturality).

Proof: Expand rawModuleAbelianHomMap and both raw pullbacks. The Kan-extension and
sheafification comparisons commute with their units. Under the inverse-image
adjunction their inverse therefore corresponds to the underlying module unit.
Naturality of this unit and the adjunction triangle identity show that its
composition comparison
commutes with upperStarComp. The same calculation applied to freeMap moves
the source generator comparison across the first pullback factor. The single
comparison commutes with scalar forgetting by naturality of
mapDerivedCategoryPlusSingleFunctor. Functoriality of derived forgetting moves
the class itself through the third factor. Compatibility of its commShiftIso
with the single comparison identifies the fourth factor. Finally the mate
composition equation identifies the inverse coefficient comparison with the
abelian upperStarComp inverse in the fifth factor. Associativity gives the
stated equality. No invertibility of the raw Hom map is needed in this argument;
in particular this is independent of the acyclicity argument of Tag 03FD.
The computation also applies to identity arrows, degree zero and empty objects. -/
theorem rawModuleAbelianHomMap_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∀ (A B : Over W) (f : A ⟶ B)
        (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)),
        rawModuleAbelianHomMap Λ k G q U A
          ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
          abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) q
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) B)
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) A)
            ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
              (Over.w f).symm).inv.app
                ((sheafCompose _
                  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G))
            U (rawModuleAbelianHomMap Λ k G q U B z) := by
  intro A B f z
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by
    rw [← Category.assoc, Over.w]
  let L := (freeSheaf Λ S).obj U
  let E := RawModuleScalarComparison.freeAbelian S U
  let t := RawModuleScalarComparison.freeMap Λ S U
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let VB := (RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlus
  let M := (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let LB := (upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k)).obj L
  let cA := scalarSourceFactor Λ (A.hom ≫ k) L E t
  let cB := scalarSourceFactor Λ (B.hom ≫ k) L E t
  let mS := moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k) w L
  let aS := abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k) w E
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G (q : ℤ)
  let bB := scalarCoefficientFactor Λ B.hom G (q : ℤ)
  let mT := moduleCoefficientFactor Λ G (q : ℤ) A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
    (q : ℤ) A B f
  let z' : ((DerivedCategory.Plus.singleFunctor _ 0).obj LB ⟶
    ((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦(q : ℤ)⟧) := z
  let e := RawModuleScalarComparison.derivedPullbackIso Λ f.left
  have hs := rawModuleScalar_source_square Λ f.left (B.hom ≫ k) (A.hom ≫ k) w L E t
  have ht := rawModuleScalar_coefficient_square Λ G (q : ℤ) A B f
  have hc := scalar_comparison_pasting M VA VB H e cA cB bA bB mS mT aS aT hs ht z'
  have hA := rawModuleScalar_map_formula Λ k G q U A
  have hB := rawModuleScalar_map_formula Λ k G q U B z
  have hf := rawModuleScalar_pullback_formulas Λ k G q U A B f z
  have hraw := hf.1
  have hab := hf.2 (rawModuleAbelianHomMap Λ k G q U B z)
  erw [hab, hA, hB, hraw]
  exact hc

end AlgebraicGeometry.Etale
