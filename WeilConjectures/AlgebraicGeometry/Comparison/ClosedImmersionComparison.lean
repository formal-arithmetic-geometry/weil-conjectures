/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageUnit
public import WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounitGeneral
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStarCanonical

/-!
# Comparison for closed immersions and the localization triangle

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and `Λ` a commutative
ring. The comparison functor `ν^*` from étale to pro-étale sheaves of `Λ`-modules satisfies:

* `ν_X^* Ri_* ≅ Ri_* ν_Z^*` on `D⁺(Z_ét, Λ)`: this is
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso i`, a closed immersion being
  quasi-compact and quasi-separated;
* `i^* ν_X^* ≅ ν_Z^* i^*`: this is `AlgebraicGeometry.ProEtale.fixedComparisonPullbackPlus`;
* `AlgebraicGeometry.ProEtale.comparisonUpperStar_openClosed_triangle`: these isomorphisms and
  `AlgebraicGeometry.ProEtale.properOpenSiteExtensionIso` (the derived form of (2.10)) carry
  `ν_X^*` of the étale localization triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶` to a distinguished
  triangle `j_! j^* ν^* K ⟶ ν^* K ⟶ Ri_* i^* ν^* K ⟶` whose first two maps are the counit of
  `j_! ⊣ j^*` and the unit of `i^* ⊣ Ri_*` on `X_proét`
  (blueprint: `proposition-comparison-immersions--3`).

The étale localization triangle on `D⁺` is
`AlgebraicGeometry.Etale.exists_distTriang_openClosed_plus`, deduced from the unbounded one
`AlgebraicGeometry.Etale.exists_distTriang_openClosed`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangle in a triangulated subcategory with prescribed first two maps can be completed
to a distinguished triangle as soon as their images can be completed to a distinguished
triangle in the ambient category. -/
lemma exists_distTriang_of_ι_map (P : ObjectProperty C) [P.IsTriangulated]
    {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : P.ι.obj Z ⟶ (P.ι.obj X)⟦(1 : ℤ)⟧)
    (hw : Triangle.mk (P.ι.map f) (P.ι.map g) w ∈ distTriang C) :
    ∃ w', Triangle.mk f g w' ∈ distTriang P.FullSubcategory := by
  refine ⟨P.fullyFaithfulι.preimage (w ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X),
    isomorphic_distinguished _ hw _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_)⟩
  simp [Functor.mapTriangle]

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {Z U X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- The étale localization triangle on bounded below complexes: for a closed immersion `i` with
open complement `j` and `K ∈ D⁺(X_ét, Λ)`, the counit `j_! j^* K ⟶ K` and the unit
`K ⟶ Ri_* i^* K` extend to a distinguished triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`. -/
theorem Etale.exists_distTriang_openClosed_plus (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ w, Triangle.mk
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j).counit.app K)
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app K) w ∈
        distTriang _ := by
  obtain ⟨w, hw⟩ := Etale.exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij
    (DerivedCategory.Plus.ι.obj K)
  let adjU := Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  let adjD := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).derivedAdjunction
    |>.ofNatIsoLeft
      (Etale.upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctorIsoMapDerivedCategory
  have hu := Adjunction.map_restrictFullyFaithful_unit_app adjD
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusCompatibility.symm
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlusCompatibility.symm K
  rw [← Adjunction.unit_rightAdjointUniq_hom_app adjU adjD] at hu
  have hc := Adjunction.map_restrictFullyFaithful_counit_app
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j
      ).mapDerivedCategoryPlusCompatibility.symm
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlusCompatibility.symm K
  let e := (adjU.rightAdjointUniq adjD).app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj K)) ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlusCompatibility.symm.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K)
  refine ObjectProperty.exists_distTriang_of_ι_map _ _ _ (e.inv ≫ w)
    (isomorphic_distinguished _ hw _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ (by simp)))
  · dsimp only [Triangle.mk_mor₁, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    exact hc.trans (by simp [Functor.mapDerivedCategoryPlusCompatibility])
  · dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
    erw [hu]
    simp only [e, Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.refl_hom, Category.id_comp]
    erw [CategoryTheory.Functor.map_id]
    simp [adjU]


/-- Comparison for closed immersions and the localization triangle: let `i : Z ⟶ X` be a closed
immersion with open complement `j : U ⟶ X` and `K ∈ D⁺(X_ét, Λ)`. The isomorphisms
`e₁ : ν_X^* j_! j^* K ≅ j_! ν_U^* j^* K ≅ j_! j^* ν_X^* K` (from (2.10),
`properOpenSiteExtensionIso`, and the inverse-image comparison `fixedComparisonPullbackPlus`) and
`e₃ : ν_X^* Ri_* i^* K ≅ Ri_* ν_Z^* i^* K ≅ Ri_* i^* ν_X^* K` (from the direct-image comparison
`rightDerivedLowerStarComparisonPlusIso` and the inverse-image comparison) carry `ν_X^*` of the
étale localization triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶` to a distinguished triangle
`j_! j^* ν^* K ⟶ ν^* K ⟶ Ri_* i^* ν^* K ⟶` whose first two maps are the counit of
`j_! ⊣ j^*` and the unit of `i^* ⊣ Ri_*` on `X_proét`
(blueprint: `proposition-comparison-immersions--3`). -/
theorem ProEtale.comparisonUpperStar_openClosed_triangle
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (w : (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) i).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) ⟶
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K))⟦(1 : ℤ)⟧)
    (hw : Triangle.mk
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j).counit.app K)
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app K) w ∈
        distTriang _) :
    ∃ w', Triangle.mk
        ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j).counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K))
        ((ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K)) w' ∈
          distTriang _ ∧
      ∃ φ : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.mapTriangle.obj
          (Triangle.mk
            ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
              (ModuleCat.{u + 1} Λ) j).counit.app K)
            ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app K)
            w) ≅
          Triangle.mk
            ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
              (ModuleCat.{u + 1} Λ) j).counit.app
                ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K))
            ((ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
                ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K)) w',
        φ.hom.hom₁ = (ProEtale.properOpenSiteExtensionIso Λ j).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) ≫
          (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
            ((ProEtale.fixedComparisonPullbackPlus Λ j).hom.app K) ∧
        φ.hom.hom₂ = 𝟙 _ ∧
        φ.hom.hom₃ = (ProEtale.rightDerivedLowerStarComparisonPlusIso i
            (ModuleCat.{u + 1} Λ)).hom.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) ≫
          (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlus.map
            ((ProEtale.fixedComparisonPullbackPlus Λ i).hom.app K) := by
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus
  let e₁ := (ProEtale.properOpenSiteExtensionIso Λ j).app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) ≪≫
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.mapIso
      ((ProEtale.fixedComparisonPullbackPlus Λ j).app K)
  let e₃ := (ProEtale.rightDerivedLowerStarComparisonPlusIso i (ModuleCat.{u + 1} Λ)).app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlus.mapIso
      ((ProEtale.fixedComparisonPullbackPlus Λ i).app K)
  have h₁ := ProEtale.comparisonUpperStar_map_openImmersionLowerShriek_counit Λ j K
  have h₂ := ProEtale.fixedComparisonDirectImageMatePlus_unit Λ i K
  let T := ν.mapTriangle.obj (Triangle.mk
    ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).counit.app K)
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app K) w)
  let φ : T ≅ Triangle.mk
      ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j).counit.app (ν.obj K))
      ((ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
        (ν.obj K)) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') :=
    Triangle.isoMk _ _ e₁ (Iso.refl _) e₃ ?_ ?_ (by simp)
  · exact ⟨_, isomorphic_distinguished _ (ν.map_distinguished _ hw) _ φ.symm, φ, rfl, rfl, rfl⟩
  · rw [Iso.refl_hom, Category.comp_id]
    exact h₁.trans (Category.assoc _ _ _).symm
  · have h₂' : T.mor₂ ≫ (ProEtale.rightDerivedLowerStarComparisonPlusIso i
        (ModuleCat.{u + 1} Λ)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) =
        (ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
          (ν.obj K) ≫ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlus.map
            ((ProEtale.fixedComparisonPullbackPlus Λ i).inv.app K) := h₂
    simp only [e₃, Iso.refl_hom, Category.id_comp, Triangle.mk_mor₂, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    erw [reassoc_of% h₂']
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The pro-étale localization triangle for objects of étale origin: for a closed immersion `i`
with open complement `j` and `K ∈ D⁺(X_ét, Λ)`, the counit `j_! j^* ν^* K ⟶ ν^* K` and the unit
`ν^* K ⟶ Ri_* i^* ν^* K` extend to a distinguished triangle in `D⁺(X_proét, Λ)`
(blueprint: `proposition-comparison-immersions--3`). It is obtained from
`ProEtale.comparisonUpperStar_openClosed_triangle` and the étale localization triangle
`Etale.exists_distTriang_openClosed_plus`; no quasi-compactness of `j` is needed. -/
theorem ProEtale.exists_distTriang_comparisonUpperStar_openClosed
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ w', Triangle.mk
        ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j).counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K))
        ((ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K)) w' ∈
          distTriang _ := by
  obtain ⟨w, hw⟩ := Etale.exists_distTriang_openClosed_plus Λ i j hij K
  obtain ⟨w', hw', -⟩ := ProEtale.comparisonUpperStar_openClosed_triangle Λ i j K w hw
  exact ⟨w', hw'⟩

end AlgebraicGeometry
