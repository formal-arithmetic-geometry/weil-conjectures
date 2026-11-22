/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange

/-!
# The two derived adjunctions of the étale extension by zero coincide

For an adjunction `adj : f ⊣ g` of exact functors between abelian categories, the levelwise
derived adjunction `Adjunction.mapDerivedCategoryAdjunction` (obtained from the total derived
adjunction) is the localization of the adjunction `adj.mapHomologicalComplex` of cochain
complexes along `DerivedCategory.Q`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_eq_localization`).

In particular, for an étale morphism `j`, the two derived adjunctions `D(j_!) ⊣ D(j^*)`
`AlgebraicGeometry.Etale.derivedEtaleLowerShriekMapAdjunction` and
`AlgebraicGeometry.Etale.derivedEtaleLowerShriekUpperStarAdjunction` are equal
(`AlgebraicGeometry.Etale.derivedEtaleLowerShriekMapAdjunction_eq`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory

section Factorsh

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- On the image of a cochain complex, the factorization isomorphism of `F.mapDerivedCategory`
through the homotopy category is the one through cochain complexes, up to the identifications
`DerivedCategory.quotientCompQhIso`. -/
@[reassoc]
lemma Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj_comp (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app ((F.mapHomologicalComplex _).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp [Functor.mapHomotopyCategoryFactors]

end Factorsh

section DerivedAdjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]

/-- The unit of the levelwise derived adjunction `Adjunction.mapDerivedCategoryAdjunction` on
`Q K` is, modulo the factorizations `Functor.mapDerivedCategoryFactors`, the image under `Q` of
the levelwise unit of `adj`. -/
lemma Adjunction.mapDerivedCategoryAdjunction_unit_app_Q_fac {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : CochainComplex C ℤ) :
    adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app K) ≫
        g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex _).obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) := by
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K)]
  have hη := adj.mapDerivedCategoryAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hη
  rw [reassoc_of% hη, ← Functor.map_comp_assoc,
    ← Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj_comp, Functor.map_comp,
    Category.assoc, ← Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj_comp]
  erw [reassoc_of% (adj.mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient C (.up ℤ)).obj K))]
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  exact DerivedCategory.quotientCompQhIso_hom_naturality _

/-- The levelwise derived adjunction `Adjunction.mapDerivedCategoryAdjunction` of an adjunction
`adj : f ⊣ g` of exact functors is the localization along `DerivedCategory.Q` of the adjunction
`adj.mapHomologicalComplex` of cochain complexes, the squares being given by the factorizations
`Functor.mapDerivedCategoryFactors`. -/
lemma Adjunction.mapDerivedCategoryAdjunction_eq_localization {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] :
    letI : CatCommSq (f.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q f.mapDerivedCategory :=
      ⟨f.mapDerivedCategoryFactors.symm⟩
    letI : CatCommSq (g.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q g.mapDerivedCategory :=
      ⟨g.mapDerivedCategoryFactors.symm⟩
    adj.mapDerivedCategoryAdjunction =
      (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization DerivedCategory.Q
        (HomologicalComplex.quasiIso _ _) DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
        _ _ := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  rw [Adjunction.localization_unit_app, ← adj.mapDerivedCategoryAdjunction_unit_app_Q_fac K]
  simp

end DerivedAdjunction

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {U Z : Scheme.{u}} (j : U ⟶ Z) [_root_.AlgebraicGeometry.Etale j]

/-- The two derived adjunctions `D(j_!) ⊣ D(j^*)` of an étale morphism `j` coincide: the one
obtained from the total derived adjunction (`derivedEtaleLowerShriekMapAdjunction`) and the one
obtained by localizing the adjunction of cochain complexes
(`derivedEtaleLowerShriekUpperStarAdjunction`). -/
theorem derivedEtaleLowerShriekMapAdjunction_eq :
    derivedEtaleLowerShriekMapAdjunction A j =
      derivedEtaleLowerShriekUpperStarAdjunction A j inferInstance :=
  Adjunction.mapDerivedCategoryAdjunction_eq_localization
    (etaleLowerShriekUpperStarAdjunction A j inferInstance)

end AlgebraicGeometry.Etale
