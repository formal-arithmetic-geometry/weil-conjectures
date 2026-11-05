/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # The normalized tower underlying a coefficient sequence

Source: Stacks Project, Tags 0940 and 0941; Bhatt--Scholze, Lemmas 3.5.4--3.5.7.
(blueprint: lem-coef-sequence-roos-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : C ⥤ E) (R : E ⥤ D)
  [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

@[irreducible] private def derivedTransition (τ : F ⟶ G ⋙ R) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso G R).hom

@[reassoc] private theorem derivedTransition_fac (τ : F ⟶ G ⋙ R)
    (K : CochainComplex C ℤ) :
    (derivedTransition F G R τ).app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  unfold derivedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

end CategoryTheory

namespace CategoryTheory
variable {C A B D E : Type*} [Category C] [Category A] [Category B]
  [Category D] [Category E] [Abelian C] [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]

@[irreducible] private def derivedMap
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    _ _ F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q)

@[reassoc] private theorem derivedMap_fac
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G)
    (K : CochainComplex A ℤ) :
    (derivedMap F G τ).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  unfold derivedMap
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

variable (U : C ⥤ A) (F : A ⥤ B) (G : C ⥤ D) (R : D ⥤ B)
  [U.Additive] [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

@[irreducible] private def derivedEvaluationIso (e : U ⋙ F ≅ G ⋙ R) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso U F).symm ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso G R

@[reassoc] private theorem derivedEvaluationIso_fac (e : U ⋙ F ≅ G ⋙ R)
    (K : CochainComplex C ℤ) :
    (derivedEvaluationIso U F G R e).hom.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      F.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  unfold derivedEvaluationIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors U F K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace WeilConjectures
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  coefficientSequenceEvaluation coefficientSequenceTransition
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

@[irreducible] private def restrictCompIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (e : f ≫ g = h) :
    SheafOfModules.restrictScalars.{u} g ⋙ SheafOfModules.restrictScalars.{u} f ≅
      SheafOfModules.restrictScalars.{u} h :=
  let e₀ : SheafOfModules.restrictScalars.{u} g ⋙ SheafOfModules.restrictScalars.{u} f ≅
      SheafOfModules.restrictScalars.{u} (f ≫ g) := normalizedDVRRestrictionCompIso f g
  e₀ ≪≫ eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) e)

end WeilConjectures
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace WeilConjectures

end WeilConjectures
