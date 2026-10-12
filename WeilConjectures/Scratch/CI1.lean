import WeilConjectures.SixFunctors.ProEtale.Derived.ClopenIdempotent
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

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
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

lemma mapDerivedCategoryAdjunction_counit_app_Qh_obj (X : HomotopyCategory D (.up ℤ)) :
    adj.mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Qh.obj X) =
      f.mapDerivedCategory.map (g.mapDerivedCategoryFactorsh.hom.app X) ≫
        f.mapDerivedCategoryFactorsh.hom.app ((g.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app X) := by
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit X
  have h₂ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((g.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₄ := f.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (g.rightDerivedFunctorUnit.app X)
  dsimp at h₁ h₂ h₃ h₄
  simp only [mapDerivedCategoryAdjunction, ofNatIsoRight_counit, ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have h₃' : g.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj X) =
      g.mapDerivedCategoryFactorsh.hom.app X ≫ g.rightDerivedFunctorUnit.app X := by
    rw [← cancel_mono (g.rightDerivedFunctorIsoMapDerivedCategory.hom.app _),
      Iso.inv_hom_id_app, Category.assoc, h₃, Iso.hom_inv_id_app]
  rw [h₃', Functor.map_comp, Category.assoc, reassoc_of% h₄, derivedAdjunction, derived_counit,
    h₁, ← reassoc_of% h₂, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Adjunction
