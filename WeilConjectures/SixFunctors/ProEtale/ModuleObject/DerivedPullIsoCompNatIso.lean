/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso

/-!
# The derived (Pull) isomorphism is induced by the underived one

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that every coefficient change
`a_X : Λ_X ⟶ Λ'_X` is flat, and `f : X ⟶ Y` a morphism of schemes. The derived (Pull)
isomorphism `ProEtale.CondensedRing.derivedPullIso a f : Lf^*_Λ ⋙ L(Ext_{a_X}) ≅
L(Ext_{a_Y}) ⋙ Lf^*_Λ'`, defined as a conjugate along the derived adjunctions, is the
isomorphism of composites of left derived functors induced by the underived (Pull) isomorphism
`ProEtale.CondensedRing.pullIso a f` (`Functor.leftDerivedFunctorCompNatIso`), all four functors
being exact (`ProEtale.CondensedRing.derivedPullIso_eq_leftDerivedFunctorCompNatIso`).
-/

@[expose] public section

universe u v u' u₁ u₂ u₃ u₄

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

section HomotopyCategory

variable {ι : Type*} {V₁ V₂ V₃ V₄ : Type*} [Category* V₁] [Category* V₂] [Category* V₃]
  [Category* V₄] [Preadditive V₁] [Preadditive V₂] [Preadditive V₃] [Preadditive V₄]
  {F₁ : V₁ ⥤ V₂} {F₂ : V₂ ⥤ V₄} {G₁ : V₁ ⥤ V₃} {G₂ : V₃ ⥤ V₄}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]

/-- The isomorphism `G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of functors between homotopy categories induced by an
isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of additive functors. -/
noncomputable def mapHomotopyCategoryCompNatIso (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) (c : ComplexShape ι) :
    G₁.mapHomotopyCategory c ⋙ G₂.mapHomotopyCategory c ≅
      F₁.mapHomotopyCategory c ⋙ F₂.mapHomotopyCategory c :=
  mapHomotopyCategoryCompIso (Iso.refl _) c ≪≫
    { hom := NatTrans.mapHomotopyCategory τ.hom c
      inv := NatTrans.mapHomotopyCategory τ.inv c
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] } ≪≫
    (mapHomotopyCategoryCompIso (Iso.refl _) c).symm

/-- The components of `CategoryTheory.Functor.mapHomotopyCategoryCompNatIso`. -/
lemma mapHomotopyCategoryCompNatIso_hom (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) (c : ComplexShape ι) :
    (mapHomotopyCategoryCompNatIso τ c).hom =
      ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) c).hom ≫
        NatTrans.mapHomotopyCategory τ.hom c) ≫
        (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) c).inv := by
  simp [mapHomotopyCategoryCompNatIso]

end HomotopyCategory

open Abelian

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  {D' : Type u₄} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The isomorphism `LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` induced by `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` is compatible
with the composite counits: on the image of a complex `K`, it is induced by `τ` on homotopy
categories. -/
lemma leftDerivedFunctorCompNatIso_hom_app_comp_counit (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (K : HomotopyCategory C (.up ℤ)) :
    (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app (DerivedCategory.Qh.obj K) ≫
        F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app K) ≫
        F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj K) =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app K) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app K ≫
            (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).inv.app K) := by
  rw [mapHomotopyCategoryCompIso_refl_hom_app, mapHomotopyCategoryCompIso_refl_inv_app,
    Category.id_comp, Category.comp_id]
  simp only [leftDerivedFunctorCompNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have k : (G₁.leftDerivedFunctorCompIso G₂).inv.app (DerivedCategory.Qh.obj K) ≫
      (G₁ ⋙ G₂).leftDerivedFunctorCounit.app K =
        G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app K) ≫
          G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory _).obj K) := by
    rw [← leftDerivedFunctorCompIso_hom_app_comp_counit, Iso.inv_hom_id_app_assoc]
  rw [leftDerivedFunctorCompIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
    reassoc_of% k]

end CategoryTheory.Functor

namespace CategoryTheory.Mod

variable {C : Type u'} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The counit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `M`,
in the form used by `CategoryTheory.Adjunction.mateEquiv_leftDerived_inv_eq`. -/
lemma derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq
    (M : HomotopyCategory (Mod C S) (ComplexShape.up ℤ)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj M) =
      (extendScalars φ).leftDerivedFunctor.map
          ((comap φ).mapDerivedCategoryFactorsh.hom.app M) ≫
        (extendScalars φ).leftDerivedFunctorCounit.app
          (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          (((extendRestrictAdjunction φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).counit.app M) := by
  rw [← derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Pull) is induced by the underived (Pull)**: for a flat coefficient change `a`, the derived
(Pull) isomorphism `Lf^*_Λ ⋙ L(Ext_{a_X}) ≅ L(Ext_{a_Y}) ⋙ Lf^*_Λ'` is the isomorphism of
composites of left derived functors induced by `pullIso a f`. -/
theorem derivedPullIso_eq_leftDerivedFunctorCompNatIso :
    derivedPullIso a f = Functor.leftDerivedFunctorCompNatIso
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ (f)^*⟦Λ⟧
      (Mod.extendScalars (coefficientMap a X)) (pullIso a f) := by
  refine Iso.ext ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).injective ?_)
  refine (mateEquiv_derivedPullIso_hom a f).trans ?_
  refine (Adjunction.mateEquiv_leftDerived_inv_eq
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (pullIso a f).symm (comapUpperStarIso a f).symm (mateEquiv_pullIso_hom a f)
    (Functor.mapHomotopyCategoryCompNatIso (pullIso a f) _).symm
    (Functor.mapHomotopyCategoryCompNatIso_hom (pullIso a f) _)
    _ _ _ _ ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac) _ _
    ((f)^*⟦Λ'⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq (coefficientMap a X))
    (Functor.leftDerivedFunctorCompNatIso (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧
      (f)^*⟦Λ⟧ (Mod.extendScalars (coefficientMap a X)) (pullIso a f)).symm _ rfl _ rfl
    (fun K ↦ ?_) _ rfl).symm
  simp only [Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompNatIso_hom, Category.assoc]
  exact Functor.leftDerivedFunctorCompNatIso_hom_app_comp_counit _ _ _ _ (pullIso a f) K

end AlgebraicGeometry.ProEtale.CondensedRing
