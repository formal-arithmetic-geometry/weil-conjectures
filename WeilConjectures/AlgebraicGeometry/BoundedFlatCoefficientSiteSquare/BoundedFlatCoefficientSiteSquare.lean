/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ConstantCoefficientScalarExtensionPresentations
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import all WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The bounded-flat coefficient/site square

Source: Stacks Project, Tags 06YQ, 0G7E, 06YY, 07A4, 08G1 and 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square).

The fixed-scalar module-sheaf presentation retains the target-ring action. Every
comparison below is the published adjunction comparison, including its chain model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale
namespace BoundedFlatCoefficientSiteSquare

/-- Bundle flatness, strict support and K-flatness, without choosing a
resolution. Source: Stacks 06YQ and 08G1
(blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def modelProperties {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A] (a b : ℤ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) ∧
    (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P

/-- The actual chain comparison, obtained by applying the ordinary adjunction
comparison in each degree. Source: Stacks 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def chainComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (etaleSheafExtendScalars φ X ⋙ comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B)
        X))
      (.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X)
      (.up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X ⋙ sheafExtendScalars φ X))
        (.up ℤ)

private theorem cochain_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (_root_.DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app
    (_root_.DerivedCategory.Q.obj P))).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem ordinary_mate
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    ((mateEquiv (etaleSheafExtendScalarsAdjunction φ X)
      (sheafExtendScalarsAdjunction φ X)).symm
      (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict X φ).inv)).natTrans =
      (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv := by
  let a := etaleSheafExtendScalarsAdjunction φ X
  let b := sheafExtendScalarsAdjunction φ X
  let c := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let d := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let δ := ((mateEquiv a b).symm
    (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict X φ).inv))
  have h := iterated_mateEquiv_conjugateEquiv a b c d δ
  rw [Equiv.apply_symm_apply] at h
  rw [comparison_restrict_mate] at h
  apply (conjugateEquiv (a.comp d) (c.comp b)).injective
  change (conjugateEquiv (a.comp d) (c.comp b)) δ.natTrans = _
  rw [← h]
  change 𝟙 _ = (conjugateEquiv (a.comp d) (c.comp b))
    ((conjugateEquiv (a.comp d) (c.comp b)).symm (𝟙 _))
  exact (Equiv.apply_symm_apply _ _).symm

private theorem cochain_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (a : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

section Representative
universe u₁ u₂ v₁ v₂ w₁ w₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
  (d : L ⊣ U.mapDerivedCategory)

private def representative :
    _root_.DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙
      _root_.DerivedCategory.Q :=
  let η : _root_.DerivedCategory.Q ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q) ⋙ U.mapDerivedCategory :=
    { app P := _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
            (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
      naturality P R f := by
        simp only [← cochain_unit_formula]
        have hn := (a.mapHomologicalComplex (.up ℤ)).unit.naturality f
        change f ≫ _ = _ at hn
        rw [← _root_.DerivedCategory.Q.map_comp_assoc, hn]
        rw [_root_.DerivedCategory.Q.map_comp, Category.assoc]
        simpa only [Functor.comp_map, Category.assoc] using congrArg
          (fun b ↦ _root_.DerivedCategory.Q.map
            ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫ b)
          (U.mapDerivedCategoryFactors.inv.naturality
            ((E.mapHomologicalComplex (.up ℤ)).map f)) }
  { app P := (d.homEquiv _ _).symm (η.app P)
    naturality P R f := d.homEquiv_naturality_right_square
      (_root_.DerivedCategory.Q.map f) (η.app R) (η.app P)
      (_root_.DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map f))
      (η.naturality f) }

private theorem representative_unit (P : CochainComplex C ℤ) :
    d.unit.app (_root_.DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map ((representative E U a d).app P) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have h : d.unit.app (_root_.DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map ((representative E U a d).app P) =
      _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
            (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
    (d.homEquiv _ _).apply_symm_apply _
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [← cochain_unit_formula]

end Representative

private theorem cochain_left_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {G : B ⥤ D} [F.Additive] [G.Additive]
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (P : CochainComplex A ℤ) :
    ((mateEquiv (G := F.mapHomologicalComplex (.up ℤ))
      (H := G.mapHomologicalComplex (.up ℤ)) (a₁.mapHomologicalComplex (.up ℤ))
      (a₂.mapHomologicalComplex (.up ℤ))).symm
      (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex τ (.up ℤ)))).natTrans.app P =
    (NatTrans.mapHomologicalComplex
      (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).natTrans) (.up ℤ)).app P := by
  rw [left_mate_app]
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f]
  exact (left_mate_app a₁ a₂ τ (P.X i)).symm

private theorem cochain_scalar_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {L₂ : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (d₁ : L₁ ⊣ U₁.mapDerivedCategory) (d₂ : L₂ ⊣ U₂.mapDerivedCategory)
    (N : A ⥤ C) (N' : B ⥤ D) [N.Additive] [N'.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    (e : N' ⋙ U₂ ≅ U₁ ⋙ N) (P : CochainComplex A ℤ) :
    ((mateEquiv d₁ d₂).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv)).natTrans.app
        (_root_.DerivedCategory.Q.obj P) ≫
      N'.mapDerivedCategory.map ((representative E₁ U₁ a₁ d₁).app P) ≫
      N'.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) =
    L₂.map (N.mapDerivedCategoryFactors.hom.app P) ≫
      (representative E₂ U₂ a₂ d₂).app ((N.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans) (.up ℤ)).app P) := by
  have h := left_mate_normalization
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ)) d₁ d₂
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    (representative E₁ U₁ a₁ d₁) (representative E₂ U₂ a₂ d₂)
    U₁.mapDerivedCategoryFactors U₂.mapDerivedCategoryFactors
    N.mapDerivedCategoryFactors N'.mapDerivedCategoryFactors
    (NatTrans.mapHomologicalComplex e.inv (.up ℤ))
    (Functor.mapDerivedCategorySquareIso e).inv
    (representative_unit E₁ U₁ a₁ d₁) (representative_unit E₂ U₂ a₂ d₂)
    (by
      intro R
      simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
        NatTrans.comp_app, Category.assoc] using cochain_square_normalization e.symm R) P
  have hc := cochain_left_mate (F := N) (G := N') a₁ a₂ e.inv P
  rw [hc] at h
  exact h

private theorem cochain_scalar_mate_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {L₂ : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (d₁ : L₁ ⊣ U₁.mapDerivedCategory) (d₂ : L₂ ⊣ U₂.mapDerivedCategory)
    (N : A ⥤ C) (N' : B ⥤ D) [N.Additive] [N'.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    (e : N' ⋙ U₂ ≅ U₁ ⋙ N) (s : E₁ ⋙ N' ≅ N ⋙ E₂)
    (δ : N.mapDerivedCategory ⋙ L₂ ≅ L₁ ⋙ N'.mapDerivedCategory)
    (hδ : δ.hom = ((mateEquiv d₁ d₂).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv)).natTrans)
    (hs : ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans = s.inv)
    (P : CochainComplex A ℤ) :
    N'.mapDerivedCategory.map ((representative E₁ U₁ a₁ d₁).app P) ≫
      N'.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) =
    δ.inv.app (_root_.DerivedCategory.Q.obj P) ≫
      L₂.map (N.mapDerivedCategoryFactors.hom.app P) ≫
      (representative E₂ U₂ a₂ d₂).app ((N.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := cochain_scalar_mate a₁ a₂ d₁ d₂ N N' e P
  rw [← hδ, hs] at h
  apply (cancel_epi (δ.hom.app (_root_.DerivedCategory.Q.obj P))).1
  rw [Iso.hom_inv_id_app_assoc]
  calc
    _ = (_ ≫ _ ≫ _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex s.inv (.up ℤ)).app P)) ≫
        _root_.DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ _root_.DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P)) h
    _ = _ := by
      have hi := (NatIso.mapHomologicalComplex s (.up ℤ)).inv_hom_id_app P
      dsimp only [NatIso.mapHomologicalComplex] at hi
      rw [Category.assoc, Category.assoc, ← _root_.DerivedCategory.Q.map_comp, hi]
      rw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint in
private theorem comparison_normalization
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        (Etale.scalarExtensionRepresentative φ X P) ≫
      (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X).mapDerivedCategoryFactors.hom.app
        (((etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).hom (.up ℤ)).app P) =
    (pbcComparisonReduction X φ).inv.app (_root_.DerivedCategory.Q.obj P) ≫
      (SheafOfModules.constantCoefficientProEtaleScalarExtension φ X).map
        ((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapDerivedCategoryFactors.hom.app
          P) ≫
      SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ X
        (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact cochain_scalar_mate_iso
    (etaleSheafExtendScalarsAdjunction φ X) (sheafExtendScalarsAdjunction φ X)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X)
    (pbcComparisonRestrict X φ) (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X)
    (pbcComparisonReduction X φ) rfl (ordinary_mate X φ) P

end BoundedFlatCoefficientSiteSquare
end AlgebraicGeometry.ProEtale
