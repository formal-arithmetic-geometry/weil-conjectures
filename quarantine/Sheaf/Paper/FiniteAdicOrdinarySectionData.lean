/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicImageNormalization

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-ordinary-section-data).

This module records one component of the canonical finite section diagrams.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace AdicCompactificationSections

open scoped ChangeOfRings

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary sections with the canonical image-arrow equation and unit normalization.
Source: BS 6.8.14(2), 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-ordinary-section-data). -/
structure FiniteAt (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    extends FiniteAtCore D l hl E R W where
  image_integral : ∀ F : sfRationalConstructibleCategory l E W.scheme,
    ImageNormalization D l hl E R W toFiniteAtCore F
  unit_module :
    (ContinuousRational.modulePull (W.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).coefficient).obj
      (SheafOfModules.unit (proEtaleModuleCoefficients
        (rationalCoefficientSheaf l (Spec (.of D.k)) E))) ≅
      SheafOfModules.unit (proEtaleModuleCoefficients
        (rationalCoefficientSheaf l W.scheme E))
  unit_module_one : ∀ V : (Spec (.of D.k)).ProEt,
    unit_module.hom.val.app
        (Opposite.op ((proEtaleBaseChange (W.scheme ↘ Spec (.of D.k))).obj V))
      (ContinuousRational.moduleUnit (W.scheme ↘ Spec (.of D.k))
        (R.along E (X := realizationBase D l hl W)
          (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
            (W.scheme ↘ Spec (.of D.k))).coefficient _ V
          (1 : (proEtaleModuleCoefficients
            (rationalCoefficientSheaf l (Spec (.of D.k)) E)).obj.obj (Opposite.op V))) =
      (1 : (proEtaleModuleCoefficients (rationalCoefficientSheaf l W.scheme E)).obj.obj
        (Opposite.op ((proEtaleBaseChange (W.scheme ↘ Spec (.of D.k))).obj V)))
  unit_pull :
    (ContinuousRational.derivedPull (W.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).coefficient).obj
        (point.J.obj (pointCoefficient D l hl E)) ≅ J.obj unit.obj
  unit_pull_normalized :
    unit_pull.hom ≫ heart.hom.app unit ≫
      (DerivedCategory.singleFunctor _ 0).map unit_sheaf.hom =
    (ContinuousRational.derivedPull (W.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).coefficient).map point.unit.hom ≫
      (R.along E (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).counit.app
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.unit (proEtaleModuleCoefficients
            (rationalCoefficientSheaf l (Spec (.of D.k)) E)))) ≫
      DerivedCategory.Q.map
        ((familyPullSingle l E R (X := realizationBase D l hl W)
          (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
            (W.scheme ↘ Spec (.of D.k))).hom.app _) ≫
      (DerivedCategory.singleFunctor _ 0).map unit_module.hom
  ordinary_sections : ∀ F, (ordinary.obj F : Type u) ≃ₗ[E]
    ((sheaf ⋙ sections l E W.scheme).obj F : Type (u + 1))
  ordinary_hom : ∀ F, (ordinary.obj F : Type u) ≃ₗ[E] (unit ⟶ F)
  /-- The actual derived adjunction transpose of the point-fibre H0-to-Hom map,
  followed by the realized coefficient unit. This equation uses direct_image. -/
  ordinary_hom_transpose : ∀ (F : sfRationalHeart l E W.scheme) (x : ordinary.obj F),
    J.map (ordinary_hom F x).hom = unit_pull.inv ≫
      ((direct_image (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).adjunction.homEquiv _ _).symm
        (point.J.map (point.hom (rationalImage D l hl E W.scheme F.obj)
          ((eqToIso (ordinary_obj F)).hom x)) ≫ (image F.obj).hom)
  natural_hom : ∀ (F G : sfRationalHeart l E W.scheme) (f : F ⟶ G) (x : ordinary.obj F),
    ordinary_hom G (ordinary.map f x) = ordinary_hom F x ≫ f
  evaluation_one : ∀ (F : sfRationalHeart l E W.scheme) (x : ordinary.obj F),
    (sheaf.map (ordinary_hom F x)).val.app (Opposite.op (ProEt.mk (𝟙 W.scheme)))
        ((unit_sheaf.inv).val.app (Opposite.op (ProEt.mk (𝟙 W.scheme)))
          (1 : (proEtaleModuleCoefficients
            (rationalCoefficientSheaf l W.scheme E)).obj.obj
              (Opposite.op (ProEt.mk (𝟙 W.scheme))))) =
      ordinary_sections F x
  natural_sections : ∀ (F G : sfRationalHeart l E W.scheme) (f : F ⟶ G)
      (x : ordinary.obj F),
    ordinary_sections G (ordinary.map f x) =
      (sections l E W.scheme).map (sheaf.map f) (ordinary_sections F x)

attribute [instance] FiniteAtCore.J_additive FiniteAtCore.J_linear

/-- The section 1 of the realized coefficient unit, on every site object.
Source: BS 6.8.14, coefficient normalization
(blueprint: def-a1-finite-adic-ordinary-section-data). -/
def unitSection {R : ContinuousRational.Family.{u} l} {W : Geometry D}
    (A : FiniteAt D l hl E R W) (V : W.scheme.ProEtᵒᵖ) :
    (A.sheaf.obj A.unit).val.obj V :=
  A.unit_sheaf.inv.val.app V
    (1 : (proEtaleModuleCoefficients (rationalCoefficientSheaf l W.scheme E)).obj.obj V)


end AdicCompactificationSections
end WeilConjectures
