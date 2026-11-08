/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Adjunction
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationIso
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationComparisons

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Localizing a descended semilinear tower

Source: Stacks Project, Tags 03CY, 03DA, 06YY and 0H7J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow
  lisseTowerFixedRealization

/-- First pull fixed module sheaves from V to W, then use the prescribed realization
on W. This is a concrete functor, independent of descended levels and transitions.
Source: Stacks Tags 03CY and 0H7J
(blueprint: lem-weil-pbc-lisse-tower-localized-realization). -/
def lisseTowerLocalRealization {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (U : Y.ProEt)
    (V : U.left.ProEt) (W : Y.ProEt) (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ) :=
  (ProEtale.upperStar
    (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f.left).mapDerivedCategory ⋙
      lisseTowerFixedRealization (W.hom ≫ g) d n

/-- Comparisons for the concrete localized realization, after the transitions have
already descended. This record supplies no etale levels or normalization arrows.
Source: Stacks Tags 03DA, 06YY and 0H7J
(blueprint: lem-weil-pbc-lisse-tower-localized-realization). -/
structure LisseTowerLocalizedComparisons
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (U : Y.ProEt)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n)) where
  model : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (lisseTowerLocalRealization g d U V W f n).obj ((localProEtaleComparison V.hom
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E
  actual : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    (lisseTowerLocalRealization g d U V W f n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)
  scalar : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    normalizationRestrict (ProEt.topology V.left) (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerLocalRealization g d U V W f (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      lisseTowerLocalRealization g d U V W f n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  actual_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((lisseTowerLocalRealization g d U V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (scalar V W f n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual V W f n).hom =
    (H (n + 1)).map (actual V W f (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
  model_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model V W f j N) ≪≫
        ((constantAdicQuotientRightIso (W.hom ≫ g) d j).app N).symm
    (H (n + 1)).map ((lisseTowerLocalRealization g d U V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (scalar V W f n).hom.app ((localProEtaleComparison V.hom
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant U.left.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization (W.hom ≫ g) d).map (lisseTowerAlgebraArrow d n k)

end AlgebraicGeometry.Scheme
