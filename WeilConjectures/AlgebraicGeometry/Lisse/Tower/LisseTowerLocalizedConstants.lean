/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexComparisons

/-! # Constant complexes in the localized fixed realization

Source: Stacks Project, Tags 03CY, 03DA, 06YY and 0H7J. This is the constant-complex
part of localized realization, independent of any descended or normalized tower.
The three scheme morphisms need no relation to one another.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Constant models and their semilinear normalization square for the specified scalar
comparison. No actual tower, descended level, descent equation or choice of local
markings is involved.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY. This is step 3 and the constant-complex part of step 1
of lem-weil-pbc-lisse-tower-localized-realization.
(blueprint: lem-weil-pbc-lisse-tower-localized-constants).

Proof: work first with ordinary module sheaves. The constant-sheaf adjunction identifies
etale constants followed by comparison and inverse image along a and b with constants on Z.
Restrict algebraic scalars along constantAdicQuotientMap and
apply associated-module-sheafification. Its adjunction identifies this functor with
constant modules on X pulled to Z, with the actual inverse-image finite ring; the
coefficient identification is exactly lisseTowerFiniteCoefficientIso. This gives the
model comparison, natural in the algebraic module. Apply the construction termwise to
complexes and localize with mapDerivedCategoryCompIso to obtain model on every E.

For a semilinear arrow k, before localization the constant/quotient restriction square
commutes on every constant generator x: both composites carry x to k(x). The scalar
square used in lisseTowerPulledScalarIso is the uniquely section-normalized one, so
its underlying abelian map has this same action. The two further restriction
compositors are pbcDerivedRestrictComp on sheaves and restrictScalarsComp' on algebraic
modules. Localizing their ordinary generator equality produces precisely the
normalizationConstantRestrict and localProEtaleComparisonCoefficients factors in
localProEtaleNormalization of normalizationConstantArrow k, with those compositors.
Finally use the identity-on-constant-sections normalization that defines
constantAdicQuotientRightIso. Conjugating the localized equality by its inverse gives
the displayed equation and lisseTowerAlgebraArrow, including its two inverse
compositors. All functors are exact here. The argument uses arbitrary modules and
complexes and therefore also includes zero objects and empty schemes. -/
theorem lisseTower_localized_constants
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d j
    ∃ model : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (L n).obj ((localProEtaleComparison a
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization g d n).obj E,
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model j N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k) := by
  dsimp
  obtain ⟨model, hmodel⟩ := lisseTower_constant_complex_comparisons g a b d
  refine ⟨fun n E ↦ (model n).app E, ?_⟩
  exact lisseTower_localized_constants_normalization g a b d model hmodel

end AlgebraicGeometry.Scheme
