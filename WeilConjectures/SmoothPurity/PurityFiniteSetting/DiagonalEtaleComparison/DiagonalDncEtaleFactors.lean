/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData

/-! # Separating the normal-integration factor from the DNC dualizing factor

The local inverse factors through the actual normal-section invariant. The first
factor involves only the Tate restriction and beta; the second involves only DNC,
diagonal base change, open restriction and the coefficient-unit comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison

/-- Tate restriction followed by inverse normal integration.
Source: diagonal-dualizing proof Step 2.
(blueprint: lem-pur-diagonal-etale-local-inverse-factors). -/
def twistToNormal (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (C : OrientationRefinement.Chart P f aY d V) :=
  OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d ≪≫
    (OrientationRefinement.beta P f aY d V C.geometry C.betaEtale).symm

/-- Inverse deformation, diagonal base change and inverse target-open restriction.
Source: diagonal-dualizing proof Steps 1--2.
(blueprint: lem-pur-diagonal-etale-local-inverse-factors). -/
def normalToDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V) :=
  (OrientationRefinement.delta P f aY d V H).symm ≪≫
    OrientationRefinement.alpha P f aY d V H ≪≫
    (OrientationRefinement.rho P f aY d V H).symm ≪≫
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (OrientationCounit.unitChange P f))

/-- Factorization at the actual normal-section object, without any compatibility
assumption. Source: the defining four factors of theta.
(blueprint: lem-pur-diagonal-etale-local-inverse-factors). -/
theorem localInverse_factors (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (C : OrientationRefinement.Chart P f aY d V) :
    OrientationCounit.localInverse P d f aY V C =
      twistToNormal P d f aY V C ≪≫ normalToDualizing P d f aY V C.geometry := by
  unfold OrientationCounit.localInverse OrientationRefinement.theta
    twistToNormal normalToDualizing
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
