/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

/-! # Canonical source coordinates for open orientation descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The total delta-beta arrow, before the kappa source comparison.
Source: model descent Steps 6--9.
(blueprint: def-pur-model-chart-orientation-restriction). -/
def modelChartLeft (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  P.chartDiagonalDelta (d + e) (f ≫ g) aT ≪≫
    P.chartDiagonalBeta (d + e) (f ≫ g) aT t

/-- The tensor delta-beta arrow, expressed on the total section source by kappa inverse.
Source: model descent Steps 6--9.
(blueprint: def-pur-model-chart-orientation-restriction). -/
def modelChartRight (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  (P.compatibleKappa d e f g aT).symm ≪≫
    P.compatibleTensorIso
      (P.chartDiagonalDelta d f (g ≫ aT) ≪≫ P.chartDiagonalBeta d f (g ≫ aT) t)
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.chartDiagonalDelta e g aT ≪≫ P.chartDiagonalBeta e g aT t)) ≪≫
      P.modelOrientationMu d e f (g ≫ aT)

/-- Restriction of the section source through its ordinary section presentation.
No orientation is used in this comparison: it is restriction of the ordinary
section presentation through the comparison functor.
Source: model descent Steps 8--9 and the open-section comparison of diagonal pasting.
(blueprint: def-pur-model-chart-orientation-restriction). -/
def modelChartSectionRestriction (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (r : ℕ) (h : X ⟶ Y) (h' : X' ⟶ Y') (j : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension r h] [SmoothOfRelativeDimension r h']
    (w : j ≫ h = h' ≫ v)
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (v ≫ aY)
  letI := P.noetherian (h' ≫ v ≫ aY)
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
    (Dnc.sourceComparison P r (pullback.fst h h) (h ≫ aY) (pullback.diagonal h)) ≪≫
  Dnc.pullComparison P j (DiagonalPasting.diagonalSection P.Coefficient P h) ≪≫
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.mapIso
      (DiagonalPasting.openSection P.Coefficient P r h h' j v w (h ≫ aY)) ≪≫
  (Dnc.sourceComparison P r (pullback.fst h' h') (h' ≫ v ≫ aY)
    (pullback.diagonal h')).symm
end WeilConjectures.PurityFiniteSetting
