/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionModelOrientationDefinitions
import WeilConjectures.AlgebraicGeometry.ModelChartOrientationLocalCalculation
import WeilConjectures.AlgebraicGeometry.ModelChartOrientationAffineDescent

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Zero-section multiplication and the three beta identifications imply the local
beta-delta equation, in the actual compatible DNC coordinates.
Source: model descent Steps 5--6
(blueprint: lem-pur-model-chart-orientation-assembly).

Proof: choose compatible affine charts for the two smooth morphisms, or check on
the compatible-chart covering when no global charts exist. The DNC pasting identity
identifies kappa followed by total delta and the normal-coordinate comparison with
the tensor of the two delta and normal-coordinate comparisons, followed by nu.
Postcompose with b_(d+e), substitute its multiplication equation, and identify the
three beta maps using the stated frame identifications. Functoriality of tensor and
pullback yields precisely the beta-delta equation. Every map is compatible with
further open restriction. Their quotient is an automorphism of the total shifted Tate
line. Apply model_orientation_tate_detection on U to the compatible-chart cover;
its injectivity makes the two global isomorphisms equal.
Zero rank uses empty frames and the tensor-unit equations. -/
theorem model_chart_orientation_assembly (P : PurityFiniteSetting.{u})
    (G : P.ModelAffineGamma)
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (hzero : ∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
      [LocallyOfFiniteType aB] [QuasiCompact aB],
        ModelZeroOrientationEquation P G B d e aB)
    (hbeta : ∀ (U' V' T' : Scheme.{u}) [IsAffine U'] [IsAffine V'] [IsAffine T']
      (f' : U' ⟶ V') (g' : V' ⟶ T')
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (aT' : T' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT'] [QuasiCompact aT'],
        ModelChartBetaIdentification P G d e f' g' aT') :
    ModelChartOrientationEquation P d e f g aT := by
  apply model_chart_orientation_affine_descent P d e f g aT
  intro U' V' T' _ _ _ f' g' _ _ _ _ _ _ _ _ aT' _ _ x y _ _ hx hy
  apply model_chart_orientation_local_calculation P G d e f' g' aT' x y hx hy
    (composition_compatible_dnc_charts P d e f' g' aT' x y hx hy) hzero
  exact hbeta U' V' T' f' g' aT'

end WeilConjectures.PurityFiniteSetting
