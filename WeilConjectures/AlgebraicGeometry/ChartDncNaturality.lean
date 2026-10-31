/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData

/-! # A compatibility step in the etale-chart orientation argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartFactors

/-- The normalized DNC map commutes with the fixed source and differential-normal
comparisons. This is only the deformation factor; no integration orientation or
frame invariance is asserted.
Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 3, second paragraph
(blueprint: lem-pur-chart-dnc-naturality).
Proof: factor the chart through H = W_A times_A U. Restrict the full source pair
and H to the common etale neighbourhood O of their sections. Counit-normalized
section restriction gives R_i and R_r, and smooth base change gives B. The source
comparison is B R_r R_i inverse. Apply section-restriction coherence on O at the
one and zero endpoints: R_ni delta_O = delta_U R_i and
R_nr delta_O = delta_H R_r. Normalized base-change coherence gives
B_N delta_H = e*delta_A B. The coefficientwise Rees composition formula identifies
B_N R_nr R_ni inverse with the stated normal comparison, since its zero endpoint
sends [a] to [e*a]. Substitute these three equations and cancel R_i and R_ni.
Transport by the canonical site comparisons, using their naturality. The formulas
fix t and x_i/t, so normalized uniqueness introduces no unit or sign. The argument
also applies in rank zero and to the empty source. -/
theorem chart_dnc_naturality (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}} [IsAffine Y]
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  letI := P.noetherian (h ≫ aY)
  ((Dnc.existsUnique_dncInvariance P d (pullback.fst h h) (h ≫ aY)
      (pullback.diagonal h) (pullback.diagonal_fst h)).exists.choose).hom ≫
      (normal P d h aY e w).hom =
      (source P d h aY e w N).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.map
          ((Dnc.existsUnique_dncInvariance P d (pullback.fst p p) (p ≫ aY)
            (pullback.diagonal p) (pullback.diagonal_fst p)).exists.choose).hom := by sorry

end WeilConjectures.PurityFiniteSetting.ChartFactors
