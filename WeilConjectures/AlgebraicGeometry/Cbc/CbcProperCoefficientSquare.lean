/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportExchangeModel
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap

/-! # The proper factor of the completed coefficient square
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The proper exchange commutes with the unit-normalized scalar comparisons.
The comparison at the upper horizontal map is constructed at the same time; its
unit fixes it uniquely. No constructibility condition on the proper source is used. -/
theorem cbcProperCoefficientSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {Z Z' Y Y' : Scheme.{u}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'}
    {g : Y' ⟶ Y} {gb : Z' ⟶ Z} [IsProper p]
    (sq : ChosenCartesianSquare gb p' p g)
    (P : CbcCompletedScalarComparison l Ω g) :
    ∃ Q : CbcCompletedScalarComparison l Ω gb,
      ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
        (M : pbcAmbientStage l Ω Z E),
        (pbcStageDatum.{u} l Ω E).TowerComplete Z M →
        (pbcStageDatum.{u} l Ω F).completedExchange sq
            ((pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Z).obj M) ≫
          ((pbcStageDatum.{u} l Ω F).push p').map ((Q.map h).app M) ≫
          (pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) p').inv.app
            (((pbcStageDatum.{u} l Ω E).completedPull gb).obj M) =
        ((pbcStageDatum.{u} l Ω F).completedPull g).map
            ((pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) p).inv.app M) ≫
          (P.map h).app (((pbcStageDatum.{u} l Ω E).push p).obj M) ≫
          (pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Y').map
            ((pbcStageDatum.{u} l Ω E).completedExchange sq M) := by sorry

end AlgebraicGeometry.Scheme
