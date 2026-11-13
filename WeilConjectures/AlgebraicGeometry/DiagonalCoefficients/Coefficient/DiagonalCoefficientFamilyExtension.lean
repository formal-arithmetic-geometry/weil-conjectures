/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteExtension
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteClosure

/-! # Scalar extension of a diagonal diagram
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Extend a Z_l diagonal diagram to the integral, rational and closure
coefficient stages, with the specified scalar/direct-image mates. This result
requires neither a chosen Cartier class nor a completed reference. -/
theorem diagonalCoefficientFamily_extension
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)) :
    ∃ family : Family l Y, family.zl = d := by
  classical
  have hfinite := fun E : PadicAlgCl.FiniteIntermediateField l ↦
    diagonalCoefficient_finiteExtension l Y hY d E
  choose integral rational hIntegral hRational using hfinite
  let toIntegral := fun E ↦ (hIntegral E).some
  let toRational := fun E ↦ (hRational E).some
  obtain ⟨closure, hClosure, hTransitions⟩ :=
    diagonalCoefficient_finiteClosure l Y hY d integral rational toIntegral toRational
  exact ⟨{
    zl := d
    integral := integral
    rational := rational
    closure := closure
    toIntegral := toIntegral
    toRational := toRational
    toClosure := fun E ↦ (hClosure E).some
    rationalTransitions := fun E F h ↦ (hTransitions E F h).some }, rfl⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
