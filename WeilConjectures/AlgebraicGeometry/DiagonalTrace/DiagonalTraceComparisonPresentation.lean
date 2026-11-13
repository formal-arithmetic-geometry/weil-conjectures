/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonPartial
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonLimitIsos

/-! # Construction of the comparison data for the projective-line trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

/-- Construct the normalized geometric, scalar-restriction and limit comparisons,
without asserting the splitting or choosing a completed trace. -/
theorem exists_diagonalTraceComparisonPresentation
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (m : X ≅ ProjectiveLine S)
    (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ p : Presentation l (ULift.{u} (Padic l)) f, p.model.model = m := by
  obtain ⟨q, hq⟩ := exists_diagonalTraceComparisonPartial l f m hm hS
  obtain ⟨hu, hl⟩ := diagonalTraceComparisonLimitIsos l f m hm hS q
  let p : Presentation l (ULift.{u} (Padic l)) f :=
    { base := q.base
      chernS := q.chernS
      chernX := q.chernX
      normalizedS := q.normalizedS
      normalizedX := q.normalizedX
      finiteS := q.finiteS
      finiteX := q.finiteX
      twistS := q.twistS
      twistX := q.twistX
      model := q.model
      restrictionS := q.restrictionS
      restrictionX := q.restrictionX
      coefficientsS := q.coefficientsS
      coefficientsX := q.coefficientsX
      LS := q.LS
      LX := q.LX
      Rf := q.Rf
      Rt := q.Rt
      Rc := q.Rc
      varyingOrdinary := q.varyingOrdinary
      varying_sections := q.varying_sections
      varying := q.varying
      varying_normalization := q.varying_normalization
      completedOrdinary := q.completedOrdinary
      completed_sections := q.completed_sections
      completed := q.completed
      limits := q.limits
      unit_limit := hu
      line_limit := hl }
  exact ⟨p, hq⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
