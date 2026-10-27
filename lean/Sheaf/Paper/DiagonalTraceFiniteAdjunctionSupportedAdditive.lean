/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceSources
public import Sheaf.Paper.DiagonalTraceFiniteCartierChern

/-! # Additive supported-arrow operation

The direct-image construction in the supported-arrow half is additive in the
finite-arrow morphism.  This module records the resulting concrete operation
before forgetting its additive structure in the parent theorem.

Source: diagonal tower trace proof (2), direct-image/limit compatibility and
the common-unit normalization
(blueprint: new-sfb-diagonal-trace-finite-adjunction-supported-additive).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource completedSupportedUnit

/-- The supported-arrow operation is obtained as an additive homomorphism on
finite-arrow morphisms.  Its normalization is the displayed supported-arrow
identity; the parent theorem only needs the underlying function.

This is the direct-image/evaluation construction step of the proof.  The
remaining normalization calculation is kept here as the pending lower item so
that it can be proved independently of the existential packaging in the parent.
(blueprint: new-sfb-diagonal-trace-finite-adjunction-supported-additive). -/
theorem diagonalTrace_finiteAdjunction_supported_additive
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
    let VX := p.restrictionX.F.mapDerivedCategory
    let VS := p.restrictionS.F.mapDerivedCategory
    let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
    ∃ Φ : (UX.obj (completedUnit l (diagonalSurface Y)) ⟶ evX.obj (VX.obj line)) →+
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
          (completedUnit l (ProjectiveLine Y)) ⟶
            evS.obj (VS.obj ((SpTowerShriek.push l E p.base p.model.geometry).obj line))),
      ∀ γ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
        Φ (UX.map
            ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
              (completedSupportedUnit l Y) ≫ γ) ≫
          shiftedComparison UX (VX ⋙ p.LX.R) (p.coefficientsX.lineMap l E p.LX) 2 ≫
            (p.LX.projection n).app _) =
          (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
              (a.hom ≫ p.Rc.R.map γ) ≫ p.sourceMap l E ≫
            (p.LS.projection n).app _ ≫ evS.map (p.varying.inv.app _) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
