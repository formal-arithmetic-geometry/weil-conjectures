/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceSources
public import Sheaf.Paper.DiagonalTraceFiniteCartierChern
import Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupportedAdditive

/-! # Supported-arrow half of the finite adjunction factorization

This is the first, source-side part of the generic finite factorization.  It
constructs the common operation and proves its equation on all supported
completed arrows.  The geometric-arrow equation is a separate statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource completedSupportedUnit

/-- The normalized operation on finite arrows satisfies the supported-arrow
identity.  The operation is subsequently characterized on geometric arrows by
`diagonalTrace_finiteAdjunction_geometric`.

Source: diagonal tower trace proof (2), direct-image/limit compatibility and the
common-unit normalization.  The proof constructs the operation by evaluation of
the derived direct image and then uses naturality of the completed square,
`SupportedSource.normalization`, and the projection equation of the normalized
limit comparison.  These calculations are independent of the geometric
adjunction calculation, so this theorem records precisely the supported half.
(blueprint: lem-sfb-diagonal-trace-finite-adjunction-supported).
-/
theorem diagonalTrace_finiteAdjunction_supported
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
    ∃ Φ : (UX.obj (completedUnit l (diagonalSurface Y)) ⟶ evX.obj (VX.obj line)) →
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
  let E := ULift.{u} (Padic l)
  let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
  let VX := p.restrictionX.F.mapDerivedCategory
  let VS := p.restrictionS.F.mapDerivedCategory
  let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
    (op n)).mapDerivedCategory
  let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
    (op n)).mapDerivedCategory
  let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
  obtain ⟨Φ, hΦ⟩ := diagonalTrace_finiteAdjunction_supported_additive l Y f p a n
  exact ⟨fun α => Φ α, hΦ⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
