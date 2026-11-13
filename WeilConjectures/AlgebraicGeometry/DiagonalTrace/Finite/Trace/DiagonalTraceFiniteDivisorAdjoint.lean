/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteAdjunctionFactorization

/-! # Finite projection of the supported diagonal as a divisor Chern adjunct
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- Finite projection identifies the pushed supported diagonal with the adjunct of
c1 of its actual divisor line. This does not decompose that line or use a trace. -/
theorem diagonalTrace_finiteDivisorAdjoint
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let V := p.restrictionS.F.mapDerivedCategory
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
        (a.hom ≫ p.Rc.R.map δ) ≫ p.sourceMap l E ≫
        (p.LS.projection n).app _ ≫ ev.map (p.varying.inv.app _) =
      (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
        ev.map (V.map
          ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
            ((p.model.coefficientPullback.derivedIso l E).hom ≫
              SpTowerClasses.firstChern l E p.chernX
                (SpTowerClasses.diagonalPic Y)))) := by
  obtain ⟨Φ, hcompleted, hgeometric⟩ :=
    diagonalTrace_finiteAdjunction_factorization l Y f p a n
  have hsurface := diagonalTrace_finiteCartierChern l Y hY D δ hδ
    p.chernX p.normalizedX p.finiteX p.restrictionX p.coefficientsX p.LX n
  have h := congrArg Φ hsurface
  rw [hcompleted δ, hgeometric
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
      (SpTowerClasses.diagonalPic Y))] at h
  exact h

end AlgebraicGeometry.ProEtale.DiagonalTrace
