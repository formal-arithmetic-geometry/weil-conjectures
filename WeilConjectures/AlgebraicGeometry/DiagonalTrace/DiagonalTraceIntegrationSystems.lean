/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
public import WeilConjectures.CategoryTheory.SixFunctors.SingleTowerEvaluationFaithful
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceLimitWitnessExistence

/-! # The system underlying a completed diagonal integral
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- A completed diagonal integral is the inverse limit of a degree-zero system
endomorphism whose evaluations are identities. This retains the single whole-system
map and its limit comparison, rather than inferring equality from derived evaluations. -/
theorem diagonalTrace_integrationSystems
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
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f) :
    ∃ a : SupportedSource l Y f t.Rc,
      ∃ s : SingleTowerLimitWitness (DiagonalMod l (ProjectiveLine Y))
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map
          (a.hom ≫ t.Rc.R.map δ ≫ t.trace)),
        s.tower = t.restrictionS.F.obj
          (SpTowerClasses.coefficient (ProjectiveLine Y)
            (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y))) ∧
        s.limitFunctor = t.LS.R := by
  obtain ⟨a⟩ := diagonalTrace_supportedSource_exists l Y f hf t
  obtain ⟨s, hs⟩ := diagonalTrace_limitWitness_exists l Y hY D δ hδ f hf t a
  exact ⟨a, s, hs⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
