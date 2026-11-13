/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceResultExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegrationSystems
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleFaithful

/-! # The completed projective-line trace

## Main declarations
- `diagonalTraceFirstModel` and `diagonalTraceSecondModel` specify both product projections.
- `DiagonalTrace.NormalizedSource` and `DiagonalTrace.SupportedSource` fix the supported source.
- `diagonalTower_trace` states the three completed traces and both integration identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u w v a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

open DiagonalTrace

set_option linter.unusedVariables false in
/-- The strict unit/section splitting defines the completed projective-line trace;
its finite reductions are the torsion traces and the two diagonal integrals are one. -/
theorem diagonalTower_trace (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ) :
    ∃ (tq : Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
      (t₁ : Result l (ULift.{u} (Padic l))
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
      (t₂ : Result l (ULift.{u} (Padic l))
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))),
      tq.model.model = Iso.refl (ProjectiveLine Y) ∧
      t₁.model.model = diagonalTraceFirstModel Y ∧
      t₂.model.model = diagonalTraceSecondModel Y ∧
      ∃ (a₁ : SupportedSource l Y
          (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₁.Rc)
        (a₂ : SupportedSource l Y
          (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₂.Rc),
        IsIntegration t₁.Rc.R a₁.hom t₁.trace δ ∧
        IsIntegration t₂.Rc.R a₂.hom t₂.trace δ := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) :=
    (map_natCast (ProjectiveLine Y ↘ Y).appTop.hom l) ▸
      hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hfirst : (diagonalTraceFirstModel Y).hom ≫
      (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) =
        pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) := by
    exact IsPullback.isoPullback_inv_fst _
  have hsecond : (diagonalTraceSecondModel Y).hom ≫
      (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) =
        pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) := by
    simp only [diagonalTraceSecondModel, Iso.trans_hom, Category.assoc, hfirst,
      pullbackSymmetry_hom_comp_fst]
  obtain ⟨tq, hq⟩ := exists_diagonalTraceResult l (ProjectiveLine Y ↘ Y)
    (Iso.refl _) (Category.id_comp _) hY
  obtain ⟨t₁, h₁⟩ := exists_diagonalTraceResult l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (diagonalTraceFirstModel Y) hfirst hP
  obtain ⟨t₂, h₂⟩ := exists_diagonalTraceResult l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (diagonalTraceSecondModel Y) hsecond hP
  obtain ⟨a₁, s₁, _, _⟩ := diagonalTrace_integrationSystems l Y hY D δ hδ
    _ (Or.inl rfl) t₁
  obtain ⟨a₂, s₂, _, _⟩ := diagonalTrace_integrationSystems l Y hY D δ hδ
    _ (Or.inr rfl) t₂
  refine ⟨tq, t₁, t₂, hq, h₁, h₂, a₁, a₂, ?_, ?_⟩
  · apply diagonalTrace_single_map_injective l (ProjectiveLine Y)
      (a₁.hom ≫ t₁.Rc.R.map δ ≫ t₁.trace) (𝟙 _)
    exact s₁.eq_id.trans ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map_id _).symm
  · apply diagonalTrace_single_map_injective l (ProjectiveLine Y)
      (a₂.hom ≫ t₂.Rc.R.map δ ≫ t₂.trace) (𝟙 _)
    exact s₂.eq_id.trans ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map_id _).symm

end AlgebraicGeometry.ProEtale
