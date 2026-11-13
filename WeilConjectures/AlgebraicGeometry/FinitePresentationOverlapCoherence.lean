/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapChartEquations
import WeilConjectures.AlgebraicGeometry.OverlapComparisonRefinement
import WeilConjectures.AlgebraicGeometry.OverlapUniversalTestCoherence

/-! # Eventual identity and cocycle equations for lifted maps

## References

* Stacks Project, Tags 01ZR and 05N7
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private lemma overlapLimitMap_stage_comp {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec))
    {i j k : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (hij : i ≤ j) (hjk : j ≤ k) :
    overlapLimitMap R c f (hij.trans hjk) ≫ overlapStageMap R f hij hjk =
      overlapLimitMap R c f hij := by
  dsimp only [overlapLimitMap, overlapStageMap]
  rw [← baseChangeMap_comp]
  congr 1
  ext
  exact c.w (homOfLE hjk).op


/-- The specific lifted natural overlap maps become coherent at a later stage.
(Stacks, Tag 01ZR, Tag 05N7) -/
theorem exists_finitePresentation_overlap_eventual_coherence
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    (M : (pullback f (c.π.app (op i))).Modules) :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        Nonempty ((T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Comparison
          ((modulesPseudofunctor.toDescentData (V₀.pullback₁ p₀).f).obj M)) →
        ∃ (l : I) (hkl : k ≤ l),
          let q := overlapStageMap R f hij (hjk.trans hkl)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkl)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkl
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkl)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkl) a)
          let p := overlapLimitMap R c f (hij.trans (hjk.trans hkl))
          T'.Coherent ∧
            Nonempty ((T'.pull (p := p) (α := fun a ↦ a)
              (fun a ↦ V.pullbackHom_map p a)).Comparison
              ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M)) := by
  classical
  intro k hjk
  dsimp only
  intro T hT hcmp
  obtain ⟨ε⟩ := hcmp
  obtain ⟨l, hkl, sq, sq₃, hself, hcomp⟩ :=
    exists_finitePresentation_overlap_eventual_chart_equations R c hc i f j hij U
      N hN hNq k hjk T hT ε.coherent
  refine ⟨l, hkl, ?_, ?_⟩
  · generalize ht : T.pull
        (p := overlapStageMap R f (hij.trans hjk) hkl) (α := fun a ↦ a)
        (p' := overlapRefinementHom U (overlapStageMap R f hij hjk)
          (overlapStageMap R f hij (hjk.trans hkl))
          (overlapStageMap R f (hij.trans hjk) hkl)
          (overlapStageMap_comp R f hij hjk hkl))
        (fun a ↦ overlapRefinementHom_map U (overlapStageMap R f hij hjk)
          (overlapStageMap R f hij (hjk.trans hkl))
          (overlapStageMap R f (hij.trans hjk) hkl)
          (overlapStageMap_comp R f hij hjk hkl) a) = TT at hself hcomp ⊢
    exact coherent_of_universal_tests (F := modulesPseudofunctor) TT sq sq₃ hself hcomp
  · exact nonempty_overlap_comparison_refinement U (overlapStageMap R f hij hjk)
      (overlapStageMap R f hij (hjk.trans hkl))
      (overlapStageMap R f (hij.trans hjk) hkl)
      (overlapStageMap_comp R f hij hjk hkl)
      (overlapLimitMap R c f (hij.trans hjk))
      (overlapLimitMap R c f (hij.trans (hjk.trans hkl)))
      (overlapLimitMap_stage_comp R c f (hij.trans hjk) hkl) T M ⟨ε⟩

end AlgebraicGeometry
