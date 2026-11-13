/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage
import WeilConjectures.AlgebraicGeometry.OverlapPairRefinementPersistence

/-! # Descent of a map on one pairwise overlap

## References

* Stacks Project, Tags 01ZR and 05N7
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

/-- The limit map factors through every later stage. -/
lemma overlapLimitMap_stage_comp {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec))
    {i j k : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (hij : i ≤ j) (hjk : j ≤ k) :
    overlapLimitMap R c f (hij.trans hjk) ≫ overlapStageMap R f hij hjk =
      overlapLimitMap R c f hij := by
  dsimp only [overlapLimitMap, overlapStageMap]
  rw [← baseChangeMap_comp]
  congr 1
  ext
  simpa using c.w (homOfLE hjk).op


-- Preserve the original unused existential binder in the public signature.
set_option linter.unusedVariables false in
/-- Descend the conjugated transition on one pairwise overlap, with persistence at later stages.
(Stacks, Tag 01ZR, Tag 05N7) -/
theorem exists_finitePresentation_overlap_pair_map_lifting
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀) :
    ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hjl : j ≤ l), k ≤ l →
      let q := overlapStageMap R f hij hjl
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjl)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (overlapLimitMap_stage_comp R c f hij hjl) N M e
      ∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
          (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
        overlapPairSquare V A p D ε a b φ := by
  obtain ⟨k, hjk, hk⟩ := exists_overlap_pair_map_at_stage
    R c hc i f j hij U N hN hNq M e a b
  refine ⟨k, hjk, ?_⟩
  intro l hjl hkl
  have hs := overlap_pair_map_refinement_persistence U
    (overlapStageMap R f hij hjk) (overlapStageMap R f hij hjl)
    (overlapStageMap R f (hij.trans hjk) hkl)
    (overlapStageMap_comp R f hij hjk hkl)
    (overlapLimitMap R c f (hij.trans hjk))
    (overlapLimitMap R c f (hij.trans hjl)) (overlapLimitMap R c f hij)
    (overlapLimitMap_stage_comp R c f hij hjk)
    (overlapLimitMap_stage_comp R c f hij hjl)
    (overlapLimitMap_stage_comp R c f (hij.trans hjk) hkl) N M e a b
  exact hs hk

end AlgebraicGeometry
