/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.Algebra.FinitePresentationColimit

/-! # A step of persistent pairwise overlap lifting

Source: Stacks Project, Tag 01ZR, first proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

/-- Lift the conjugated map on a fixed pair at one stage, without any assertion
about later stages.
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 05N7 (2), (3).
(blueprint: lem-pc-fp-overlap-pair-single-stage).

Proof: The ambient stage is quasi-separated, so the intersection of its two
chosen affine opens is quasi-compact. Cover this intersection at stage j by
finitely many affine opens, and each pairwise intersection of this refinement
by finitely many affine opens. Stage transition maps are affine, so the inverse
images of these affine opens remain affine and cover each later overlap.
Base change of the limit cone is a limit cone for each such affine system;
Spec and global sections identify its coordinate ring with the directed colimit
of the stage rings. Restrict the conjugated transition of M to these affines.
The restricted N a and N b remain finitely presented and quasi-coherent, and
quasi-coherent pullback is scalar extension. Tag 05N7 (2) lifts the finitely many
maps; (3) makes their restrictions agree on the refinement intersections at a
common later stage.
Glue by the sheaf condition. The glued limit map is the prescribed conjugated
transition because this is true on the affine refinement. Transport along the
canonical iterated chart maps and pullback composition comparisons gives the
stated square at this stage. This does not establish persistence. An empty
overlap has its unique map; the tail above j is nonempty, and passing to its
partial-order quotient handles a preorder. -/
theorem exists_overlap_pair_map_at_stage
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
    ∃ (k : I) (hjk : j ≤ k),
      let q := overlapStageMap R f hij hjk
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjk)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (by
          dsimp only [p, q, overlapLimitMap, overlapStageMap]
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op) N M e
      ∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
          (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
        overlapPairSquare V A p D ε a b φ := by sorry


end AlgebraicGeometry
