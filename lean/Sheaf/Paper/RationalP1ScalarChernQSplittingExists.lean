/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps
import all Sheaf.Paper.DiagonalCompletedChernSplitting

/-! # A one-sided q Chern splitting existence statement

Source: diagonal-tower unit/Chern splitting and the first rational P1 triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- The q Chern arrow admits a complementary shifted line component.

Source: the normalized completed q splitting, followed by realization, scalar
extension, and the canonical q pushforward comparison (blueprint:
lem-sfb-rational-p1-scalar-q-splitting-existence).

Proof: transport the complementary component of `completed_chern_splitting` for
`r.tq` through `realize_splitting` and the finite, rational, and closure scalar
compatibilities. The endpoint normalizations identify the second component with
`scalarQChern`; composing its target with the canonical q comparison preserves
invertibility. This is exactly the geometric splitting step used by the
homological criterion, with the homology concentration and componentwise
isomorphism conclusions postponed to the parent theorem. -/
theorem scalar_q_chern_splitting_exists
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a) :
    ∃ v : ((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X Y) 0).obj (line l c Y)) ⟦(2 : ℤ)⟧ ⟶
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v (scalarQChern l c Y r a)) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
