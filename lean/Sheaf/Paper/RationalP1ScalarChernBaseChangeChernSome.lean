/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps
import Sheaf.Paper.RationalP1ScalarChernSomeRaw

/-! # Specialized coefficient cases for scalar Chern exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- The scalar exchange preserves the positive Chern generator equation in the
some coefficient case.

This is a strict coefficient specialization of the scalar Chern exchange component.
The proof first lifts the normalized completed Chern adjuncts, then transports their
components through realization and scalar extension. The coefficient-level exchange
mate and root-normalized Tate comparison identify the pulled-back q component with the
p2 component; the whole-system Chern normalization identifies those components with
`cq` and `c₂`. The remaining diagram chase is carried out at this concrete some coefficient.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-chern-some). -/
theorem scalar_chern_base_change_chern_some
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l (some E)).X
    let cq := scalarQChern l (some E) Y r a
    let c₂ := scalarP2Chern l (some E) Y r b
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map cq ≫ secondTraceExchange l (some E) k p hpl Y =
        (scalarUnitPullIso Λ Y).hom ≫ c₂ := by
  dsimp only
  unfold scalarQChern scalarP2Chern
  dsimp
  exact scalar_chern_base_change_chern_some_raw l E k p hpl Y δ family r a ha b hb

end AlgebraicGeometry.ProEtale.RationalP1
