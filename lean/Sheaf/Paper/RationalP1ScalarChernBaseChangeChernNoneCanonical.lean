/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps

/-! The closure-coefficient Chern exchange for canonical normalized lifts. -/

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

/-- The geometric closure-coefficient exchange produces a normalized pair of
completed Chern lifts.  The lifts are existential here; their uniqueness is a
separate statement, so this is the concrete geometric exchange obligation
below the arbitrary-input theorem.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-chern-none) -/
theorem scalar_chern_base_change_chern_none_canonical
    (l : ℕ) [Fact l.Prime]
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
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤))) :
    ∃ a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧),
      CompletedChernNormalized l r.tq.toPresentation a ∧
    ∃ b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧),
      CompletedChernNormalized l r.t₂.toPresentation b ∧
      (let Λ := (coefficient l none).X
       let cq := scalarQChern l none Y r a
       let c₂ := scalarP2Chern l none Y r b
       let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
       F.map cq ≫ secondTraceExchange l none k p hpl Y =
           (scalarUnitPullIso Λ Y).hom ≫ c₂) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
