/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps

/-! # Raw finite coefficient transport for the positive Chern exchange -/

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

/-- The explicit finite coefficient transport equation underlying the positive Chern
exchange.  This is the raw equation before packaging the two composites as
`scalarQChern` and `scalarP2Chern`.
Source: the coefficient-level exchange mate and the finite intermediate-field leg
of the diagonal tower.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-chern-some-raw). -/
theorem scalar_chern_base_change_chern_some_raw
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
    let q := extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E)
      (ProjectiveLine Y ↘ Y) ((family.toRational E).units Y) (family.toRational E).lineP
      (family.integral E).Rq (family.rational E).Rq (family.toRational E).q.square
      (extendScalarChern (integralMap l E) (ProjectiveLine Y ↘ Y)
        ((family.toIntegral E).units Y) (family.toIntegral E).lineP family.zl.Rq
        (family.integral E).Rq (family.toIntegral E).q.square
        (realizeScalarChern l (ProjectiveLine Y ↘ Y) r.eP r.eY r.tq.Rc
          family.zl.Rq r.q_square a)) ≫
      (eqToIso (family.rational E).q_canonical).hom.app _
    let p₂ := extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E)
      (secondProjection Y) ((family.toRational E).units (ProjectiveLine Y))
      (family.toRational E).lineW (family.integral E).R₂ (family.rational E).R₂
      (family.toRational E).p₂.square
      (extendScalarChern (integralMap l E) (secondProjection Y)
        ((family.toIntegral E).units (ProjectiveLine Y)) (family.toIntegral E).lineW
        family.zl.R₂ (family.integral E).R₂ (family.toIntegral E).p₂.square
        (realizeScalarChern l (secondProjection Y) r.eW r.eP r.t₂.Rc
          family.zl.R₂ r.p₂_square b)) ≫
      (secondDiagramPushIso _ Y _ (family.rational E)).hom.app _
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map q ≫
        secondTraceExchange l (some E) k p hpl Y =
      (scalarUnitPullIso Λ Y).hom ≫ p₂ := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
