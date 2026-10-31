/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerFiniteLevelData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerEvaluationLevelData

/-! # Finite levels of a normalized smooth tower adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Finite exceptional adjunctions and their coefficient-mate equations for an already
constructed smooth tower adjunction with normalized chart counits.
Source: blueprint det-sp-tower-gluing, Levels
(blueprint: lem-route-tower-chart-adjunction-levels).

Proof:
1. `finiteLevelData_exists` gives, at every level, finite compact-support preservation, a finite
exceptional right adjoint with its adjunction and realization, scalar preservation on X and Y,
the invertible compact-support coefficient comparisons and the invertible coefficient mates
(reduction-exceptional, reduction-direct-image).
2. `evaluationLevelData_exists`, applied to these finite data and the supplied charts, gives the
normalized evaluations, the comparisons of the evaluated tower right adjoint with the finite
right adjoints, their counit and unit equations and the reduction equation through
`coefficientMate`.
3. The fields of `Levels` are exactly the fields of the two records; bundle them. -/
theorem tower_chart_adjunction_levels
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G)
    (charts : Charts l E b o q k X Y
      ⟨inferInstance, inferInstance, inferInstance⟩ f d
      (CondensedRing.compactificationOverField f) hF G adj) :
    Nonempty (Levels l E b o q (CondensedRing.compactificationOverField f) hF G adj) := by
  obtain ⟨finite⟩ := finiteLevelData_exists l E b o q pchar k hne X Y f d hF
  obtain ⟨evaluated⟩ :=
    evaluationLevelData_exists l E b o q pchar k hne X Y f d hF G adj charts finite
  refine ⟨{
    finite_closed := finite.finite_closed
    right := finite.right
    adjunction := finite.adjunction
    realization := finite.realization
    support_evaluation := evaluated.support_evaluation
    comparison := evaluated.comparison
    counit := evaluated.counit
    unit := evaluated.unit
    scalarX := finite.scalarX
    scalarY := finite.scalarY
    direct_image_iso := finite.direct_image_iso
    coefficient_iso := finite.coefficient_iso
    reduction := evaluated.reduction
  }⟩

end AlgebraicGeometry.ProEtale.SpTowerGluing
