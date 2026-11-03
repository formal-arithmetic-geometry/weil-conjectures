/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
public import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement

/-! # Exceptional base change in current integral coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-tower.md
and its proof, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).

The tower operations are the recorded ordinary derived varying-ring operations.
The integral category is the current bounded constructible full subcategory of
internal modules over the pulled-back condensed ring. No completeness condition
is imposed in its definition. A natural index n represents exponent n+1.
The auxiliary records only specify the canonical reduction, proper/open and
adjunction comparisons needed to state clause (3); all are outputs of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (ex : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o ex)

variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

/-- Geometric reduction data for clause (3), before transporting any exchange or mate.
Source: proof (3), reduction formulas (blueprint: def-sp-tower-exceptional-integral-coordinates).
-/
structure IntegralData where
  rX : Vertex l E b o q ex laws X
  rY : Vertex l E b o q ex laws Y
  rX' : Vertex l E b o q ex laws X'
  rY' : Vertex l E b o q ex laws Y'
  geometry : ReductionGeometry l E (presentation l E b o q ex laws)
  openIso : OpenReductionIsIso l E (presentation l E b o q ex laws) geometry
  support : Support l E b o q ex laws c rX rY geometry openIso
    a.support_closed a.right a.adjunction
  support' : Support l E b o q ex laws (c.ofIsPullback sq) rX' rY' geometry openIso
    a.support_closed' a.right' a.adjunction'
  pull : Pull l E b o q ex laws u' rX' rX geometry a.pull_closed
  pull' : Pull l E b o q ex laws v rY' rY geometry a.pull_closed'

end AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
