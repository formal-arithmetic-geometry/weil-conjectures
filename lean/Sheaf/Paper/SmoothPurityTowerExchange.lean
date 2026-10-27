/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData
public import Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData

/-! # Exchange invertibility for normalized coefficient towers

Source: blueprint operations proof (2b)
(blueprint: lem-sp-tower-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The complete exchange field for `Laws`, obtained by combining the finite-level
criterion with tower detection. This is strictly one field of the laws structure;
projection, localization, boundedness and detection are separate. Source: blueprint
operations proof (2b).

Proof: fix a coefficient index and use the retained origin to apply the finite
compact-support base-change theorem to its fixed-scalar antecedent. The witness
transport identity and StrictFiniteExchangeComparisons identify the realized map
with the finite exchange, up to the specified invertible comparisons. Cancel them
and transport along Origin.realization by naturality. StrictWordComparisons then
identifies evaluation of the tower exchange with this finite map, again up to
invertible comparisons. Finally b.calculus detects isomorphisms jointly. Empty
schemes and the zero complex satisfy the same cancellations. No witness transition
compatibility is needed (blueprint: lem-sp-tower-exchange-realization).
-/
theorem tower_exchange_laws (b : Base l E) (o : Operations l E b)
    (x : OpenExchange l E b o) (levels : ComparisonLevels l E b o)
    (coordinates : StrictFiniteCoordinates l E b)
    (_words : StrictWordComparisons l E b o x levels)
    (_finite : StrictFiniteExchangeComparisons l E b o levels coordinates) :
    ∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (sq : IsPullback h f' f g) (c : Compactification f)
      (C : DerivedCategory.Plus (S l E X)),
      (∀ n : ℕ, Origin l E b X n C.obj) →
      IsIso ((exchange l E b o x sq c).app C.obj) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
