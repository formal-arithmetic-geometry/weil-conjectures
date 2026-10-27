/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.SmoothPurityTowerChartData

/-! # Uniform level bounds give the ordinary tower domain

Source: blueprint latest, Local pairs, bounded-below strict-tower domain
(blueprint: lem-sp-level-bounds-tower-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Uniform finite-level bounds give the recorded domain for the actual ordinary tower.
The origins hypothesis concerns independent finite complexes and contains no tower claim.
Source: blueprint latest, Local pairs, and chart-admissibility proof steps 2--3
(blueprint: lem-sp-level-bounds-tower-domain).

Proof: exact evaluation commutes with homology. If i < a, all evaluations of H^i(C)
vanish. The ordinary tower sheaf has zero components, so is zero, proving C.IsGE a.
Transport C by the inverse of the section-preserving derived realization. Its evaluated
levels are naturally isomorphic to the original levels: the abelian realization changes
no section or restriction map. Transport finite constructibility, cohomology vanishing
and Tor amplitude across these isomorphisms. The same a,b,s,t therefore establish
spConstructibleTorTowers for every presentation D. For each n apply the given origins
assertion to the n-th level and its prescribed intervals. The etale witness is bounded
below; its exact comparison is bounded below too. Transport the fixed-scalar comparison
through the canonical intrinsic module equivalence to obtain Origin n C. This is a
separate witness for each n; no compatibility or normalized transitions are asserted. -/
theorem domain_of_level_bounds
    (base : SpTowerShriek.Base l E) (T : Scheme.{u}) [IsNoetherian T]
    (horig : origins l E T)
    (C : SpTowerShriek.D l E T) (a b s t : ℤ) (hab : a ≤ b) (hst : s ≤ t)
    (hC : bounds l E T C a b s t) : domain l E base T C := by sorry

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
