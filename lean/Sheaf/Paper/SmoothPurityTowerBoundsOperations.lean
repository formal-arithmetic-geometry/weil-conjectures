/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.SmoothPurityTowerChartData

/-! # Separate uniform intervals under elementary tower operations

Source: blueprint latest, Local pairs and Uniformity
(blueprint: lem-sp-elementary-tower-bounds).
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

/-- Inverse image and tensor with any specified strict Tate tower preserve both
intervals; a cochain shift subtracts its index from all four endpoints.
Source: blueprint latest, Local pairs and Uniformity, chart-admissibility steps 4--6
(blueprint: lem-sp-elementary-tower-bounds).

Proof: evaluate the actual ordinary inverse image using geometry.pullEvaluation.
Choose an etale bounded constructible finite-Tor origin at each level. Exact etale
inverse image preserves its cohomological interval. A bounded flat constructible model
in the specified Tor interval pulls back to a model with the same support and flat
terms; comparison pullback identifies its realization with the pro-etale inverse image.
This proves the first clause, without a compatibility condition on the origins.
For the second, rootTower_finite_tensor and the normalized Kummer comparison identify
each finite twist with the comparison pullback of the etale Tate line. Since ell is
invertible in characteristic p, that line and all its nonnegative powers are locally
free of rank one, including exponent zero. Tensor is therefore exact, preserves
constructibility and both intervals, and computes the ordinary derived tensor.
The prescribed level and transition fields of Twists identify these finite operations
with evaluation of the actual tower tensor; no new tower is chosen. The third clause
uses evaluation's shift comparison and H^i(C[j]) = H^(i+j)(C). The same identity after
tensoring a degree-zero test module proves the shifted Tor interval. Constructibility
and boundedness are preserved under reindexing degrees. -/
theorem elementary_tower_bounds
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (hlp : l ≠ p)
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base) :
    (∀ (X Y : Over (Spec (.of k))) [IsNoetherian X.left] [IsNoetherian Y.left]
      (f : X ⟶ Y) (C : SpTowerShriek.D l E Y.left) (a b s t : ℤ),
      bounds l E Y.left C a b s t →
      bounds l E X.left ((SpTowerShriek.pull l E base (ops.geometry f.left)).obj C)
        a b s t) ∧
    (∀ (T : Over (Spec (.of k))) [IsNoetherian T.left] (w : Twists l E T.left)
      (C : SpTowerShriek.D l E T.left) (r : ℕ) (a b s t : ℤ),
      bounds l E T.left C a b s t →
      bounds l E T.left (twist l E base w C r) a b s t) ∧
    (∀ (T : Scheme.{u}) (C : SpTowerShriek.D l E T) (j a b s t : ℤ),
      bounds l E T C a b s t →
      bounds l E T (C⟦j⟧) (a - j) (b - j) (s - j) (t - j)) := by sorry

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
