/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Over
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.BaseChangeProduct
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField

/-!
# Products of geometrically irreducible schemes over a field

Source: Stacks Project, Tags 038F and 054P; Tag 0B9I, proof of (1)
(blueprint: lem-sc-geometrically-irreducible-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fibre product of two geometrically irreducible schemes over a field is geometrically
irreducible for its structure map through the first projection. By `pullback.condition`, this
is also the structure map through the second projection.

Source: Stacks Project, Tags 038F and 054P; used in Tag 0B9I, proof of (1)
(blueprint: lem-sc-geometrically-irreducible-product).

Proof: fix a field extension `k'/k`. The canonical base-change/product identification
(lem-pc-base-change-product) identifies the base change of the product with the product of
`X` and `Y` after base change to `k'`. Both factors are geometrically irreducible over `k'`:
for every further extension `K/k'`, the iterated base-change identification
(def-pc-base-change) identifies their base changes with `X_K` and `Y_K`, which are irreducible
by the hypotheses (def-pc-geometrically-irreducible). Apply
lem-sc-irreducible-product-over-field over `k'` (Tag 038F). Transport irreducibility across
the canonical isomorphism. Since `k'/k` was arbitrary, the product is geometrically
irreducible. -/
theorem geometricallyIrreducible_pullback_over_field (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [GeometricallyIrreducible (X ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))] :
    GeometricallyIrreducible
      (pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))) := by
  sorry

end AlgebraicGeometry
