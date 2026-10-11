/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Sheaf.AlgebraicGeometry.Dimension

/-!
# Regularity, Noetherianity and dimension of the projective line

Source: Stacks Project, Schemes, Example 01JE (`schemes-example-projective-line`),
with the standard polynomial-ring regularity and dimension assertions
(blueprint: lem-sc-p1-regular-dimension-one).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

/-- Over any field, the projective line is quasi-compact and locally Noetherian,
regular, and has dimension one. Regularity is the affine-neighbourhood condition of
`def-weil-regular-scheme`; `IsRegularRing` includes Noetherianity of the coordinate ring.
Source: Stacks Project, Example 01JE, and Algebra, Tags 00OQ and 00KG
(blueprint: lem-sc-p1-regular-dimension-one).

Proof:
1. The standard affine cover of `def-sc-p1-standard` consists of two spectra of polynomial
   rings in one variable. Each is quasi-compact by
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` (iii); a finite union of
   quasi-compact opens is quasi-compact. Their rings are Noetherian by
   `lem-sc-p1-polynomial-noetherian`, giving local Noetherianity by `pqf-def-locnoeth`.
2. Each point lies in one of these charts, whose coordinate ring is regular by
   `lem-sc-p1-polynomial-regular`. This gives the affine neighbourhood required by
   `def-weil-regular-scheme`.
3. By `lem-weil-pbc-affine-open-stalk-localization`, the stalk at a chart point is the
   localization of its coordinate ring at the corresponding prime. Its dimension equals
   the prime's height by `lem-weil-pbc-localization-dimension-chains-below-prime`, bounded
   by the ring dimension by `lem-pc-ring-dimension-supremum-heights`. The chart dimension
   is one by `lem-sc-p1-polynomial-dimension-one`. At the prime `(t)` the strict chain
   `(0) < (t)` gives stalk dimension at least one. Taking the supremum of stalk dimensions
   as in `def-pc-dimension` therefore gives dimension exactly one.
4. Assemble quasi-compactness and local Noetherianity (the Noetherian-scheme clauses),
   affine-neighbourhood regularity, and dimension one. -/
theorem noetherian_regular_dim_one (k : Type u) [Field k] :
    let X := ProjectiveLine (Spec (.of k))
    CompactSpace X ∧ IsLocallyNoetherian X ∧
      (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)) ∧
      X.dim = 1 := by
  sorry

end AlgebraicGeometry.ProjectiveLine
