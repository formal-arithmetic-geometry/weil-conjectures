/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.CompletionMateComparison
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.StrictPerfectCoefficientPackage
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

/-! # Perfect quotient coefficient projections on arbitrary small sites -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} {A : Type u} [CommRing A] {I : Ideal A}

/-- Perfect quotient coefficients make the specified finite and strict-tower
coefficient exchange projections invertible for every ambient object.

Source: Stacks, Cohomology on Sites, Tags 0B54, 0B56, 0941; completed projection
coherence, proof Steps 6 and 7
(blueprint: lem-pur-perfect-quotient-projection).

Proof: Represent each A/I^(n+1) by a bounded complex of finite projective A-modules.
The constant-module functor is exact, so this gives the same coefficient sheaf in
its derived category, retaining every finite-free retraction. Compute the direct
image on a K-injective representative. The finite-projective totalization
projection theorem gives an inverse to the counit-tensor projection with this
coefficient complex. Its representative formula identifies it with the underlying
restriction of finiteProjection, using the normalized scalar/pullback comparison
and normalized finite adjunction. Restriction of quotient coefficients is exact
and conservative on cohomology, so finiteProjection is invertible. Evaluate the
strict-tower coefficient exchange at each index. The specified evaluation and
scalar-restriction comparisons identify it with the same finite projection.
Thus its cone is acyclic at every index. Cohomology of strict towers is computed
componentwise, so the whole cone is zero and towerProjection is invertible.
The whole-tower map was constructed before evaluating, so no assertion of
faithfulness of evaluation on morphisms is used. The zero quotient is included:
its derived module category is zero and the same cone argument applies. -/
theorem perfectQuotientProjection (f : Morphism Y X) (h : PerfectQuotients A I) :
    (∀ H : X.derived A, IsIso (f.towerProjection A I H)) ∧
      ∀ (n : ℕ) (H : X.derived A), IsIso (f.finiteProjection A I n H) := by
  sorry

end CategoryTheory.AdicSites
