/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap

/-! # Reflection through the specified completed pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Completed pullback is the reflection of ordinary pullback on every ambient input.
Source: Stacks Tag 099N, proof of (2) and (5), together with Tag 099M;
blueprint completed-exchange coherence, proof steps 1 and 4.
(blueprint: lem-weil-pbc-completed-pullback-reflection).
Proof: take a flat-term K-flat representative of K and form its whole strict quotient
sequence. Tensor balancing identifies its pullback with the quotient sequence of the
ordinary pullback, including all transitions and the augmentation. The Koszul/quotient
comparison identifies its derived inverse limit with the completion reflector. The
map ordinaryToCompleted is the adjunct of that augmentation, so the comparison carries
its unit to the actual reflector unit. The reflector has complete output and gives
bijective precomposition into every complete object. Restriction to constant
coefficients and the complete-category equivalence transport these assertions back
to the completed coefficient category; this uses the unit-preserving comparison,
not an inference from levelwise equalities. The representative K need not be complete. -/
theorem AdicCoefficientDatum.completedPull_reflection {U V : Scheme.{t}} (u : U ⟶ V) :
    (∀ K : d.derived V, d.TowerComplete U ((d.completedPull u).obj K)) ∧
      ∀ (K : d.derived V) (L : d.derived U), d.TowerComplete U L →
        Function.Bijective (fun a : (d.completedPull u).obj K ⟶ L ↦
          d.ordinaryToCompleted u K ≫ a) := by
  sorry

end AlgebraicGeometry.Scheme
