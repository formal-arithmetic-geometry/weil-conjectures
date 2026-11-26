/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.Polynomial.Basic
import WeilConjectures.RingTheory.PolynomialGRingRegularComparison
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.PolynomialCompleteLocalFormalFibres
import WeilConjectures.RingTheory.RegularComposition

/-!
# A comparison local ring for polynomial formal fibres

For a maximal ideal `Q` of `R[x]` over a G-ring `R`, there is a flat local map from `R[x]_Q` to a
Noetherian local ring `B` such that `R[x]_Q → B̂` is regular.

## Implementation details

With `A = R_p`, the ring `B` is the localization of `Â[x]` at the prime over `Q`. The map
`R[x]_Q → B` is regular by the G-ring hypothesis, and `B → B̂` is regular by the complete-local
polynomial formal-fibre theorem. This gives only the bottom and right sides of the comparison
square; regularity of the completion of `R[x]_Q` still requires completing the comparison map and
faithfully flat descent.

## References

* [Stacks, Tag 07PV] (the completion square in the second paragraph of the proof)
-/

@[expose] public section

universe u

/-- At a maximal ideal of a polynomial ring over a G-ring, there is a flat local
comparison map into a Noetherian local ring whose composite with completion is regular. -/
theorem exists_polynomial_flat_local_regular_completion_comparison
    (R : Type u) [CommRing R] (hR : IsGRing R)
    (Q : Ideal (Polynomial R)) [Q.IsMaximal] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ φ : Localization.AtPrime Q →+* B,
        φ.Flat ∧
        (∀ x : Localization.AtPrime Q,
          x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
            φ x ∈ IsLocalRing.maximalIdeal B) ∧
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ).IsRegular := by
  obtain ⟨S, hS, hSN, hSL, hSC, Q', hQ', hQc, φ, hφ, hlocal⟩ :=
    exists_polynomial_regular_local_comparison R hR Q
  let := hS
  let := hSN
  let := hSL
  let := hSC
  let := hQ'
  let B := Localization.AtPrime Q'
  let A := Localization.AtPrime Q
  let C := AdicCompletion (IsLocalRing.maximalIdeal B) B
  let : Algebra A B := φ.toAlgebra
  let : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  have hB : IsNoetherianRing B := inferInstance
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have hc : (algebraMap B C).IsRegular :=
    Polynomial.isRegular_algebraMap_adicCompletion_localization S Q' hQc
  have hcomp : (algebraMap A C).IsRegular :=
    RingHom.IsRegular.comp_of_fiber_noetherian hφ hc
      (fun p _ ↦ Ideal.isNoetherianRing_fiber p)
  exact ⟨B, inferInstance, inferInstance, hB, φ, hφ.1, hlocal, hcomp⟩
