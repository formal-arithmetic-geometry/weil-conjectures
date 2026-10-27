/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.TameInertiaScalarMateData


/-! # Derived scalar tensor on the finite continuous Koszul model

Source: paragraph (3) of the direct-image stability proof, finite-coordinate calculation
(blueprint: lem-sfb-tame-inertia-derived-tensor-computation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.TameInertiaScalarMate

open TameInertiaKoszul

variable (E Ω : Type u) [NormedField E] [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))

variable [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]

variable (p ℓ r : ℕ) [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [Context p r E] [Context p r Ω] [ScalarRestriction E p r Ω h]
  [RestrictionUniversal E p r Ω h]
  (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)


/-- The ordinary unbounded derived scalar tensor exists with its actual scalar unit,
and its comparison computes tensor on the finite Koszul complexes.

Source: Stacks Project, Tags 06YQ and 07A6; finite-free calculation in paragraph (3)
of the direct-image stability proof
(blueprint: lem-sfb-tame-inertia-derived-tensor-computation).

Proof: Transport the internal module categories to sectionwise module sheaves using
`InternalAbelianSheafModule.sectionModuleEquivalence`. Adjoint uniqueness identifies
ordinary scalar extension with the existing change-of-rings tensor and its actual
unit. Transport the universal derived pair and the normalized derived adjunction of
`sheafRingDerivedCoefficientAdjunction` back along these equivalences. Its unit identity
holds on every homotopy object by the fraction formula with identity denominators.
For each M, the fixed subspace N is finite dimensional, as a subspace of M. An E-basis
of N identifies its all-continuous coefficient sheaf with a finite power of C_E,
because the specified module topology makes the coordinate maps homeomorphisms.
Combining this with the subset coordinates identifies each Koszul term with a finite
free sheaf, including the empty power. Tensoring with such a sheaf is a finite direct
sum, hence exact. The terms vanish outside [0,r], so Tag 06YQ gives K-flatness.
The derived change-of-rings comparison on this K-flat complex is invertible.
All transports use the same quotient and Qh comparisons as in DerivedTensor. -/
theorem derived_tensor_computation :
    ∃ s : DerivedTensor E Ω h, ∀ M : Inputs E p ℓ r,
      IsIso (s.comparison.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (dE.koszul.obj M))) := by
  sorry

end Profinite.TameInertiaScalarMate
