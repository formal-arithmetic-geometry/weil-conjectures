/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.TameInertiaScalarMateData

/-! # Ordinary scalar extension of the finite continuous Koszul model

Source: paragraph (3) of the direct-image stability proof, finite-coordinate calculation
(blueprint: lem-sfb-tame-inertia-scalar-tensor-computation).
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
  (m : CoefficientMaps E p ℓ r Ω h dE dΩ)



/-- The ordinary scalar adjunct between the two finite Koszul complexes is invertible.

Source: finite-coordinate scalar calculation, paragraph (3) of the direct-image
stability proof (blueprint: lem-sfb-tame-inertia-scalar-tensor-computation).

Proof: Choose an E-basis of the finite-dimensional fixed subspace N. The specified
module topologies identify F tensor_E N with a finite product of F, for F=E,Omega.
Continuous sections commute with these finite products. Thus degree a has the finite
basis indexed by pairs (I,j), with I of cardinality a and j a basis index of N.
The ordinary scalar adjunct sends z tensor x to z times the coefficient inclusion
of x, by the ordinary unit and the balanced tensor universal property. In these
coordinates its inverse sends y to the finite sum of y_(I,j) tensor e_(I,j).
Balancing and the basis expansion give both inverse identities; these maps commute
with restrictions and descend through sheafification, so they are actual internal
module maps. The differential matrices have E entries, and the same alternating
signs on both sides; scalar multiplication commutes with them. The resulting inverse
in every degree makes the chain map an isomorphism. Empty coordinate sets and N=0
use empty sums, and r=0 is the single degree-zero calculation. -/
theorem scalar_tensor_computation (M : Inputs E p ℓ r) :
    IsIso (tensorMap E Ω h p ℓ r dE dΩ m M) := by
  sorry

end Profinite.TameInertiaScalarMate
