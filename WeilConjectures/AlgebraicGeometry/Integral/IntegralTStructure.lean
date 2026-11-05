/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCanonicalTruncations
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # The bounded standard integral t-structure

Source: blueprint, smooth base change, order 1431; BBD 1.3.1--1.3.6
(blueprint: prop-weil-pbc-integral-tstructure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

/-- The actual integral category has the inherited triangulated structure.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: intrinsic completion is invariant under isomorphisms, shifts and triangles.
Refine the two finite stratifications and take common local models. Their cones remain
bounded complexes with adic-lisse finite-type terms; the finite coefficient categories
are abelian, and their finite-lisse cohomology is stable under kernels, cokernels and
extensions. Exact comparison inverse image transports the cone and its retained origins.
Their normalizations satisfy the quotient cocycle by functoriality. Zero satisfies all
three conditions. Thus the full subcategory is triangulated with inherited triangles. -/
@[instance] theorem pbcIntegralProperty_isTriangulated :
    ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := by
  exact (pbcIntegralUniformComplete_isTriangulated l E T hDim.out hInv.out).2

/-- Ambient canonical truncation induces the standard integral t-structure.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: pbcIntegralCanonicalTruncations_mem gives closure under both ambient truncations.
The ambient canonical truncation triangle has its two terms in the integral category,
so HasInducedTStructure.mk' supplies the required truncation triangles. Fullness gives
orthogonality, and the inherited shifts give the two shift axioms. -/
@[instance] theorem pbcIntegralProperty_hasInducedTStructure :
    ObjectProperty.HasInducedTStructure
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
      (pbcAmbientTStructure T l E) := by
  exact ObjectProperty.HasInducedTStructure.mk'
    (fun X hX m ↦ pbcIntegralCanonicalTruncations_mem T l E ⟨X, hX⟩ m)

set_option linter.unnecessarySimpa false in
/-- The inherited shifts are linear for the actual constant-section scalar action.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: the full inclusion is faithful and linear, its comparison with shift is induced
by the ambient shift, and the ambient derived shift is linear. Faithfulness tests the
scalar equation and gives it in the full subcategory. -/
@[instance] theorem pbcIntegralShift_isLinear (n : ℤ) :
    (shiftFunctor (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) n).Linear
      (PbcIntegralRing l E) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear (PbcIntegralRing l E) :=
    Functor.linear_of_iso (PbcIntegralRing l E) (P.ι.commShiftIso n).symm
  refine ⟨fun f r ↦ P.ι.map_injective ?_⟩
  simpa only [Functor.map_smul, Functor.comp_map] using
    (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul r f

end AlgebraicGeometry.Scheme
