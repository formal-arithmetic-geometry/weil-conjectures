/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # Exact coefficient restriction preserves intrinsic completeness.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (W : Scheme.{u})

/-- Exact coefficient restriction preserves intrinsic completeness.
Source: Stacks Project, Tags 099B and 0A0E; the restriction and unit-power argument
of lem-weil-pbc-finite-free-completion-transport, step 2.
(blueprint: lem-pbc-scalar-restriction-complete).

Proof: identify the actual completed coefficient rings with their published
presentations by pbcCompletedComparison, retaining each finite quotient map.
The source uniformizer maps to a unit times a positive power of the target
uniformizer. Their powers are cofinal, so target-uniformizer completeness implies
completeness for the image of the source uniformizer, by the unit-power Cech/Koszul
criterion. Exact restriction carries this augmented Koszul computation to the
source ring: scalar restriction preserves the products and cones in the local
completion complex, and its scalar action on each differential is multiplication
by that image. It also detects the acyclicity of the corresponding Cech Hom
complexes. Consequently the restricted object is complete for the source
uniformizer. The comparison of intrinsic completeness with this local criterion
and transport back along pbcCompletedComparison give the stated predicate. This
argument uses no scalar/completion isomorphism and no constructibility assumption. -/
theorem pbcScalarRestrictionComplete (K : PbcCompletedDerived W (pbcIntegralDatum l F))
    (hK : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F) K) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W)).obj K) := by sorry

end AlgebraicGeometry.Scheme
