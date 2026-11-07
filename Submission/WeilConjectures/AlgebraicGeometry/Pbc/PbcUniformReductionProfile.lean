/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Uniform reduction cohomology
Source: uniform triangulation supplement, steps 2 and 5.
(blueprint: def-weil-pbc-uniform-reduction-profile). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
open ProEtale

/-- Reduction followed by the exact change from function coefficients to constants.
Source: blueprint order 1250
(blueprint: def-weil-pbc-uniform-reduction-profile). -/
abbrev pbcConstantReduction (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcCompletedReduction T d n ⋙
    pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom

/-- One cohomological interval for all reductions, with intrinsic constructibility.
Source: blueprint triangulation supplement, steps 2 and 5
(blueprint: def-weil-pbc-uniform-reduction-profile). -/
def PbcUniformReductionProfile (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) : Prop :=
  ∃ a b : ℤ, ∀ n : ℕ,
    ((pbcConstantReduction T d n).obj K).IsGE a ∧
    ((pbcConstantReduction T d n).obj K).IsLE b ∧
    DerivedCategory.homologyProperty
      (@IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n) _
        (d.quotientFinite n)) ((pbcConstantReduction T d n).obj K)

end AlgebraicGeometry.Scheme
