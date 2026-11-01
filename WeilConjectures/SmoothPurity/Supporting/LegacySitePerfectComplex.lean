/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-!
# Compatibility predicates for the former coefficient model

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-pf-reduction`,
order 1881. These declarations retain their original meanings for existing consumers.
They do not define perfectness for condensed coefficients.
(blueprint: def-weil-legacy-site-perfect-compatibility).

## Main definitions

- `IsFiniteCoefficientSitePerfect`
- `IsIntegralCoefficientSitePerfect`
- `IsRationalCoefficientSitePerfect`
- `IsAlgebraicallyClosedCoefficientSitePerfect`
-/

@[expose] public section

set_option autoImplicit false

universe d t u v

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
end WeilConjectures

namespace WeilConjectures

/-- Abelian sheafification on the actual pro-etale slice, at the coefficient size.
Source: Stacks Tag 03DA (blueprint: def-weil-site-perfect-complex). -/
noncomputable instance sitePerfectOverAbSheafify (Y : AlgebraicGeometry.Scheme.{t})
    (U : Y.ProEt) :
    HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology Y).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion on that same small model of the slice.
Source: Stacks Tag 03DA (blueprint: def-weil-site-perfect-complex). -/
noncomputable instance sitePerfectOverAbLocallyBijective (Y : AlgebraicGeometry.Scheme.{t})
    (U : Y.ProEt) :
    ((AlgebraicGeometry.Scheme.ProEt.topology Y).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Site-perfectness at the finite coefficient stage uses an actual covering sieve
and bounded finite-projective models of module sheaves on its members. The exponent
is `n + 1`, so every positive finite level is included.
Source: Weil blueprint, order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsFiniteCoefficientSitePerfect (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (K : @DerivedCategory (SheafOfModules.{max u (t + 1)}
      (integralCoefficientSheaf l E Y n)) _ _ (HasDerivedCategory.standard _)) : Prop :=
  letI := integralCoefficientAbSheafify.{t, u} Y
  letI := integralCoefficientAbLocallyBijective.{t, u} Y
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (integralCoefficientSheaf l E Y n))
  @SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{t + 1, t, max u (t + 1)}
    _ _ _ (integralCoefficientAbSheafify.{t, u} Y)
    (fun U ↦ sitePerfectOverAbSheafify.{t, u} Y U)
    (fun U ↦ sitePerfectOverAbLocallyBijective.{t, u} Y U)
    (integralCoefficientAbLocallyBijective.{t, u} Y)
    (integralCoefficientCommRingSheaf l E Y n) (HasDerivedCategory.standard _) K

end WeilConjectures
