/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionCoefficientSupport

/-! # The genuine integral support tower

Source: the native-coefficient refinement of Step 3 in the current blueprint
`part-duality-trace-formula/sec-smooth-purity/sec-the-trace-map-of-affine-space/
sk-prop-an/thm-pur-localized-top-chern.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.PurityFiniteSetting

/-- The integral support object is the genuine derived limit of finite quotients.
Source: the integral coefficient comparison, the locally free twist theorem,
and the support-limits theorem, Steps 4--5 of
`lem-pur-zero-section-bottom-coefficients`.
Proof: construct the quotient cone from the actual maps from Z_l to
ZMod(ell^(n+1)). The integral coefficient comparison identifies its ordinary
limit with the continuous integral coefficient sheaf. Its surjective quotient
transitions identify the degree-zero object with the derived limit. The signed
Tate line of rank r is finite locally free, hence its tensor functor preserves
products and the Roos triangle. The root-normalized finite comparisons identify
the tensor terms with the prescribed finite signed lines, compatibly with the
quotient transitions. Shift by 2r and apply the actual integral support functor,
a triangulated right adjoint preserving products. To identify the terms, regard
coefficient restriction as the direct image of the identity ringed topos. Derived
pushforward composition identifies its two composites with ordinary open direct
image, including their units. Exact restriction then identifies the localization
fibers defining closed support. Thus the image terms are exactly the fixed
integral objects `zeroIntegralSupportTerms V n`, and the transported Roos triangle
gives the conclusion. No nonflat restriction functor is claimed to preserve
K-injectives, and no varying-category model is substituted for the integral one.
(blueprint: lem-pur-zero-native-integral-limit). -/
theorem nativeZeroSupport_integral_limit
    {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) :
    ∃ hprod : HasProduct (zeroIntegralSupportTerms V),
      letI := hprod
      ∃ f : ∀ n, zeroIntegralSupportTerms V (n + 1) ⟶ zeroIntegralSupportTerms V n,
        IsDerivedLimit f (nativeZeroSupport V .integers) := by
  sorry

end WeilConjectures.PurityFiniteSetting
