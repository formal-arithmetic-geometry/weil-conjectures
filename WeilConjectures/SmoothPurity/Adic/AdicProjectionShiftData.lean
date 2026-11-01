/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.CompactSupportPbcTransport.CompactSupportProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization

/-! # Completed projection and trace-transpose definitions

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: def-pur-adic-projection-trace-data).

The projection is the proper counit mate followed by the open comparison, transported
by the actual quotient-completion units. All tensors below are the recorded completed
tensors. The first input is arbitrary in the full integral finite-Tor category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Exceptional
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : ConstructibleExceptionalCoefficients.RingSystem C.l C.Qbar D C.different (f := f))
  (c : Compactification f)

end Exceptional
end WeilConjectures
