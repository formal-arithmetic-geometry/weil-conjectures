/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.RationalTensorRealization.RationalRealizationTensorComparisonStructures

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ContinuousRational
namespace WeilConjectures.RationalTensorRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l)
  (X : ContinuousRational.Base.{u} l) (E : Padic.FiniteCoefficientFields l Ω)
  [CompactSpace X.scheme] [QuasiSeparatedSpace X.scheme]

end WeilConjectures.RationalTensorRealization
