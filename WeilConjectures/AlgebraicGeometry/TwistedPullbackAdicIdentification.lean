/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackAdicAgreement

/-! # Identification of the integral twisted scalar comparison

Source: purity transport, agreement with ordinary adic scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (B : FiniteFieldDatum.{u}) (C : B.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (Y ↘ Spec (.of B.k))]
  [∀ x : X, Invertible (C.l : X.residueField x)]
  [∀ y : Y, Invertible (C.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The specified integral tensor comparison becomes the ordinary adic source
comparison after the actual completion maps. Source: purity-transport scalar-square
calculation, Step 11; the definition of the source comparison in adic scalar
naturality. (blueprint: lem-pur-twisted-pullback-adic-identification).

Proof: Work on a flat K-flat representative for the finite-Tor object K. Expand
integralA into integralQ and the completed pullback comparison. Remove completed
tensor using tensorToTermwiseOnGood; ShiftData.beta_normalization fixes this map
on the chosen representative. The canonical scalar completion isomorphism chi
identifies strict-system scalar extension with ordinary scalar extension. Its
naturality cancels the intermediate chi on the pulled-back object. The remaining
factors are, in order, ordinary scalar shift, scalar change of the termwise Tate
line, and ordinary scalar/pullback balancing, followed by inverse chi on K. This
is the defining sourceScalarComponent, with exactly the two shifted beta factors
in AdicAgreement. These equalities concern the whole normalized system and hence
descend through the derived category. Finally the localization functor preserves
the two composites and the specified shifts, identifying a with the localization
of integralA. No purity isomorphism or exceptional comparison is used. -/
theorem twistedPullbackAdicIdentification
    (hC : AdicPurityScalarNaturality.ScalarClosed B C X Y)
    (s : ∀ R : Fields C.l C.Qbar, ShiftData C.l R.val X d) :
    AdicAgreement B C f d hC s := by sorry

end WeilConjectures.TwistedPullbackScalars
