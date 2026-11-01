/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.PbcDescentFunctors
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportExchangeModel
import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportExchangeModelExists
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-!
# Compact-support base change with algebraically closed l-adic coefficients

Source: Weil conjectures blueprint main-20261015, six-functors basics,
`sk-thm-sf-pf-field/thm-cbc-qbar`, order 1992 (blueprint: thm-cbc-qbar).

The finite-stage endpoints are fixed by their composites with integral localization,
and the exchange components by the specified completed compact-support exchange.
The conclusion includes both the overfield representative and independence relative
to an isomorphism from a representing pair to the fixed input object.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Limits.limit
  pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek completedCompactSupportExchange
  pbcFiniteField pbcScalarExtension pbcScalarAssociator
  ScalarLocalization.category ScalarLocalization.preadditive
  StageSystem.Morphism.descNatTrans

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Scheme
