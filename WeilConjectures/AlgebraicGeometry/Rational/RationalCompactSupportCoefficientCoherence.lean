/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExtensionCompactSupportBaseChange

import WeilConjectures.AlgebraicGeometry.Cbc.CbcCompactSupportCoefficientFamilyExistence
import WeilConjectures.AlgebraicGeometry.Cbc.CbcCompletedPullCoefficientFamilyExistence
import WeilConjectures.AlgebraicGeometry.Cbc.CbcRationalExchangeStage
import WeilConjectures.AlgebraicGeometry.Cbc.CbcRationalExchangeCoefficientSquare

/-! # Coefficient coherence of the normalized compact-support exchange

Source: blueprint main-20261015, `sk-thm-sf-pf-field/thm-cbc-qbar.proof.md`,
opening scalar-extension paragraph; Stacks Tag 0E8I for the open tensor factor
(blueprint: lem-cbc-rational-compact-support-coefficient-coherence).

The compact-support comparisons are specified by the open-unit/proper-counit
mates. The completed pullback comparisons retain their completion units.
The exchange is the rationalization of the actual strict-tower construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

end AlgebraicGeometry.Scheme
