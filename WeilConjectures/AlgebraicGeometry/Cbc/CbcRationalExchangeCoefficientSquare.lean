/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
import WeilConjectures.AlgebraicGeometry.Cbc.CbcProperCoefficientSquare
import WeilConjectures.AlgebraicGeometry.Cbc.CbcOpenCoefficientSquare
import WeilConjectures.AlgebraicGeometry.Cbc.CbcIntegralNormalizedCoefficientSquare
import WeilConjectures.AlgebraicGeometry.Cbc.CbcLocalizedCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-! # The rational exchange coefficient square

Source: current blueprint, coefficient coherence of units, counits and mates.
(blueprint: lem-cbc-rational-exchange-coefficient-square)
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

/-- The normalized stage exchanges satisfy the coefficient square.
The stage maps are supplied; this asserts only their compatibility with beta.

Source: current blueprint, coefficient coherence of units and counits;
parent coefficient-coherence proof, steps 5--10, 15--16.
(blueprint: lem-cbc-rational-exchange-coefficient-square).

Proof: first work integrally with ordinary coefficient tensor. The inverse
beta of H is the open-unit mate followed by the proper counit-tensor map;
that of P is fixed by its ordinary balancing and completion-unit equation.
For the open square, the two ordinary composites send a summand tensor
(i_alpha x) tensor s to the same pulled-back summand with x tensor s.
Pass to completions by precomposing with the completion unit. Tensor
preserves completeness by finite freeness, and reflection uniqueness makes
the two completed composites equal. For the proper square, the strict tower
exchange is the projection-formula realization of the ambient adjunction
mate. Restriction to the ramified arithmetic subsequence retains the whole
tower and its quotient augmentations. Compare the two ambient maps by
transposition under the larger-ring pullback/direct-image adjunction.
The counit-tensor and ordinary balancing formulas give identical transposes.
Reflection uniqueness then gives the completed proper coefficient square.
Paste these open and proper squares in the order defining
completedCompactSupportExchange: proper exchange, then proper pushforward
of open exchange. Naturality moves the open scalar map across the proper
exchange; the proper square replaces its initial factors; the open square
replaces the factors inside proper pushforward. Naturality of the proper
scalar comparison collects the surviving maps into the composite beta
comparisons. Localize the resulting equality. The beta fields of the four
families identify these comparisons, with the inverse endpoint conjugations
cancelling. The supplied component specifications identify tau with these
localized integral exchanges on every integral representative. Every raw
rational object is such a representative, so the displayed equality follows
for all objects. This uses no invertibility of the exchange itself. -/
theorem cbcRationalExchange_coefficientSquare
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (H : CbcCompactSupportCoefficientFamily l Ω c)
    (H' : CbcCompactSupportCoefficientFamily l Ω c')
    (P : CbcCompletedPullCoefficientFamily l Ω g)
    (P' : CbcCompletedPullCoefficientFamily l Ω g')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω, (H.family.base.Φ E ⋙ P.family.base.Φ E) ⟶
        (P'.family.base.Φ E ⋙ H'.family.base.Φ E))
    (hτ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      ∀ (K : pbcIntegralStage l Ω X E)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g ⋙
            (pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj))
      (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        (((pbcStageDatum.{u} l Ω E).completedPull g' ⋙
          cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c'.i c'.isOpenImmersion ⋙
            (pbcStageDatum.{u} l Ω E).push c'.g).obj K.obj)),
      HEq ((τ E).app ((pbcStageLocalization l Ω X E).obj K))
        ((pbcStageLocalization l Ω Y' E).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
              c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩))))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcStageCategory l Ω X E) :
    ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((τ E).app K) ≫
        ((P'.family.base.comp H'.family.base).β h).hom.app K =
      ((H.family.base.comp P.family.base).β h).hom.app K ≫
        (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K) := by
  apply cbcLocalizedCoefficientSquare l Ω c c' gbar properSquare openSquare H H' P P' τ hτ
  intro E F h K
  exact cbcIntegralNormalizedCoefficientSquare l Ω c c' gbar
    properSquare openSquare H H' P P' τ hτ h K

end AlgebraicGeometry.Scheme
