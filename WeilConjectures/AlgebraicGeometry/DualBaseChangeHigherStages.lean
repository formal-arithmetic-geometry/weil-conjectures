/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualBaseChangeFiniteStage
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum

/-! Higher-stage dual base change coherence. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w a b c d a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ i₁ j₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures

/-- Higher-stage dual base change: for the integral, rational and common-stage operations,
the recorded compact-support exchanges (`dualBaseChangeHigherExchange`) induce dual
base-change stages.
Source: blueprint, sec-six-functors/sk-thm-sf-compatibility, proof of
thm-sf-dual-base-change, Steps 1-5, applied to each of the three higher stages.

Proof (the five steps of the parent node, separately for each of the three stages):

1. Write A = Lg^* Rf_!, B = Rf'_! Lg'^*, R = Rf^! Rg_* and T = Rg'_* Rf'^!.
Restrict the four A1 adjunctions of the stage to the supplied domains
(`dualCtfPullAdjunction`, `dualCtfSupportAdjunction`). Compose their Hom bijections
using def-weil-pbc-composite-adjunction to obtain A ⊣ R and B ⊣ T
(`dualBaseChangeLeftAdjunction`, `dualBaseChangeRightAdjunction`). A2 and the stage
coherence datum give the exchange τ : A ≅ B whose forward map is the restriction
`dualBaseChangeExchange` of the given exchange.

2. Under def-weil-pbc-adjunction-conjugate, α = τ^c : T ⟶ R has component the unit of
A ⊣ R, followed by RτT, followed by R applied to the counit of B ⊣ T. Conjugating τ⁻¹
gives β : R ⟶ T, with the other unit, Tτ⁻¹R, and the other counit. Conjugation reverses
composition and preserves identities (`conjugateEquiv_comp`, `conjugateEquiv_id`), so
αβ and βα are identities, β = `conjugateIsoEquiv` of τ⁻¹ and β⁻¹ = `conjugateEquiv` of τ.

3. For a comparison of two squares with endpoint functors G,H and transformations x,y
satisfying (Gτ')y = x(τH) (fix-lem-exchanges (1)), the two conjugate-pasting identities
of lem-weil-pbc-mate-pasting give the corresponding equation for α and the mates of x,y.
Compose with the inverses β on both sides and cancel αβ and βα: this is
`DualBaseChangeMateLaws.square`.

4. Apply the two exchange-pasting equations of fix-lem-exchanges (2). Conjugation reverses
the composite, and lem-weil-pbc-mate-pasting identifies conjugates of whiskered terms with
whiskered conjugates under the pasted adjunctions. Taking inverses gives
β_gh = (Rg'_* β_h)(β_g Rh_*) and β_fe = (β_e Rf'^!)(Re^! β_f), with the direct composition
comparisons `dualCtfDirectComposition` and, by lem-sf-mate, the exceptional comparisons
`dualCtfExceptionalComposition`: these are `dualBaseChangeHorizontalComposite` and
`dualBaseChangeVerticalComposite`.

5. If g is proper, lem-weil-pbc-proper-base-change makes g' proper. A4 supplies
c_g : Rg_! ≅ Rg_* and c_g' : Rg'_! ≅ Rg'_* on the restricted domains
(`dualBaseChangeProperIdentification`); βproper is the composite of Rf^! c_g, β and
c_g'⁻¹ Rf'^!, which is the required equation by definition.
(blueprint: lem-sf-dual-base-change-higher-stages). -/
theorem dualBaseChangeHigherStages
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    dualBaseChangeStage S.higher.integral S.integralCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.integralExchange Q)) ∧
    dualBaseChangeStage S.higher.rational S.rationalCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.rationalExchange Q)) ∧
    dualBaseChangeStage S.closure.commonStage S.commonCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.closure.commonStageExchange Q)) := by
  sorry

end WeilConjectures
