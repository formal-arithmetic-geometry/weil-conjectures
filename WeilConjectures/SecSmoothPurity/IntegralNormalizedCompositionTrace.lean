/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CompositionTrace
import WeilConjectures.SecSmoothPurity.IntegralNormalizedTraceRefinement

/-! # Integral coefficient components of normalized smooth counit composition

Source: current blueprint `sk-prop-sp-composition.proof.md`, the paragraph "Towers" and
the opening paragraph (`R lim` gives the integral identity).
(blueprint: lem-pur-integral-normalized-composition-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The normalized smooth counit transitivity equation `NormalizedCompositionTrace` holds
for `ℤ_ℓ` and for `𝒪_E` for every finite intermediate field `E` of the fixed algebraic
closure of `ℚ_ℓ` (ramified `E` included), for all smooth composable pairs, coherent support
data and arbitrary composite compactifications.

Proof in words.  The theorem is the two-step assembly supplied by the two helper
theorems imported above.  First,
`integralCompositeNormalizedCompositionTrace` gives the normalized equation for the
integer coefficient and for every finite-intermediate-field coefficient on each
generated composite compactification.  Then
`normalizedCompositionTrace_of_composite` transports each of those equations through
the common-refinement comparison, coherent support compositor, and normalized counit
naturality, yielding the equation for the arbitrary compactification and support data
quantified by `NormalizedCompositionTrace`.  Applying these two steps to the integer
case and pointwise to the finite-intermediate-field case gives the displayed
conjunction. -/
theorem integralNormalizedCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    NormalizedCompositionTrace ell D hEll .integers ∧
      ∀ E : PadicAlgCl.FiniteIntermediateField ell,
        NormalizedCompositionTrace ell D hEll (.integral E) := by
  have h := integralCompositeNormalizedCompositionTrace ell D hEll
  refine ⟨?_, ?_⟩
  · exact normalizedCompositionTrace_of_composite ell D hEll .integers h.1
  · intro E
    exact normalizedCompositionTrace_of_composite ell D hEll (.integral E) (h.2 E)

end AlgebraicGeometry.ProEtale.PurityTransport
