/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Identification of finite words through the fixed scalar realization.
Source: blueprint operations proof (2), expanded steps 6--7; Stacks 00YV;
openTensorNormalization.finite_compatibility and compactSupport_exchange_transport.
(blueprint: lem-sp-strict-finite-word-identification).

Proof: the exact equivalence sfIntrinsicModuleEquivalence has underlying comparison
the additive sheafification counit. Its inverse is the sheafification unit on the
original module sections. The ordinary pullback square comparisonFiniteOrdinaryPull
therefore has exactly this section normalization; localize it and use the canonical
left-derived/exact comparison to obtain comparisonFinitePull. Conjugation of the
canonical derived adjunctions determines its unique right-adjoint comparison, with
both unit and counit equations. These comparisons give StrictFiniteCoordinates.
The flat K-flat tensor representative of the semilinear calculus and the tensor
model of finite_compatibility agree on every signed total summand: their ordinary
maps send pure tensors to the same pure tensors under the fixed counit. The total
summand injections and then localization identify the representative comparisons.
Thus finite_compatibility supplies the finite tensor isomorphism with exactly the
underlying, representative, and FiniteTensorPin normalizations requested here.
Transporting the proper counit transpose through these adjunction coordinates and
then the open tensor map through the finite tensor pin identifies the published
projection word, including its final pullback compositor, with comparisonLevelProjection.
Likewise the unit, pullback square, counit, and open unit commute with the fixed
realization, so the published compactification exchange becomes comparisonLevelExchange.
Apply compactSupport_exchange_transport at each individual etale-origin witness
to identify its input arrow with the ambient exchange. No compatibility between
witnesses is used. The open in a compactification is quasi-compact because f is
quasi-compact and its proper factor is separated. The argument also applies to
zero complexes, empty schemes, and identity open squares; ramification only changes
the canonical quotient-ideal equality, never the scalar normalization. -/
theorem strictFiniteWordIdentification (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) :
    ∃ coordinates : StrictFiniteCoordinates l E b,
      StrictFiniteExchangeComparisons l E b o levels coordinates ∧
      StrictFiniteProjectionComparisons l E b o levels coordinates := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
