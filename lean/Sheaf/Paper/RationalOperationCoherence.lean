/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData

import Sheaf.Paper.RationalRawOperationCoherence
import Sheaf.Paper.FiniteStageKaroubiExtension

/-! # Coefficient coherence for one completed operation pair

Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-operation-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Operations

variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)

/-- One completed operation pair has its canonical integral comparisons, raw coefficient
system morphisms, and supported Karoubi extensions, with normalized units and towers.
Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-operation-coherence).
Proof: compare the two coefficient sheaf maps on every finite quotient and use
uniqueness of the inverse-limit map. Transport the direct-image scalar mate by
conjugateIsoEquiv and completed pullback by its unit-normalized strict-tower model.
Lift these comparisons through the full complete subcategories. Scalar-extension
unit and successive-extension equations give their integral units and towers.
Localize the two comparisons and their inverses, conjugating by the specified
integral/raw tensor comparisons, including the equal-field tensor-unit branch.
Every raw object is integral and every arrow is a fraction of an integral arrow,
so these components determine the localized comparisons and all their equations.
Extend by functorExtension₂; naturality at the projector and idempotence give the
supported inverse formulas and preserve the same unit and tower equations. -/
theorem rationalOperationCoherence :
  ∃ (pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω V a ≅
      pbcAmbientCompleteIntegralTransition l Ω U a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) q),
  ∃ (pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω U a ≅
      pbcAmbientCompleteIntegralTransition l Ω V a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) q),
  ∃ (rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
    (pbcAmbientCompleteRawSystem l Ω V)),
  ∃ (rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω V)
    (pbcAmbientCompleteRawSystem l Ω U)),
    HasOperationCoherence l Ω q pPush pPull rPush rPull := by
  obtain ⟨pPush, pPull, rPush, rPull, hr⟩ := rationalRawOperationCoherence l Ω q
  obtain ⟨tU, tV, mPush, hmPush, mPull, hmPull, hpPush, hpPull, huPush, huPull,
    hrPush, haPush, hnPush, hbPush, hrPull, haPull, hnPull, hbPull⟩ := hr
  obtain ⟨kPush, hkPush, hbKPush, huKPush⟩ := completeKarMorphism_exists l Ω rPush hnPush
  obtain ⟨kPull, hkPull, hbKPull, huKPull⟩ := completeKarMorphism_exists l Ω rPull hnPull
  refine Exists.intro @pPush ?_
  refine Exists.intro @pPull ?_
  refine Exists.intro rPush ?_
  refine Exists.intro rPull ?_
  refine ⟨@tU, @tV, mPush, hmPush, mPull, hmPull, ?_⟩
  refine ⟨@hpPush, @hpPull, huPush, huPull, ?_⟩
  refine ⟨hrPush, haPush, hnPush, @hbPush, ?_⟩
  refine ⟨hrPull, haPull, hnPull, @hbPull, ?_⟩
  refine ⟨kPush, ?_, ?_, ?_, ?_, kPull, ?_, ?_, ?_, ?_⟩
  · exact hkPush
  · intro E
    rw [hkPush E]
    let := haPush E
    infer_instance
  · exact @hbKPush
  · exact huKPush
  · exact hkPull
  · intro E
    rw [hkPull E]
    let := haPull E
    infer_instance
  · exact @hbKPull
  · exact huKPull

end Operations
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
