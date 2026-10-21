/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData

/-! # Coefficient coherence for one completed operation pair

Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-raw-operation-coherence)
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
system morphisms, with normalized units and towers.
Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-raw-operation-coherence).
Proof: compare the two coefficient sheaf maps on every finite quotient and use
uniqueness of the inverse-limit map. Transport the direct-image scalar mate by
conjugateIsoEquiv and completed pullback by its unit-normalized strict-tower model.
Lift these comparisons and their inverses through the full complete subcategories.
Their inverse laws follow by faithfulness of the inclusions. The normalized
coefficient identity comparison, conjugated by the two model isomorphisms, gives
pPush(id); its composite with the source tensor unit is the target tensor unit.
The same argument with the completed pull comparison gives pPull(id). For three
fields, expand the two successive comparisons. Naturality moves the intervening
model maps, their inverses cancel, and the published scalar coefficient-tower
equations identify the remaining path with the single comparison through the
canonical tensor associator.
Localize the two comparisons and their inverses, conjugating by the specified
integral/raw tensor comparisons, including the equal-field tensor-unit branch.
Every raw object is integral and every arrow is a fraction of an integral arrow,
so these components determine the localized comparisons and all their equations.
The localized naturality and coefficient-tower equations give the raw system morphisms:
apply the source localization to each integral tower equation and substitute the
normalization of the raw associator. The adjacent inverse integral/raw comparisons
cancel. At E=M substitute the integral unit equations and the equal-field
normalization of the integral/raw comparison; the resulting beta components are
identities. Every raw object is Q(K), so extensionality gives HEq beta refl.
Additivity follows directly on the tensor Hom maps. -/
theorem rationalRawOperationCoherence :
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
    HasRawOperationCoherence l Ω q pPush pPull rPush rPull := by sorry

end Operations
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
