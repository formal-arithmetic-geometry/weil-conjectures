/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerAdic.AdicHeartPullbackFibres
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.PerAdic.AdicHeartPullbackFibres
import WeilConjectures.CategoryTheory.StageSystem.Const
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Adic coefficient fibres in the intrinsic coefficient presentation

Source: Bhatt--Scholze, Section 6.8, especially Propositions 6.8.4 and 6.8.14
(blueprint: lem-per-adic-heart-pullback-fibres).
The original module supplies the raw completed-coefficient statements unchanged.
The declarations below transport their actual section normalization to the intrinsic
rational and common-stage categories used by the constructible Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ W)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The actual inclusion of a finite coefficient field, with its canonical small model.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicCoefficientEmbedding (L : Padic.FiniteCoefficientFields l Qbar) :
    AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L →+* Qbar :=
  L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom

variable {k : Type u} [Field k] [Fact (IsUnit (l : k))]
open PerAdic

end WeilConjectures
