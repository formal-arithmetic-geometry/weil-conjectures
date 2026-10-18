/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons

/-! # Completed pullback on the actual common-stage Qbar category

Source: Stacks Tag 099N (2),(5); Bhatt--Scholze, Section 6.8, Remark 6.8.15
(blueprint: def-weil-pbc-completed-pullback).
The published strict-tower pullback is retained. Its integral restriction and the
normalized completed scalar comparisons descend it to the existing pair category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  (f : X ⟶ Y)

/-- Restriction of the actual completed pullback to the integral constructible objects.
Source: BS 6.8.2 and Remark 6.8.15; Stacks 099N
(blueprint: def-weil-pbc-completed-pullback).
Proof: take finite reductions of a K-flat integral representative. The strict-tower
comparison identifies the reductions of completed pullback with exact finite-level
inverse image. Pull back the finite constructible stratification and its etale-origin
witnesses. Boundedness is unchanged by exact finite inverse image, and the tower
construction gives intrinsic completeness. These verify each defining integral
constructibility condition. No nonemptiness or base-field invertibility is used. -/
theorem pbcQbarIntegralPull_mem (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω Y E) :
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj) := by
  sorry

/-- The coherent pullback family is fixed by the actual integral pullback and the
normalized scalar comparison; in particular no arbitrary natural isomorphism is chosen.
Source: BS Remark 6.8.15; Stacks 099N
(blueprint: def-weil-pbc-completed-pullback).
Proof: restrict completed pullback by pbcQbarIntegralPull_mem and rationalize its
coefficient-linear maps. The inverse of the localized completed scalar comparison
is the beta map of this family. Its tensor-unit and associator equations give the
coherent-family equations, including repeated fields. PbcPullbackBetaSpec fixes
these components on every integral representative and rationalization fixes all
fraction arrows, so the specified finite-stage functors and beta maps are unique. -/
theorem pbcQbarPullFamily_existsUnique :
    ∃! F : StageSystem.Morphism
        (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        F.Φ E = pbcDescentPullback l Ω f (pbcQbarIntegralPull_mem l Ω f) E) ∧
      PbcPullbackBetaSpec l Ω f (pbcQbarIntegralPull_mem l Ω f) F := by
  sorry

/-- The unique normalized common-stage family of actual completed pullbacks.
Source: BS Remark 6.8.15 (blueprint: def-weil-pbc-completed-pullback). -/
def pbcQbarPullFamily : StageSystem.Morphism
    (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out) :=
  (pbcQbarPullFamily_existsUnique l Ω f).exists.choose

/-- The pair-category pullback: (E,K) goes to (E,Lf*K), and a common-stage arrow
is mapped by the normalized beta, actual pullback, inverse beta formula.
Source: BS Remark 6.8.15 (blueprint: def-weil-pbc-completed-pullback). -/
def pbcQbarCompletedPull : pbcQbarCategory l Ω Y ⥤ pbcQbarCategory l Ω X :=
  (pbcQbarPullFamily l Ω f).functor

end AlgebraicGeometry.Scheme
