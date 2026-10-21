/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.IntegralConstructibleKernels
import Sheaf.Paper.ConstructibleCokernelsExtensions

/-! # Closure for integral constructible module objects

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1),(3), with the
integral finite-presentation comparison spelled out below.
(blueprint: lem-weil-pbc-integral-constructible-serre)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Integral constructible module objects form a weak Serre class.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1),(3), with the
integral finite-presentation comparison spelled out below.
(blueprint: lem-weil-pbc-integral-constructible-serre)

Proof: the coefficient-dependent kernel closure is combined with generic cokernel
and extension closure for locally finitely presented internal module sheaves. The latter
uses finite generator lifts and presentations, so requires no noetherianity of the
coefficient ring. The kernel assertion retains the finite integral model comparison
and the DVR argument. All three closures concern the same constructibility property. -/
theorem integralConstructible_serre (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) := by
  obtain ⟨hc, he⟩ := constructible_cokernels_extensions X
    (condensedRingObj (integralCoeff ℓ E) X)
  exact ⟨integralConstructible_kernels ℓ E X, hc, he⟩

end AlgebraicGeometry.ProEtale.CondensedRing
