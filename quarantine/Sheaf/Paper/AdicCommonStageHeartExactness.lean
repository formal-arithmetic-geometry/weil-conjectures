/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.AdicNormalizedFibreCommonStageData

/-! # Exact representatives in the common heart -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Finite inclusions preserve homology and finite exact diagrams descend; field tensor
is faithful and exact with injective unit.
Source: BS 6.8.14 (blueprint: lem-per-common-stage-heart-exactness).

Proof: apply the heart cone formulas to finite cones and their common images. The
triangulated inclusions and their t-exact truncation comparisons preserve kernels and
cokernels with their maps. Images are kernels of cokernels, and homology is their
image-to-kernel quotient, so these too are preserved. For eventual vanishing, express
identity equals zero in the quotient and use eventual equality to make it hold at one
finite enlargement. The converse follows by applying the inclusion functor. Represent
all objects, arrows and zero composites of a finite complex at one stage, using finite
heart presentations and the common-stage calculus. This proves finite-complex descent.
For a short exact complex, its endpoint kernel, middle homology and endpoint cokernel
have zero common image. Kill their identities at a common enlargement; exact finite
transitions preserve these defects, so the enlarged representative is short exact.
Finally field tensor preserves limits by flatness and colimits by adjunction. A linear
coordinate functional on Omega taking 1 to 1 retracts the unit w ↦ 1 tensor w, proving
its injectivity and, by naturality, faithfulness of scalar extension.
-/
theorem common_stage_heart_exactness :
    Nonempty (CommonStageHeartExactness.{u, v, w} l Ω (k := k)) := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
