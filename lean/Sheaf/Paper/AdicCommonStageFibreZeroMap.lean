/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.AdicNormalizedFibreCommonStageData

/-! # Common-stage zero-map detection -/

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

/-- Any common fibre family with natural finite-stage comparisons detects zero maps.
Source: BS 6.8.14 (blueprint: lem-per-common-stage-fibre-zero-map).

Proof: put the source and target of the common arrow into finite heart presentations,
and represent their conjugated arrow at one common finite stage. Enlarge once more so
both representatives belong to the finite heart, using t-exactness and finite-heart
presentations. Naturality of each finite_stage comparison conjugates the fibre map to
the scalar extension of the finite fibre map. If all common maps vanish, faithfulness
of field tensor makes every finite fibre map zero. Finite-fibre zero-map detection
makes the finite arrow zero. Its quotient class and its conjugate are therefore zero.
This uses one stage for the arrow, independently of the geometric point; no simultaneous
choice of fields indexed by all points is required. The argument includes empty schemes
and zero objects since finite-fibre detection already includes these cases.
-/
theorem common_stage_fibre_zero_map (ω : Fibres (k := k) l R)
    (point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x)
    (h : CommonStageHeartExactness.{u, v, w} l Ω (k := k))
    (X : FiniteTypeBase k)
    (F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) (f : F ⟶ G)
    (hf : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point X κ x).functor.map f = 0) : f = 0 := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
