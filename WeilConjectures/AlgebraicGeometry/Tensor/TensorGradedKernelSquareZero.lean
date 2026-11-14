/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedKernelLocalIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.CommRingCat

/-! # Square-zero kernel of the graded tensor quotient

Source: Stacks Project, Tag 09MS, the square-zero direct-sum ideal sequence.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

/-- The homogeneous quotient has square-zero kernel when the immersion does.
Source: Stacks Project, Tag 09MS, the square-zero direct-sum ideal sequence. -/
theorem tensorGradedKernel_squareZero {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (A : TensorGradedAlgebraData j L) (hI : j.ker ^ 2 = ⊥) :
    ∀ (U : X.Opens) (a b : A.B.right.obj.obj (op U)),
      A.p.right.hom.app (op U) a = 0 → A.p.right.hom.app (op U) b = 0 → a * b = 0 := by
  intro U a b ha hb
  apply TopCat.Presheaf.IsSheaf.section_ext A.B.right.property
  intro x hx
  obtain ⟨V, hVU, hxV, haV, hbV⟩ := tensorGradedKernel_locally_ideal j L A U a b ha hb x hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  have hJ : j.ker.ideal V * j.ker.ideal V = ⊥ := by
    have h := congrArg (fun J : X.IdealSheafData ↦ J.ideal V) hI
    simpa only [pow_two, IdealSheafData.ideal_mul, Pi.mul_apply,
      IdealSheafData.ideal_bot, Pi.bot_apply] using h
  have hprod := Ideal.mul_mem_mul haV hbV
  rw [← Ideal.map_mul, hJ, Ideal.map_bot] at hprod
  simpa only [Ideal.mem_bot, map_mul, map_zero] using hprod

end
end AlgebraicGeometry.Scheme.Modules
