/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Exactness and degree projections for a graded quotient

Source: Stacks Project, Tag 09MS, direct sum of coherent-equation-ses.
(blueprint: lem-sc-tensor-graded-degree-data).
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

/-- The canonical kernel sequence of a graded algebra quotient, with its degree maps.
The kernel object and its inclusion are fixed, rather than selected from existence.
Source: Stacks Project, Tag 09MS, direct sum of coherent-equation-ses.
(blueprint: lem-sc-tensor-graded-degree-data). -/
structure TensorGradedDegreeData {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (A : TensorGradedAlgebraData j L) where
  shortExact : (ShortComplex.kernelSequence (tensorGradedAlgebraMap A.p)).ShortExact
  k : ∀ d : ℕ,
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶ kernel (tensorGradedAlgebraMap A.p)
  degree : ∀ d : ℕ,
    ShortComplex.kernelSequence (tensorGradedAlgebraMap A.p) ⟶
      ShortComplex.kernelSequence (tensorGradedUnit j (L.tensorPow d))
  q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf A.C ⟶
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d))
  degree_quotient : ∀ d : ℕ, (degree d).τ₃ = q d
  k_colimit : IsColimit (Cofan.mk (kernel (tensorGradedAlgebraMap A.p)) k)
  k_inclusion : ∀ d : ℕ, k d ≫ kernel.ι _ = kernel.ι _ ≫ A.b d
  c_projection : ∀ d : ℕ, A.c d ≫ q d = 𝟙 _
  k_projection : ∀ d : ℕ, k d ≫ (degree d).τ₁ = 𝟙 _
  k_orthogonal : ∀ a d : ℕ, a ≠ d → k a ≫ (degree d).τ₁ = 0

end
end AlgebraicGeometry.Scheme.Modules
