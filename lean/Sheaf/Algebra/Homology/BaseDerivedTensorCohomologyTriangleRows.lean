/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.RingTheory.Flat.Basic

/-! # Universal base-change counits on distinguished triangles

Source: Stacks Project, Tag 06Y6, exactness and independence of derived change of rings.
(blueprint: lem-pc-base-derived-tensor-cohomology-triangle-rows). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

/-- Universal base-change models give an exact localized row and a morphism to the
ordinary extended triangle's homology row. No tensor coefficient complex is involved.

Source: Stacks Project, Tag 06Y6 (exact derived change of rings and universal counit).
Proof: restrict T to R and apply the exact derived extension functor to B. Identify
its three cohomology objects with the prescribed models by uniqueness of left derived
functors, with the counit commuting under these identifications. Naturality at
multiplication by each a in A identifies the A-actions. B-linearity and tensor
induction therefore make all three sequence maps A tensor_R B-linear. Restriction
of scalars is exact and reflects exactness, so the resulting five-term row is exact.
Extend this row to C; flatness preserves exactness. The universal counit commutes
with shifts and sends the third triangle map to the ordinary third triangle map.
Its naturality gives the first, second and fourth squares; shift compatibility and
naturality of the homology shift isomorphism give the boundary square. Transpose
these squares under extension/restriction adjunction; comparison_eq and localized_eq
identify their vertical arrows with the specified localizedComparison maps. This
construction uses only a distinguished localized triangle, not termwise exactness
of its scalar extension. Zero rings and unbounded or zero complexes are included.
(blueprint: lem-pc-base-derived-tensor-cohomology-triangle-rows). -/
theorem exists_baseDerivedTensorCohomologyModel_triangle_rows
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (hC : Module.Flat (A ⊗[R] B) C)
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let E := extendScalars (algebraMap (A ⊗[R] B) C)
    ∃ (s₀ : E.obj (m₁.cohomology i) ⟶ E.obj (m₂.cohomology i))
      (s₁ : E.obj (m₂.cohomology i) ⟶ E.obj (m₃.cohomology i))
      (s₂ : E.obj (m₃.cohomology i) ⟶ E.obj (m₁.cohomology (i + 1)))
      (s₃ : E.obj (m₁.cohomology (i + 1)) ⟶ E.obj (m₂.cohomology (i + 1))),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ m₂.localizedComparison i =
        m₁.localizedComparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₁) i ∧
      s₁ ≫ m₃.localizedComparison i =
        m₂.localizedComparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₂) i ∧
      s₂ ≫ m₁.localizedComparison (i + 1) = m₃.localizedComparison i ≫
        CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1) ∧
      s₃ ≫ m₂.localizedComparison (i + 1) = m₁.localizedComparison (i + 1) ≫
        HomologicalComplex.homologyMap (F.map T.mor₁) (i + 1) := by sorry

end ModuleCat
