/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence

/-! # The ordinary universal derived tensor triangle row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

/-- The exact row before the final extension of coefficients, together with its
ordinary universal-counit squares. There is no flatness hypothesis and no localized map.

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1 (exactness and choice independence).
Proof: restriction of scalars A to R is exact, so it sends the distinguished
localized triangle to a distinguished triangle in D(R). Apply the exact total
left derived extension R to B supplied by exists_baseDerivedExtension_resolution.
Universal uniqueness identifies each model's derived functor with this common
functor, compatibly with its counit. Conjugate its long exact cohomology sequence
by the cohomologyIso identifications of the three models in degrees i and i+1.
The three same-degree maps commute with multiplication by A by functoriality.
The boundary also commutes with it: multiplication gives an endomorphism of the
input triangle and the homology boundary is natural in that endomorphism.
The cohomologyIso_smul equations identify these endomorphisms with a tensor 1.
B-linearity and induction on pure tensors give A tensor_R B-linear maps.
Faithful exact restriction to B reflects the exactness of the resulting row.
For the counit squares, compute on K-flat resolutions: the augmentation is a
morphism of triangles commuting with the shift. Universal uniqueness transports
these identities to the prescribed model counits. Apply homology; ordinaryIso
is natural and compatible with shifts since its pure-tensor formula fixes it.
Substitution of comparison_eq proves the three arrow squares and boundary square.
Only the image of T in D(A) need be distinguished: neither T nor its ordinary
extension must be termwise exact. The construction applies unchanged to zero
rings, zero complexes, arbitrary degrees and unbounded complexes.
(blueprint: lem-pc-base-derived-tensor-ordinary-triangle-rows). -/
theorem exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C) (i : ℤ) :
    let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    ∃ (s₀ : m₁.cohomology i ⟶ m₂.cohomology i)
      (s₁ : m₂.cohomology i ⟶ m₃.cohomology i)
      (s₂ : m₃.cohomology i ⟶ m₁.cohomology (i + 1))
      (s₃ : m₁.cohomology (i + 1) ⟶ m₂.cohomology (i + 1)),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ m₂.comparison i =
        m₁.comparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₁) i ∧
      s₁ ≫ m₃.comparison i =
        m₂.comparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₂) i ∧
      s₂ ≫ m₁.comparison (i + 1) = m₃.comparison i ≫
        CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1) ∧
      s₃ ≫ m₂.comparison (i + 1) = m₁.comparison (i + 1) ≫
        HomologicalComplex.homologyMap (F.map T.mor₁) (i + 1) := by sorry

end ModuleCat
