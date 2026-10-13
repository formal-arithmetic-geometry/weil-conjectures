/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence

/-! # Exact five-term diagrams for localized tensor comparison

Source: Stacks Project, Tags 06Y6, 0BYJ and 0DJA(1).
(blueprint: lem-pc-localized-tensor-comparison-triangle-five-term-diagram).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The comparison is a morphism of exact five-term cohomology sequences.
No component is assumed or asserted to be invertible.

Source: Stacks Project, Tag 06Y6 (exactness of derived tensor), Tag 0BYJ
(functorial associativity), and Tag 0DJA(1) (the tensor comparison).

Proof: first represent T by a cone triangle f : P₁ → P₂ of K-flat complexes.
A roof for the first morphism, followed by a K-flat replacement of its apex,
gives such f; its cone P₃ is K-flat. Tensor this triangle with Q over A.
hQ preserves the quasi-isomorphisms used in its presentation. Restrict to R
and derive extension to B. Derived tensor is exact by Tag 06Y6. Multiplication
by A commutes with this functor, so its long cohomology sequence is a sequence
of A tensor_R B-modules. Extend this sequence to C. Flatness hC preserves
its exactness. The second exact functor is derived extension from A to C
followed by derived tensor with N. Scalar extension of each Pⱼ is K-flat over
C, so its values are computed by F(Pⱼ) tensor N without K-flatness of N.

The universal counit for R-to-B extension, the scalar-extension map and t
give the comparison. To check the connecting square, compute on the cone
presentation before descending: the tensor-cone identification reindexes
the P₂ summands and the shifted P₁ summands. A degree-zero map on the second
factor acts on both summands and commutes with the inclusion and projection.
The Koszul signs in the shift identification occur on both sides of that
projection square. The scalar-extension unit and tensor associator satisfy
the same summand equations. Thus the comparison commutes with the cone
boundary as well as f and the cone inclusion. Taking homology gives a morphism
of long exact sequences. Take the consecutive terms belonging to
P₁ at i, P₂ at i, P₃ at i, P₁ at i+1 and P₂ at i+1 to obtain exact S, D and φ.

Finally transport each vertical arrow to the prescribed U₁, U₂ and U using
exists_localizedTensorComparison_representative_square. The derived cone
presentation identifies their derived objects with those of P₁, P₂ and P₃;
both sides are K-flat. The square theorem supplies source and target
isomorphisms commuting with each comparison composite, hence an arrow
isomorphism. Its model-universality argument includes arbitrary prescribed
models; alternatively apply localized model independence first. This gives
the five stated arrow isomorphisms. No comparison-isomorphism hypothesis or
five lemma is used here. The same cone and cohomology argument covers zero
complexes, zero rings, split triangles and arbitrary degrees.
(blueprint: lem-pc-localized-tensor-comparison-triangle-five-term-diagram). -/
theorem exists_localizedTensorComparison_triangle_five_term_diagram
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ T.obj₃))
    (hUK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
    (U₁ U₂ : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU₁ : Nonempty (DerivedCategory.Q.obj U₁ ≅ T.obj₁))
    (hU₂ : Nonempty (DerivedCategory.Q.obj U₂ ≅ T.obj₂))
    (hK₁ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U₁ (curriedTensor _)).Acyclic)
    (hK₂ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U₂ (curriedTensor _)).Acyclic)
    (m₁ : BaseDerivedTensorCohomologyModel R A B (U₁ ⊗ Q) C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B (U₂ ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
      (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
        m.localizedComparison j ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
    ∃ (S D : ComposableArrows (ModuleCat.{u} C) 4) (φ : S ⟶ D),
      S.Exact ∧ D.Exact ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 0) ≅ Arrow.mk (cmp U₁ m₁ i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 1) ≅ Arrow.mk (cmp U₂ m₂ i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 2) ≅ Arrow.mk (cmp U mU i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 3) ≅ Arrow.mk (cmp U₁ m₁ (i + 1))) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 4) ≅ Arrow.mk (cmp U₂ m₂ (i + 1))) := by
  sorry

end ModuleCat
