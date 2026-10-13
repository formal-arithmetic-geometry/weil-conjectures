/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Acyclic enlargement with prescribed reduced cokernel

Source: Stacks Project, More on Algebra, Tag 0BCA.
-/

@[expose] public section

universe u v w w'

open CategoryTheory

namespace AlgebraicGeometry

/-- Construct an acyclic cone and a cokernel sequence for any acyclic lift of it.

Source: Stacks Project, More on Algebra, Tag 0BCA, cone and dotted-arrow paragraphs.
(blueprint: lem-sc-complex-lift-acyclic-enlargement).

Proof: Reduced class members are projective by extension of scalars. Represent the
supplied derived isomorphism by a quasi-isomorphism from E to the reduction of K₀,
using bounded projective complexes. Its mapping cone C is bounded above, acyclic,
and has terms reducing class members, by closure under binary sums. For any
bounded-above acyclic class complex A supplied with a reduction
isomorphism to C, regard C as an R-complex.
The quotient map A -> C is degreewise surjective and a quasi-isomorphism. Lift the
map K₀ -> C through it in the homotopy category, using K-projectivity of K₀. Lift
the correcting homotopy degreewise by projectivity and subtract its boundary.
This gives a strictly commuting map f : K₀ -> A whose reduction is the cone
inclusion. Take B to be the actual cokernel complex of f. The cokernel sequence is
right exact and B is bounded above. Extension of scalars preserves cokernels;
the cokernel of the cone inclusion is E[1]. This identifies the reduction of B
with E[1], and the reduced sequence splits in each degree. No injectivity of f
before reduction is asserted here; that is the separate class-splitting step. -/
theorem exists_complex_lift_acyclic_enlargement
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (K₀ : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hKbound : ∃ b : ℤ, K₀.IsStrictlyLE b)
    (hKterms : ∀ i : ℤ, K₀.X i ∈ Pclass)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P))
    (hderived : Nonempty (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀) ≅ DerivedCategory.Q.obj E)) :
    ∃ C : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ,
      (∃ b : ℤ, C.IsStrictlyLE b) ∧ C.Acyclic ∧
      (∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
        Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≅ C.X i)) ∧
      ∀ A : CochainComplex (ModuleCat.{max u v} R) ℤ,
        (∃ b : ℤ, A.IsStrictlyLE b) → A.Acyclic →
        (∀ i : ℤ, A.X i ∈ Pclass) →
        Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A ≅ C) →
        ∃ S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ),
          S.X₁ = K₀ ∧ S.Exact ∧ Epi S.g ∧ S.X₂.Acyclic ∧
          (∀ i : ℤ, S.X₂.X i ∈ Pclass) ∧ (∃ b : ℤ, S.X₃.IsStrictlyLE b) ∧
          Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj S.X₃ ≅ E⟦(1 : ℤ)⟧) ∧
          ∀ i : ℤ, Nonempty
            (((S.map (HomologicalComplex.eval (ModuleCat.{max u v} R)
              (ComplexShape.up ℤ) i)).map
                (ModuleCat.extendScalars (Ideal.Quotient.mk I))).Splitting) := by
  sorry

end AlgebraicGeometry
