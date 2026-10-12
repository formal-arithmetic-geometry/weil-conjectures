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
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.Algebra.Homology.AcyclicLift
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRings

/-!
# Lifting a derived complex for a projective class

Source: Stacks Project, More on Algebra, Lemma 15.75.2 (Tag 0BCA)
(blueprint: lem-sc-complex-lift-class-projective).
-/

@[expose] public section

universe u v w w'

open CategoryTheory

namespace AlgebraicGeometry

/-- Stacks Project, More on Algebra, Tag 0BCA, lemma-lift-complex
(blueprint: lem-sc-complex-lift-class-projective).

Reduction is Mathlib's extension of scalars to `R ⧸ I`, including the differential.
The class condition is expressed for any model of a binary direct sum. The hypothesis
on the derived reduction is included in `hK`: a bounded-above projective representative
computes derived tensor product by ordinary termwise extension of scalars.

Proof:
1. Choose the representative in (5). By (1) its terms are projective, hence flat.
   Apply `lem-pc-module-bounded-flat-kflat` and `lem-pur-derived-change-of-rings`
   to compute derived reduction. By (4), E is bounded above and projective; use
   `lem-pc-ring-derived-map-representative` to represent the derived isomorphism
   by a quasi-isomorphism from E to the reduced representative.
2. Its cone C is bounded above and acyclic. Each term is a sum of two reductions,
   hence a reduction of a class member by (2).
3. Apply `lem-sc-complex-lift-acyclic-projective` to lift C to an acyclic class
   complex A with a termwise surjective reduction map to C.
4. Use `lem-pc-ring-derived-map-representative` to lift the cone inclusion to a map
   from the representative to A up to homotopy. Lift the homotopy through the
   termwise surjection by projectivity and subtract its boundary to obtain strict
   commutation. Its reduction is a split injection with class-reduction cokernel.
5. Such a map between class members is split injective: lift the projection onto
   the reduced cokernel to a class member by projectivity. By (3) it is surjective
   and splits. Its kernel is in the class by (2). The projection of the original
   map onto this kernel is an isomorphism modulo I, hence surjective by (3),
   and splits by (1). Its kernel T is in the class by (2) and has zero reduction.
   Zero is in the class as a summand; (3) applied to zero to T gives T = 0.
6. The cokernel complex Q is bounded above with class terms. Since A is acyclic,
   Q shifted by -1 represents K. The termwise split sequence remains exact after
   reduction; its cokernel is E shifted by 1, so Q shifted by -1 reduces to E
   as a complex, with all differentials respected. -/
theorem complex_lift_class_projective
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hsurj : ∀ (P₁ P₂ : ModuleCat.{max u v} R) (f : P₁ ⟶ P₂),
      P₁ ∈ Pclass → P₂ ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P))
    (hK : ∃ K₀ : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, K₀.IsStrictlyLE b) ∧ (∀ i : ℤ, K₀.X i ∈ Pclass) ∧
      Nonempty (DerivedCategory.Q.obj K₀ ≅ K) ∧
      Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) ≅ DerivedCategory.Q.obj E)) :
    ∃ P₀ : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, P₀.IsStrictlyLE b) ∧ (∀ i : ℤ, P₀.X i ∈ Pclass) ∧
      Nonempty (DerivedCategory.Q.obj P₀ ≅ K) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀ ≅ E) := by
  sorry

end AlgebraicGeometry
