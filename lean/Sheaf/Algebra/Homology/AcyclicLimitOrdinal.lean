/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Acyclicity of ordinal inverse limits

Source: Stacks Project, Homology, Lemma 12.31.8, Tag 0AAT
(blueprint: lem-pur-kinjective-ML-ordinals).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- Stacks Project, Homology, Tag 0AAT (blueprint: lem-pur-kinjective-ML-ordinals).
An inverse system of acyclic complexes indexed by an ordinal has acyclic limit if each
stage maps surjectively, degree by degree, onto the limit of the preceding stages.
The surjectivity hypothesis is written as lifting every compatible family on `Set.Iio β`.

Proof: argue by transfinite induction on the ordinal, simultaneously for all such systems.
For a degree-zero cocycle `x`, recursively choose compatible primitives in degree minus one.
At the first stage use acyclicity. At a successor, choose an arbitrary primitive; its defect
from the preceding primitive is a degree-minus-one cocycle, hence a boundary. Lift a
primitive of this defect in degree minus two by surjectivity, and add its differential.
At a limit stage the earlier inverse-limit complex is acyclic by the induction hypothesis.
The same correction applies: the difference between the compatible earlier primitives and
the image of an arbitrary primitive is a cocycle in that limit. Write it as a boundary,
lift its degree-minus-two primitive by the stated surjectivity, and add its differential.
The resulting compatible family is a primitive of `x` in the full limit. Apply the same
argument to each shift to obtain exactness in every integer degree. These are the five
elementary proof steps of the node; no further proof dependencies are used. -/
theorem acyclic_limit_of_surjective_initialSegments
    (α : Ordinal.{u}) (K : α.ToTypeᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ)
      (x : ∀ γ : Set.Iio β, (K.obj (op γ.val)).X n),
      (∀ (γ δ : Set.Iio β) (h : γ ≤ δ),
        (K.map (homOfLE (show γ.val ≤ δ.val from h)).op).f n (x δ) = x γ) →
      ∃ y : (K.obj (op β)).X n, ∀ γ : Set.Iio β,
        (K.map (homOfLE (le_of_lt γ.property)).op).f n y = x γ) :
    (limit K).Acyclic := by
  sorry

end CochainComplex
