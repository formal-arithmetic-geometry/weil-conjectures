/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteFilteredLocalization
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

/-!
# Filtered-injective representatives in the filtered localization

Source: Stacks Project, Derived Categories, Tags 05TW, 05TY and 015Q
(blueprint: lem-trf-filtered-localization-injective-model).

The optional interval is absent for all finite filtrations and is `some (a, b)`
for filtrations with `Fᵃ = ⊤` and `Fᵇ⁺¹ = ⊥`. All constructions below use the
canonical filtered category, graded quasi-isomorphisms and localization functors.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

namespace CategoryTheory

/-- Filtered-injective resolutions compute the bounded-below filtered localization.
Source: Stacks Project, Derived Categories, Tags 05TW, 05TY and 015Q; the same
resolution construction preserves every prescribed finite filtration interval.

Proof:
1. Embed each finite filtered object strictly into a filtered injective by resolving
its finitely many graded pieces and using their finite direct sum. Resolve kernels
and coimages of the differentials, lift the maps between them to their resolutions,
and apply the filtered horseshoe construction. Totalize the resulting first-quadrant
resolution. After each graded functor the augmented columns are resolutions, so the
augmentation is a graded quasi-isomorphism. The total complex is bounded below and
termwise filtered injective. All embeddings, finite sums and cones preserve the
prescribed interval, so this construction works for each value of `B`.
2. A map from a graded-acyclic complex to a bounded-below filtered-injective complex
is null-homotopic: construct a filtration-preserving homotopy inductively from the
lowest nonzero target degree, extending over strict monomorphisms by filtered
injectivity. Apply this to a graded-acyclic cone and its shift. The Hom exact sequence
of its cone triangle makes precomposition by a graded quasi-isomorphism bijective.
Represent localized morphisms by left fractions; the preceding bijection removes
the denominator uniquely and gives exactly the bijectivity of localization on Hom.
3. The inclusion of filtered injectives is fully faithful, including on homotopy
categories. Part 2 gives full faithfulness after localization, and part 1 gives
essential surjectivity. Inclusion and localization preserve the standard cone
triangles and their shifts, so this comparison is a triangulated equivalence.
4. By the finite injective graded-filtration splitting theorem, each underlying
term is a finite direct sum of its injective graded pieces and is injective.
The graded terms are injective by definition. Forgetting and grading are additive,
hence preserve the bounded-below condition. Their composites on filtered injectives
are the ordinary evaluation functors term by term; the defining localization-lift
isomorphisms yield the two commutative squares, for forgetting and every grading.
(blueprint: lem-trf-filtered-localization-injective-model). -/
theorem filteredLocalization_injectiveModel
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] (B : Option (ℤ × ℤ)) :
    (∀ K : CochainComplex.Plus (FiniteFilteredObjects C B false),
      ∃ (I : CochainComplex.Plus (FiniteFilteredObjects C B true))
        (f : K ⟶ (filteredInjectiveInclusion C B).mapCochainComplexPlus.obj I),
        finiteFilteredQuasiIso C B
          ((HomotopyCategory.Plus.quotient (FiniteFilteredObjects C B false)).map f)) ∧
    (∀ K I : FiniteFilteredHomotopyPlus C B false,
      (∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p)) →
      Function.Bijective ((finiteFilteredQh C B).map : (K ⟶ I) →
        ((finiteFilteredQh C B).obj K ⟶ (finiteFilteredQh C B).obj I))) ∧
    (filteredInjectiveComparison C B).IsEquivalence ∧
    (filteredInjectiveComparison C B).IsTriangulated ∧
    (∀ (I : FiniteFilteredHomotopyPlus C B true) (n : ℤ) (p : Option ℤ),
      Injective ((filteredEvaluation C B true p).obj (I.obj.as.X n))) ∧
    (∀ p : Option ℤ,
      Nonempty (filteredInjectiveComparison C B ⋙ finiteFilteredDerivedEvaluation C B p ≅
        (filteredEvaluation C B true p).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)) := by
  sorry

end CategoryTheory
