/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralBasicRealization
public import WeilConjectures.SixFunctors.GeneratorReductionStatement
public import WeilConjectures.SixFunctors.IntegralExpressionRecursionData
import WeilConjectures.SixFunctors.IntegralExpressionCanonicalSupport
import WeilConjectures.SixFunctors.IntegralExpressionCanonicalEquations

/-! # Recursion for integral expression comparisons

Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient-comparison
sentence; the expression-tree refinement in the DAG
(blueprint: lem-sf-integral-expression-recursion).

The comparison data below are the given primitive comparisons, restricted to the
published intermediate domains. All coefficient equalities live in the derived
category of strict systems. No structural-generator coherence is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
namespace ExpressionRecursion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Simultaneous finite-tree recursion for the given primitive realizations and their
whole-system coefficient maps.
Source: blueprint latest, fix-prop-coherence.proof.md, coefficient-comparison sentence;
the expression-recursion refinement in the DAG
(blueprint: lem-sf-integral-expression-recursion).

Proof: recursively compose the primitive coefficient natural transformations,
whiskering through each unary functor and taking the product of both tensor
children. Restrict this explicit transformation to the expression domain and
transpose it using the actual reduction/limit adjunction. The component
invertibility lemma makes this transpose an isomorphism, whose inverse defines
the canonical comparison family. Applying the inverse hom-set equivalence gives
the coefficient identity directly, before any finite evaluation. The canonical
equations lemma identifies this specified inverse with the displayed leaf, unary,
tensor and open/proper recursive formulas. The canonical support lemma identifies
the one-input compactification branch with the given direct comparison by its
whole-system normalization. Combine these three conclusions for the same family. -/
theorem integralExpressionRecursion (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (d : Primitives l E D o) (_rec : Reconstruction l E D)
    (dc : DirectComparisons l E D o d.model) :
    ∃ c : Comparisons l E D o,
      (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
        {W : Over (Spec (.of D.k))} (e : Expression _ I X W)
        (g : e.geometric) (K : (e.domain l E o).FullSubcategory),
        Equations l E d c e g K ∧
          coefficientMap l E d e g K.obj =
            (calculus l E W.left).reduction.map ((c e g).inv.app K) ≫
              (calculus l E W.left).adjunction.counit.app
                ((e.evaluate (systemInterpretation l E o)).obj
                  ((inputReduction l E X).obj K.obj))) ∧
      SupportAgreement l E d dc c := by
  refine ⟨canonicalComparisons l E D o d _rec, ?_,
    canonicalComparisons_support l E D o d _rec dc⟩
  intro I _ X W e g K
  exact ⟨canonicalComparisons_equations l E D o d _rec e g K,
    canonicalComparisons_coefficient l E D o d _rec e g K⟩

end ExpressionRecursion
end WeilConjectures.IntegralSystemRealization
