/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientNormalizedReductionModels

/-! # Components of normalized coefficient evaluation projection

Source: Stacks 07A4, 08J9 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-evaluation-projection-components).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Every finite evaluation of the unit-defined normalized projection is invertible.
This is the componentwise finite-prefix calculation; the remaining joint detection
of isomorphisms is proved in `coefficientNormalizedEvaluationProjection`.
Source: Zheng Construction 4.1 and Proposition 4.17(a); Stacks 07A4 and 08J9;
the component calculation in step 3 of
`lem-coef-normalized-evaluation-projection`.
(blueprint: lem-coef-normalized-evaluation-projection-components).

Proof: identify the actual evaluation tensor comparison with the normalized
semilinear comparison on flat-term K-flat representatives. For levels at most `n`,
the projection factors as scalar tensor reassociation followed by the normalized
reduction of `M`; for larger levels the singleton extension and its tensor image
are zero. The representative normalization and exact evaluation transport these
component isomorphisms to the displayed derived morphism. -/
theorem coefficientNormalizedEvaluationProjection_components
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (M : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M) (n : ℕ)
    (L : normalizedDVRDerived l E W n ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceDerivedEvaluation l E W n)
    (P : normalizedDVRDerived l E W n) (q : ℕ) :
    IsIso ((coefficientSequenceDerivedEvaluation l E W q).map
      ((adj.homEquiv _ _).symm
        ((R.finiteClosed n).tensor.map
            (Prod.mkHom (adj.unit.app P)
              (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj M))) ≫
          (R.evaluationTensor n).inv.app (L.obj P, M)))) := by
  sorry

end WeilConjectures
