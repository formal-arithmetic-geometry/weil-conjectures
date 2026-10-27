/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurReductionLimitShiftData
public import Sheaf.Paper.SequenceKInjectiveComparisonShifts
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Finite models of the adjoint coefficient shift

Source: Stacks 06YY, 07A6 and 0941; current blueprint
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The shift of reduction adjoint to the canonical total-limit shift agrees with
all finite K-flat scalar-extension models and the supplied evaluation isomorphisms.
Source: Stacks 06YY (derived tensor), 07A6 (derived adjunction), and 0941;
current blueprint coefficient-comparison sentence
(blueprint: lem-pur-reduction-finite-shift-normalization).

Proof: use the ordinary tensor/limit adjunction of the quotient ring diagram.
Its Hom bijection sends a map to its compatible finite scalar transposes. Resolve
one input by a flat-term K-flat complex; shifting gives the same quotient complex
on reindexed terms with differential multiplied by (-1)^r. Derive the finite
scalar extension with this termwise shift; its universal comparison agrees with
coefficientFiniteReductionModel, on every K-flat complex, by the universal counit.
Resolve the restricted output simultaneously by a K-injective tower. The exact
restriction/localization comparison, Rlim of the replacement map, and the inverse
derived unit give precisely purCoefficientLimitModel. The proved replacement
shift square computes its canonical total-limit shift on the shifted replacement.
The ordinary Hom transposes commute with these shifts. Hence the prescribed
unit-normalized coefficient evaluations identify the shift on reduction with the
mate of that limit shift, by uniqueness of compatible adjoint shifts. Substituting
this equality gives the evaluation squares. These are natural system maps before
evaluation; faithfulness of derived evaluation is not assumed. The construction
uses no finite-field datum, finiteness of W, completeness, or exact products.
For r=0 the comparisons are identities; for r+s the two differential signs
multiply, including negative r. The zero complex and the empty scheme give the
same identity squares. -/
theorem purReductionFiniteShiftNormalization
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    letI := S.adjunction.leftAdjointCommShift ℤ
    ∃ finite_reduction_shift :
        ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ,
      (∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (hQr : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧)),
      letI := finite_reduction_shift n
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
        ((coefficientFiniteDerivedExtension l E W n).commShiftIso r).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
      (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
        DerivedCategory.Q.map
          ((((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso r).hom.app Q) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) ∧
      (∀ n : ℕ,
      letI := finite_reduction_shift n
      NatTrans.CommShift (S.reductionEvaluation n).hom ℤ) := by sorry

end WeilConjectures
