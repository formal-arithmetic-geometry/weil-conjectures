/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitAdjunctionComparison

/-! # Regular completed units and their strict reductions

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap
namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalObject integralObject rationalSource modelScalar modelUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Strict multiplication identifies the reduction of the completed regular module
with the regular module on the whole coefficient sequence site.
Source: Bhatt--Scholze, Section 6.5 and Lemma 6.8.2(1); Stacks 06YY and 0941.
(blueprint: lem-pur-completed-unit-strict-comparison).
Proof: apply the simultaneous reduction model to the flat-term K-flat regular
single complex. Its nth scalar extension is the finite regular single complex
by multiplication, inverse z to 1 tensor z. Quotient maps preserve multiplication
and one. Thus these finite chain maps commute with every horizontal quotient
arrow and assemble to a chain map on the sequence site, using its strict-system
equivalence. The inverse maps assemble in the same way. Localizing this strict
isomorphism and composing the supplied simultaneous representative comparison
gives c. At each finite level the chain multiplication is the transpose of the
actual completed-ring projection. The normalized scalar-extension counit and
the reductionModel evaluation equation therefore give the asserted equation,
with precisely constantCoefficientReductionMap. The section condition on b
fixes the identification of the evaluation of the regular sequence module;
there are no scalar automorphisms left in those identifications. This is a
whole-system construction before localization and uses no joint faithfulness
of derived evaluation. Empty sites and degree-zero zero objects satisfy the
same formulas. -/
theorem completedUnitStrictComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x) :
    ∃ c : S.reduction.obj (integralConstantCoefficientObject l E W) ≅ systemObject l E W,
      ∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E W n).map c.hom ≫
          (evaluationSingle l E W n).hom ≫
          (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).map
            (b n).hom =
        (S.reductionEvaluation n).hom.app (integralConstantCoefficientObject l E W) ≫
          constantCoefficientReductionMap l E W n := by
  obtain ⟨d, hd⟩ := regularLimitComparisonData l E D hl W b hb
  exact adjunctionComparison l E W S b hb d hd

end WeilConjectures.CompletedUnitPullback
