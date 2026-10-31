/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularSequenceNormalized
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularSequenceLimit

/-! # The regular completed unit and its coefficient-system limit comparison

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemma 6.8.2(1), together with
the normalized coefficient-system evaluation calculus.

The theorem records the geometric part of the strict comparison separately from
the adjunction transport.  Its proof constructs the compatible finite quotient
maps from the normalized strict scalar unit, assembles them into the derived
coefficient-system limit, and proves the Roos completeness and normalization
properties of the regular completed object.
(blueprint: lem-pur-completed-unit-regular-limit-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The regular completed coefficient has a normalized derived limit comparison.

Proof: use the normalized strict scalar unit on the regular single complex.  Its
finite multiplication isomorphisms and section formulas identify every quotient
with the supplied `b`; the transition identities assemble these maps into a
cone over the coefficient tower.  The strict-unit quasi-isomorphism and its Roos
triangle identify the cone point with the completed regular object, while the
normalized evaluation calculus transports the cone to `coefficientSequenceLimit`.
The projection equation is the finite adjunction transpose of the same quotient
map.  The construction is valid for the empty scheme and for exponent zero.
(blueprint: lem-pur-completed-unit-regular-limit-comparison). -/
theorem regularLimitComparisonData (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u})
    (b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x) :
    ∃ c : integralConstantCoefficientObject l E W ≅
        (coefficientSequenceLimit l E W).obj (systemObject l E W),
      IsNormalizedCoefficientSequence l E W (systemObject l E W) ∧
      IntegralOnSlice.IsComplete l E W none (integralConstantCoefficientObject l E W) ∧
      ∀ n : ℕ,
        c.hom ≫ (coefficientSequenceProjection l E W n).app (systemObject l E W) ≫
            (coefficientFiniteDerivedRestriction l E W n).map
              (evaluationSingle l E W n).hom ≫
                (coefficientFiniteDerivedRestriction l E W n).map
                  ((DerivedCategory.singleFunctor _ 0).map (b n).hom) =
          (coefficientFiniteAdjunction l E W n).unit.app
              (integralConstantCoefficientObject l E W) ≫
            (coefficientFiniteDerivedRestriction l E W n).map
              (constantCoefficientReductionMap l E W n) := by
  obtain ⟨c, hc⟩ := regularSequenceLimitComparison l E D hl W b hb
  exact ⟨c, regularSequenceNormalized l E W b hb,
    (integralConstantCoefficient_constructible l E W D hl).2.2.1, hc⟩

end WeilConjectures.CompletedUnitPullback
