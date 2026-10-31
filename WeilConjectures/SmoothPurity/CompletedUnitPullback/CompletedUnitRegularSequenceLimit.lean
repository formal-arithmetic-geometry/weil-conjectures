/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData

/-! # Derived limit of the regular quotient sequence

Source: Bhatt--Scholze Sections 3.5 and 6.5; Stacks 0941.

The strict quotient tower of the regular completed module has the specified
derived sequence limit, with its actual finite projection legs.
(blueprint: lem-pur-completed-unit-regular-sequence-limit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed regular sheaf is the derived limit of its strict quotient sequence,
with the prescribed finite projection legs.

Source: Bhatt--Scholze Sections 3.5 and 6.5, Lemma 6.8.2(1); Stacks 0941.
Proof: identify each finite scalar extension of the regular single complex with
the finite regular single complex by multiplication, inverse z to 1 tensor z.
The actual quotient maps commute with multiplication and one. These identities
identify the restricted regular sequence with the strict quotient tower before
localization. Its locally surjective transition maps give the Roos triangle; the
strict scalar-unit quasi-isomorphism identifies its homotopy limit with the
completed regular single complex. Transport that triangle through the specified
right-derived sequence-limit comparison. The zero shifted coordinate and the
normalized strict-unit coordinates identify every projection with the actual
completed-ring projection. Transpose that projection through the finite derived
adjunction to obtain exactly constantCoefficientReductionMap. The sectionwise
identity hypothesis on b fixes the finite identifications. The proof also applies
to the empty scheme and the first quotient.
(blueprint: lem-pur-completed-unit-regular-sequence-limit). -/
theorem regularSequenceLimitComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u})
    (b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x) :
    ∃ c : integralConstantCoefficientObject l E W ≅
        (coefficientSequenceLimit l E W).obj (systemObject l E W),
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
  sorry

end WeilConjectures.CompletedUnitPullback
