/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.IntegralSupportNormalizationData

/-! # Projection and shift normalization of the canonical closed comparison

Source: smooth-purity localization, integral support comparison; Stacks 0941 and 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical closed-image comparison has the strict projection formula and the
canonical signed shift. These are properties of closedAlpha itself, before choosing
its inverse or restricting direct image to the constructible subcategories.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md, integral
support comparison; Stacks 0A07 and 0941, and the normalized strict Roos comparison.
(blueprint: lem-sf-closed-alpha-normalization).

Proof: restriction of scalars and closed direct image both evaluate on the same
fiber product, and their coefficient actions agree by the finite quotient projection
identity for the completed structural map. This gives a strict natural comparison
of the quotient diagrams, commuting with every transition. Its adjunction transpose
is closedReduction: C.pull_model identifies both maps on one flat-term K-flat
representative, with the actual quotient augmentation and zero homotopy coordinate.
Taking right-adjunction conjugates therefore identifies closedLimit with this
sectionwise direct-image/total-limit comparison. The n-th projection of that
comparison is the derived scalar-restriction comparison followed by the inverse
of the system direct-image evaluation comparison. Compose with direct image of the
actual reconstruction unit. Naturality of the projections gives exactly the displayed
formula, with the original unit and all three maps in their specified directions.
This is a calculation of the strict comparison before evaluation; no faithfulness
of derived evaluation is asserted. Each ordinary comparison acts degreewise and
commutes with shifted differentials. In the Roos complex the degree-r shift changes
the homotopy coordinate by (-1)^r and leaves the projection coordinate unchanged.
The zero homotopy coordinate of the unit is preserved. Consequently the unit, limit
comparison and their composite closedAlpha commute with precisely the specified
shifts. Descent along good-complex localization and restriction to the full
constructible category preserve both equations, including zero and empty inputs. -/
theorem closedAlpha_normalization {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (C : SfOrdinaryIntegralComparison l E i)
    [IsIso (closedReduction l E i C)] :
    NatTrans.CommShift (closedAlpha l E i C) ℤ ∧
    ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
      (closedAlpha l E i C).app K ≫
        (coefficientSequenceProjection l E X n).app
          ((FrobeniusExchange.systemDirect l E i).obj
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) =
      (sfCompletedDerivedDirectImage l E i).map
        (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj ≫
          (coefficientSequenceProjection l E Z n).app
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
        (sfDerivedRestrictionComparison l E i n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Z n).obj
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
        (scalarReductionDerivedRestriction l E X n).map
          ((directEvaluationIso l E i n).inv.app
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) := by sorry

end WeilConjectures.IntegralSupportNormalization
