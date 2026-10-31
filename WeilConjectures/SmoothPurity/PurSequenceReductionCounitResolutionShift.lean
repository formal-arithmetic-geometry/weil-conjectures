/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurSequenceKFlatComparisonData
public import WeilConjectures.SixFunctors.Supporting.PurReductionLimitShiftData

/-! # Resolution-level shift compatibility for the quotient counit

Source: Stacks 06YY and 0G7D; the normalized representative equation.
(blueprint: lem-pur-sequence-reduction-counit-resolution-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/- STATEMENT-DISPUTED: the hypotheses do not determine the displayed square.
`D.unit_shift` and `D.counit_shift` constrain `D.reduction_shift` only through
the independently supplied adjunction
`S.adjunction : S.reduction ⊣ coefficientSequenceLimit`, whose unit is
`𝟭 ⟶ S.reduction ⋙ coefficientSequenceLimit` and whose counit is
`coefficientSequenceLimit ⋙ S.reduction ⟶ 𝟭`. Neither is the left-derived
counit
`A.reductionCounit : DerivedCategory.Q ⋙ S.reduction ⟶
O.pullback.mapHomologicalComplex _ ⋙ DerivedCategory.Q`, and no field ties
them to it or to `O`. The field `O.limit` is an isomorphism of underived
sequence functors, and no field states its derived comparison with
`A.reductionCounit`. Likewise, `A.representative` only says that
`A.reductionCounit.app Q` is the hom of some isomorphism carrying a finite
presentation; it does not relate that isomorphism to `S.adjunction`. Thus the
finite equations `D.finite_shift_model`, `D.reduction_shift_evaluation`, and
the representative presentation cannot be lifted to equality of these
whole-system maps; `CoefficientDerivedSystemFibers.isIso_iff_evaluations`
detects invertibility only. A right-Kan construction supplies a shift for
`A.reductionCounit`, but the requested theorem additionally asserts that this
shift is the separately chosen `D.reduction_shift`. Repair requires a
whole-system normalization field (for example the unit of `S.adjunction`
against `A.reductionCounit`, or the derived form of `O.limit`), or the
requested square as data. Concretely, the fields only pin `A.reductionCounit`
up to a natural automorphism `theta` of the target functor
`O.pullback.mapHomologicalComplex _ ⋙ DerivedCategory.Q` whose finite
evaluations are identities: postcomposing `A.reductionCounit` and `A.ε` with
such a `theta` keeps `comparison`, both left-derived fields and `unique`, and
`representative` holds with `e ≪≫ theta.app Q`, since
`CoefficientReductionPresentation` constrains `e` only through its finite
evaluations. The displayed square then changes by `theta`, and no field forces
`theta` to commute with the shifts. So the missing normalization is a gap in the
supplied data (no field excludes such `theta`), not an omitted cancellation
lemma.
-/

/-- The normalized quotient counit has the prescribed shift square on every
resolving representative. This is the representative calculation before
localization; its proof uses the shifted tensor presentation and the signed
termwise reindexing.
Source: Stacks sites-cohomology.tex, Tags 06YY and 0G7D.
(blueprint: lem-pur-sequence-reduction-counit-resolution-shift).
-/
theorem purSequenceReductionCounitResolutionShift
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : PurReductionLimitShiftData l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) :
    letI := D.reduction_shift
    ((DerivedCategory.Q ⋙ S.reduction).commShiftIso r).hom.app Q ≫
        (A.reductionCounit.app Q)⟦r⟧' =
      A.reductionCounit.app (Q⟦r⟧) ≫
        ((O.pullback.mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q).commShiftIso r).hom.app Q := by
  sorry

end WeilConjectures
