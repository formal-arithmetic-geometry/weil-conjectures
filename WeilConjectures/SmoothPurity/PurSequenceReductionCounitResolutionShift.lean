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

/- Added hypothesis `hA`: without it the data pins `A.reductionCounit` only up to a natural
automorphism of its target whose finite evaluations are identities, and such an automorphism
need not commute with the shifts, so the square was not determined. `hA` asks that
`A.reductionCounit` be compatible with shifts (`NatTrans.CommShift`) for `D.reduction_shift`
on `S.reduction` and the canonical shifts on `DerivedCategory.Q` and the termwise pullback.
The square is then the component of this compatibility at `Q`.
-/

set_option linter.unusedVariables false in
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
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i))
    (hA : letI := D.reduction_shift
      NatTrans.CommShift A.reductionCounit ℤ) :
    letI := D.reduction_shift
    ((DerivedCategory.Q ⋙ S.reduction).commShiftIso r).hom.app Q ≫
        (A.reductionCounit.app Q)⟦r⟧' =
      A.reductionCounit.app (Q⟦r⟧) ≫
        ((O.pullback.mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q).commShiftIso r).hom.app Q := by
  let := D.reduction_shift
  exact NatTrans.shift_app_comm A.reductionCounit r Q

end WeilConjectures
