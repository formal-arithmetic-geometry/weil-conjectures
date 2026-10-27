/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.PurSequenceKFlatComparisonData

import Sheaf.Algebra.Homology.StrictCoefficientTensorDescent

/-! # Descent of the specified quotient-sequence shifts

Source: Stacks 06YY, 0G7D and 012Z.
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

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The universal comparison preserves the specified ordinary shifts and the canonical
finite computation maps.
Source: Stacks, sites-cohomology.tex, Tags 06YY and 0G7D; homology.tex, Tag 012Z;
steps 6 and 7 of lem-pur-sequence-kflat-comparison-shifts.
(blueprint: lem-pur-sequence-reduction-shifts).

Proof: additive ordinary pullback commutes with cochain shifts by identity on reindexed
terms. Its shifted differential is (-1)^r times the original mapped differential.
The same computation applies to every finite scalar extension. Naturality of the
ordinary quotient transformations gives their shift squares before localization.
The tensor shift isomorphism shows that resolving complexes stay resolving under
shifts: tensor with a shifted K-flat complex is a shift of an acyclic tensor, flat
terms reindex, and shifted quasi-isomorphisms are quasi-isomorphisms.
Descend the identity-on-terms comparisons through this resolving class. Universal
uniqueness gives the shift structure on A.L and on S.reduction, characterized by their
counit squares. The comparison A.alpha satisfies that counit equation, so cancellation
on resolving representatives gives its shift square. Apply exact evaluation to those
squares and the finite normalization in A.representative: uniqueness gives the finite
resolution square and the reductionEvaluation shift square on all derived inputs.
At shift zero all term maps are identity; for a sum of shifts they are still identity,
and the differential signs multiply. Uniqueness extends the zero and addition equations
to the localization, giving CommShift (and hence inverse-shift coherence). -/
theorem purSequenceReductionShifts
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O) :
    Nonempty (PurSequenceKFlatShiftComparison l E W S O A) := by sorry

end WeilConjectures
