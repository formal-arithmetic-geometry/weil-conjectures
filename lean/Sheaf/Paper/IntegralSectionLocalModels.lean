/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.CondensedConstantConstructibility

/-! # Finite scalar models under the normalized integral section comparison

Source: Bhatt--Scholze, Definition 6.8.10; integral constructibility bridge, step 7.
(blueprint: lem-sfb-integral-section-local-models).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The normalized section comparison preserves and reflects the stratified finite
scalar models of an individual module sheaf.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), coefficient
comparison in step 7 of lem-sfb-integral-constructible-completion-bridge.
(blueprint: lem-sfb-integral-section-local-models).

Proof: identify the two completed coefficient rings by their positive quotient
projections. The section-action equivalence retains the underlying abelian sheaf,
sections and restrictions. A finite presentation on the condensed point is a finite
matrix of global scalar sections. Evaluation at the point identifies these scalars
with the lifted valuation ring PbcIntegralRing; the chosen coefficient comparisons
send each scalar to its image in every quotient, so they preserve that matrix.
Exactness carries its cokernel to the completed constant realization of the same
finitely presented scalar module. Conversely, a finite scalar presentation gives a
finite presentation on the condensed point and hence that same local model.
The section-action equivalence and restriction of scalars along the normalized ring
isomorphism commute with inverse image to a stratum and with localization to a
pro-etale object. Replace each pro-etale cover by its generated covering sieve on
the terminal object to obtain the completed-model convention. In the reverse
direction, the covering sieve contains a generating pro-etale cover. Transport the
local cokernel isomorphisms on these members in the inverse equivalence. Keep the
same finite constructible stratification in both directions. Since X is Noetherian,
it is qcqs, so IsConstantModelConstructible selects exactly this stratified branch.
Zero modules, empty covers on the empty scheme and zero-rank presentations are
preserved by the same exact functors, so no nonemptiness assumption is needed. -/
theorem integralSectionLocalModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : AdicCompletion.Modules l E X) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M ↔
      Scheme.IsIntegralStratifiedFinitelyPresented X (Scheme.pbcIntegralDatum l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
            ((integralSectionFunctor l E X).obj M)) := by sorry

end AlgebraicGeometry.ProEtale
