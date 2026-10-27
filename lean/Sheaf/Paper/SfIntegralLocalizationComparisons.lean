/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.SfLocalizationData
public import Sheaf.Paper.SfIntegralOrdinaryRecollementRealization

import Sheaf.Paper.SfExceptionalReductionTransitions
import Sheaf.Paper.CompletedPullbackReduction

/-! # Integral supported operations and normalized finite reductions

These data contain no quantitative Tor assertion. A family of finite localization
records is an input. The additional closed-pullback reduction is used to prove its
uniform integral Tor bound.
Source: current blueprint, supported localization, Integral stage and Other stages.
(blueprint: def-sf-integral-localization-comparison-data). -/

@[expose] public noncomputable section

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The qualitative integral localization data for a given finite family.
The fields are the original integral comparison fields; no Tor or limit condition
or existence assertion is built into this record. Closed pullback reduction is
included in addition to the original fields.
Source: current blueprint, prop-sf-localization-all-stages.proof.md, Integral stage.
(blueprint: def-sf-integral-localization-comparison-data). -/
structure SfIntegralLocalizationComparisonData
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (F : ∀ n : ℕ, SfFiniteLocalization l E n k i j) where
  supported : SfSupportedLocalization
    (sfIntegralConstructible l E X).ι (sfIntegralConstructible l E Z).ι
    (sfIntegralConstructible l E U).ι
  closed_pull : supported.iPull ≅
    @constructibleIntegralPullback l _ E _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull ≅
    @constructibleIntegralPullback l _ E _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  closed_push : supported.iPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  open_push : supported.jPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E U).ι ⋙ sfCompletedDerivedDirectImage l E j
  closed_reduction (n : ℕ) :
    supported.iPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E Z n ⋙ (F n).supported.iPush
  open_reduction (n : ℕ) :
    supported.jPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E U n ⋙ (F n).supported.jPush
  open_pull_reduction (n : ℕ) :
    supported.jPull ⋙ sfLocalizationConstructibleReduction l E U n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (F n).supported.jPull
  exceptional_reduction (n : ℕ) :
    supported.exceptional ⋙ sfLocalizationConstructibleReduction l E Z n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (F n).supported.exceptional
  exceptional_counit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.exceptionalAdjunction.counit.app K) =
      (closed_reduction n).hom.app (supported.exceptional.obj K) ≫
        (F n).supported.iPush.map ((exceptional_reduction n).hom.app K) ≫
        (F n).supported.exceptionalAdjunction.counit.app
          ((sfLocalizationConstructibleReduction l E X n).obj K)
  open_unit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.openAdjunction.unit.app K) ≫
      (open_reduction n).hom.app (supported.jPull.obj K) ≫
        (F n).supported.jPush.map ((open_pull_reduction n).hom.app K) =
      (F n).supported.openAdjunction.unit.app
        ((sfLocalizationConstructibleReduction l E X n).obj K)
  closed_pull_reduction (n : ℕ) :
    supported.iPull ⋙ sfLocalizationConstructibleReduction l E Z n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (F n).supported.iPull

/-- Realize the qualitative integral localization and compare it to a supplied finite family.

Source: current blueprint, prop-sf-localization-all-stages.proof.md, Integral stage,
especially the two reduction comparisons, and Other stages.
(blueprint: lem-sf-integral-localization-comparisons).

Proof: use the given ordinary integral recollement. Its restricted five functors and
three adjunctions are the supported operations. Transport its ordinary supported
triangle along the completed-pullback isomorphism on complete objects; the normalized
adjunction identifies its second map with the restricted open unit. Shifted Hom
orthogonality makes its boundary unique and natural. Closed full faithfulness gives
an invertible exceptional unit, and adjunction with open image gives exceptional-open
vanishing. The pullFunctor is the restriction of the specified integral pullback;
fullness identifies it with constructibleIntegralPullback. The two image functors
are literal restrictions of the completed direct images. Direct-image reduction on
these complete objects gives the closed and open reduction
isomorphisms. The K-flat pullback/reduction square gives both pullback reductions.
Restrict the counit transpose alphaOf of SfExceptionalReduction to constructibles.
The exceptionalReductionTransitionComparison theorem makes it invertible and gives
precisely the displayed exceptional-counit and open-unit equations. Identify its finite
right adjoint with the one in F n by the unique isomorphism preserving the counit;
ordinary left adjoint comparisons similarly identify the remaining finite functors.
This conjugates the comparison equations to the supplied F n, without choosing new
adjunction maps. None of these steps assumes finite Tor amplitude or finite
cohomological dimension. Zero objects and empty open or closed pieces satisfy the
same adjunction and uniqueness argument. -/
theorem sfIntegralLocalizationComparisons
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : ∀ n : ℕ, SfFiniteLocalization l E n k i j)
    (O : SfIntegralOrdinaryRecollement l E i j) :
    Nonempty (SfIntegralLocalizationComparisonData l E k hl t i j F) := by sorry

end WeilConjectures
