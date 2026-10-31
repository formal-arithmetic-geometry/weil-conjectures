/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceProductDerivedComparison
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceRelationsDerivedComparison

/-! # Localization of the two coinduced products

Source: Stacks 079P, 07A6 and 015F.
(blueprint: lem-coef-sequence-derived-coinduced-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

/-- Localization identifies the ordinary coinduced products and both their maps
with the products formed using the specified derived adjunctions.
Source: Stacks 079P, 07A6 and 015F; step 3 of the locally finite coinduced
resolution in lem-coef-sequence-derived-evaluation-full.
(blueprint: lem-coef-sequence-derived-coinduced-comparison).

Proof: resolve every complex K_n independently by K-injectives, and independently
resolve every Res(K_n). Exact coinduction, being right adjoint to exact evaluation,
preserves K-injectives. The product of these coinduced K-injectives represents their
product in the derived category. The maps from the corresponding products formed
from K are quasi-isomorphisms: evaluation at any level m sees only finitely many
nonzero factors, and finite products commute with cohomology. Identify each factor
by the canonical exact-functor factorizations. The product universal property gives
the two asserted isomorphisms. For the augmentation, project to n and use the formula
for the unit of the localized adjunction; it is the localized original unit followed
by those factorizations. For the difference, project to n, transpose by the derived
adjunction, and use the localization formula for the actual coefficient transition,
together with naturality of the evaluation and scalar-restriction factorizations.
Both expressions become the same difference of adjacent transition composites.
Products jointly detect these equalities. Restrictions of scalars are exact but
are never asserted to preserve K-injectives. All constructions are valid for
unbounded complexes, the zero object, identity transitions, and the empty site. -/
theorem complexSequence_derivedComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃ (a : DerivedCategory.Q.obj (complexProduct l E W K) ≅
        derivedProduct l E W (DerivedCategory.Q.obj K))
      (b : DerivedCategory.Q.obj (complexRelations l E W K) ≅
        derivedRelations l E W (DerivedCategory.Q.obj K)),
      DerivedCategory.Q.map (complexAugmentation l E W K) ≫ a.hom =
        derivedAugmentation l E W (DerivedCategory.Q.obj K) ∧
      DerivedCategory.Q.map (complexDifference l E W K) ≫ b.hom =
          a.hom ≫ derivedDifference l E W (DerivedCategory.Q.obj K) := by
  obtain ⟨a, ha⟩ := complexProduct_derivedComparison l E W K
  obtain ⟨b, hb⟩ := complexRelations_derivedComparison l E W K a ha
  exact ⟨a, b, ha, hb⟩

end WeilConjectures.CoefficientCoinduction
