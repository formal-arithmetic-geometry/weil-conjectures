module

public import Sheaf.Paper.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

@[expose] public section

universe u₁

open CategoryTheory

namespace AlgebraicGeometry

/-- The abelian-group part of hypercover cohomology comparison.
Source: Stacks Project, Tag 01H0; blueprint order 949.
The injective-resolution double-complex comparison, refinement independence, and finite
successive lifting argument establish the colimit universal property.
(blueprint: thm-weil-pbc-hypercover-cohomology-abelian-part) -/
theorem hypercover_cohomology_abelian_part (X : Scheme.{u₁}) [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) := by
  sorry

end AlgebraicGeometry
