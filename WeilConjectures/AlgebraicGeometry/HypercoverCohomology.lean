/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Cohomology of a sheaf as a colimit over hypercovers

The étale cohomology of a sheaf on a qcqs scheme is the colimit of the cohomology of its
sections over finite split étale hypercovers.
-/

@[expose] public section

universe u₁

open CategoryTheory

namespace AlgebraicGeometry

/-- For a qcqs scheme `X`, étale cohomology of abelian sheaves and of sheaves of modules over any
ring `R` is the colimit over finite split étale hypercovers of the hypercover cohomology. -/
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  sorry

end AlgebraicGeometry
