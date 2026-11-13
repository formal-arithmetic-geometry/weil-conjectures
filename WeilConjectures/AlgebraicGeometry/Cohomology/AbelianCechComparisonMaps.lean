/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonCore
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonNormalization

/-! # Objectwise canonical abelian Čech comparisons

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- The quotient of beta by alpha exists for one coefficient sheaf, with its
canonical degree-zero value. Naturality in different coefficient sheaves and
compatibility with connecting maps are separate statements.

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2. -/
theorem exists_abelianCechComparison_maps
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hα : ∀ I : InjectiveResolution F, QuasiIso (abelianCechAlpha U I)) :
    ∃ c : ∀ q, (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F,
      (∀ q, IsAbelianCechComparison U F q (c q)) ∧
      c 0 = (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv.app F ≫
        (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv.app F := by
  classical
  have hq := exists_abelianCechComparison_core U F hα
  choose c hc using hq
  refine ⟨c, hc, ?_⟩
  exact abelianCechComparison_zero_normalization U hcover F (c 0) (hc 0)
end AlgebraicGeometry.Scheme.Modules
