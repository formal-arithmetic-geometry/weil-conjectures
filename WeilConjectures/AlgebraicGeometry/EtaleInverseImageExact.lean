/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Exactness of inverse image on abelian étale sheaves

## References

* Stacks Project, Tags 03Q1 and 0034
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Inverse image on abelian sheaves on the small étale site is exact, additive, preserves
kernels and cokernels, and carries short exact sequences to short exact sequences
(Stacks, Tags 03Q1 and 0034). -/
theorem upperStar_abelian_exact {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
    PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f) ∧
    (upperStar AddCommGrpCat.{u + 1} f).Additive ∧
    (∀ (G H : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : G ⟶ H),
      PreservesLimit (parallelPair φ 0) (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesColimit (parallelPair φ 0) (upperStar AddCommGrpCat.{u + 1} f)) ∧
    (∀ (S : ShortComplex (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})),
      S.ShortExact → (S.map (upperStar AddCommGrpCat.{u + 1} f)).ShortExact) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro G H φ
    exact ⟨inferInstance, inferInstance⟩
  · intro S hS
    exact hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)

end AlgebraicGeometry.Etale
