module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.ULift

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- Every nonzero derived module object receives a nonzero map from the rank-one
single complex into an integer shift. Source: Stacks Project, Tag 0F5X, first paragraph.
(blueprint: new-stage3-derived-module-rank-one-nonzero-map)

Proof in words: represent the object by a complex. Nonvanishing of the object implies
nonvanishing of some cohomology module, since an acyclic representative is zero in the
derived category. A nonzero cohomology class is represented by a cycle. Evaluation at
the lifted unit turns that cycle into a chain map from the free rank-one single complex
to the corresponding shift. The map is nonzero because its cohomology class is nonzero;
the K-projective localization calculation identifies this chain map with a derived map.
-/
theorem derivedModule_rankOne_nonzero_map
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (K : DerivedCategory (ModuleCat.{max w vH} S)) (hK : ¬ IsZero K) :
    ∃ n : ℤ, ∃ f :
      (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ K⟦n⟧, f ≠ 0 := by
  sorry

end CategoryTheory
