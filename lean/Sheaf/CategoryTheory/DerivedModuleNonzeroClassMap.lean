module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Nonzero homology classes give nonzero rank-one derived morphisms.
Source: Stacks Project, Tag 064B.
-/

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- A nonzero homology class yields a nonzero rank-one derived morphism.
Source: Stacks Project, Tag 064B, applied to the projective rank-one single complex.
(blueprint: new-stage3-derived-module-rank-one-nonzero-map-chain)

Proof in words: choose a complex C and an isomorphism Q(C) ≅ K, and transport x
through the homology isomorphism. Choose a cycle z representing that class.
The linear map ULift S → C.X n sending ULift.up s to s • z defines a chain map
from the rank-one single complex into C[n], since z is a cycle. After localization
and transport along Q(C[n]) ≅ K[n], its degree-zero homology map sends the lifted
unit to x under the canonical homology identifications. A zero derived morphism
induces the zero homology map, contradicting hx. This proves nonvanishing.
-/
theorem derivedModule_nonzero_class_map
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (K : DerivedCategory (ModuleCat.{max w vH} S)) (n : ℤ)
    (x : ((DerivedCategory.homologyFunctor
      (ModuleCat.{max w vH} S) n).obj K)) (hx : x ≠ 0) :
    ∃ f :
      (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ K⟦n⟧, f ≠ 0 := by
  sorry

end CategoryTheory
