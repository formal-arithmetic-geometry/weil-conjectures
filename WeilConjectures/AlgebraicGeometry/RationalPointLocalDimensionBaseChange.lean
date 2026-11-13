/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.RationalPointTopologicalLocalDimensionBaseChange
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension

/-!
# Local dimension of rational points under field extension

## References

* [Stacks Project, Tag 00P4](https://stacks.math.columbia.edu/tag/00P4)
* [Stacks Project, Tag 00OU](https://stacks.math.columbia.edu/tag/00OU)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Local-ring dimension at a rational point is unchanged by extending the ground field. -/
theorem ringKrullDim_rationalPoint_field_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K]
    (q : Spec (.of K) ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hq : q ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _)
    (hqp : q ≫ pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p) :
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
      ringKrullDim ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk
          (q (IsLocalRing.closedPoint K))) := by
  have hleft := ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt f p hp
  calc
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
        topologicalKrullDimAt (p (IsLocalRing.closedPoint k)) :=
      hleft
    _ = topologicalKrullDimAt (q (IsLocalRing.closedPoint K)) :=
      topologicalKrullDimAt_rationalPoint_field_baseChange f p hp K q hq hqp
    _ = ringKrullDim ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk
          (q (IsLocalRing.closedPoint K))) :=
      (ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q hq).symm

end AlgebraicGeometry
