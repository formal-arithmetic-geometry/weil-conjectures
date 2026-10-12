/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLissePartition
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.EtaleLocallyConstantOpenPullback
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-!
# The reducible step for finite lisse partitions

Source: finite pushforward constructibility blueprint, step 2.
(blueprint: lem-weil-pbc-etale-lisse-partition-reducible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The reducible Noetherian induction step only uses partitions on proper closed subsets;
it does not require the generic-lissity hypothesis.

Source: blueprint `lem-weil-pbc-finite-pushforward-constructible-noetherian`, step 2.
(blueprint: lem-weil-pbc-etale-lisse-partition-reducible).

Proof: The nonempty closed subset T has finitely many irreducible components, by
Noetherianity of the closed subspace. List them as T_1,...,T_r. Because T is not
irreducible, every component is a proper closed subset of T. Apply the given hypothesis
to each component. For each stratum in component i, take the inverse image of the
complement of the closed subset T_1 union ... union T_{i-1}. This is an open subscheme
of the stratum; compose its open immersion with the old stratum immersion. Composition
preserves immersions. The images are the old images minus the earlier components,
so the resulting finite list is disjoint and covers T. Pullback composition identifies
the new sheaf with the open restriction of the old lisse sheaf. Restrict an etale
trivializing cover; the restriction comparison and the constant-sheaf pullback comparison
show local constancy, and the inverse-image geometric-stalk bijection shows finiteness.
Thus every new stratum is lisse. Empty differences can be kept as empty strata. -/
theorem nonempty_etaleLissePartition_of_reducible
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T : TopologicalSpace.Closeds X) (hne : (T : Set X).Nonempty)
    (hred : ¬ IsIrreducible (T : Set X))
    (ih : ∀ Z : TopologicalSpace.Closeds X, Z < T →
      Nonempty (EtaleLissePartition F (Z : Set X))) :
    Nonempty (EtaleLissePartition F (T : Set X)) := by sorry

end AlgebraicGeometry.Scheme
