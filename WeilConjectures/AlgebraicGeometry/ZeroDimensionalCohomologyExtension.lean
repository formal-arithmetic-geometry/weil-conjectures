/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyRest

/-! # Étale cohomology in dimension zero

## References

* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
-/

@[expose] public section


universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The underlying point type of a separated finite-type zero-dimensional scheme
over an algebraically closed field is finite.
-/
theorem zero_dimensional_etale_finite
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) : Finite C := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact finite_of_compact_of_discrete



end AlgebraicGeometry
