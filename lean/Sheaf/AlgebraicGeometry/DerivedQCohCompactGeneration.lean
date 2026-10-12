/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
import Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration
import Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives
import Sheaf.AlgebraicGeometry.PerfectObjectCompact
import Sheaf.CategoryTheory.CompactObject
import Sheaf.CategoryTheory.WeakTriangulatedGenerator

/-! # Compact generation of the quasi-coherent derived category

Source: Stacks Project, Derived Categories of Schemes, Theorem 36.15.3 (Tag 09IS),
and Derived Categories, Definition 13.37.5 (Tag 09SQ)
(blueprint: lem-pc-derived-qcoh-compact-generation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact quasi-separated scheme, the full subcategory of complexes with
quasi-coherent cohomology is compactly generated, with its inherited triangulated structure.
Source: Stacks Project, Tag 09IS and Tag 09SQ
(blueprint: lem-pc-derived-qcoh-compact-generation).

Proof:
1. By `lem-pc-derived-qcoh-perfect-generation`, perfect complexes generate under shifts,
cones, retracts and arbitrary direct sums.
2. By `lem-pc-perfect-object-compact` and `lem-pc-perfect-complexes-compact-set`, choose
set-indexed representatives of the perfect complexes, all compact. Their coproduct exists
by `lem-pc-derived-qcoh-direct-sums`. If all maps from this coproduct into shifts of K
vanish, all maps from each representative into shifts of K vanish. The objects A such that
Hom(A[m], K) vanishes for all integers m form a strictly full subcategory closed under
shifts, retracts and sums. Closure under cones follows from exactness of Hom out of a
triangle (`lem-weil-pbc-hom-out-of-triangle-exact` (ii)): a map from the cone factors through
the shifted first object and hence is zero. Step 1 makes this subcategory the whole category;
thus the identity of K is zero and K is zero. The coproduct is therefore a weak generator
(`def-pc-generators`).
3. Arbitrary direct sums exist by `lem-pc-derived-qcoh-direct-sums`; the family of Step 2
therefore satisfies `def-pc-compactly-generated`, using `def-pc-compact-object`.
The triangulated structure is inherited from D(O_X), since quasi-coherent cohomology is
stable under shifts and extensions and contains zero. -/
theorem schemeDerivedQCoh_compactlyGenerated (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ htri : (schemeDerivedQCohProperty X).IsTriangulated,
      letI := htri
      ∃ hsums : HasCoproducts.{u} (schemeDerivedQCohCategory X),
        letI := hsums
        IsCompactlyGeneratedTriangulated.{u} (schemeDerivedQCohCategory X) := by
  sorry

end AlgebraicGeometry
