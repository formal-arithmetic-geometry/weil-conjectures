/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Exterior powers shifted by a locally constant rank

## References

* [Stacks, Duality for Schemes, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
-/

@[expose] public section

universe uE

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- The open and closed rank-`n` stratum. (Stacks, Tag 0BR0) -/
def exteriorRankOpen {X : Scheme.{uE}} (r : LocallyConstant X ℕ) (n : ℕ) : X.Opens :=
  ⟨{x | r x = n}, r.isLocallyConstant.isOpen_fiber n⟩

/-- Degree `n` is the extension by zero, from the rank-`n` stratum, of the top exterior
power; negative degrees are zero. (Stacks, Tag 0BR0) -/
noncomputable def locallyRankedExteriorTerm {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) (n : ℤ) : X.Modules :=
  if 0 ≤ n then
    (pushforward (exteriorRankOpen r n.toNat).ι).obj
      (exteriorPower
        ((restrictFunctor (exteriorRankOpen r n.toNat).ι).obj M) n.toNat)
  else 0

/-- The complex `wedge^r M[-r]`: degree `n` is supported on the rank-`n` stratum and every
differential is zero. (Stacks, Tag 0BR0) -/
noncomputable def locallyRankedExteriorComplex {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) : CochainComplex X.Modules ℤ :=
  CochainComplex.of (locallyRankedExteriorTerm M r) (fun _ => 0)
    (fun _ => zero_comp)

end AlgebraicGeometry.Scheme.Modules
