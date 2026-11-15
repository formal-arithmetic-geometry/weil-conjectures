/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Compactification.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Compactification.NagataCompactification

/-!
# Compactifiability over a field

A separated finite-type morphism between finite-type schemes over a field admits a
compactification (`hasCompactification_of_finiteType_over_field`).

## Implementation details

Compactifiability is expressed by the existing `AlgebraicGeometry.Compactification` and
`AlgebraicGeometry.HasCompactification`: a scheme `Z`, an open immersion `i`, a proper
morphism `g`, and the equality `f = i ≫ g`. No new compactifiability predicate is introduced.

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tags 0ATT, 0F41, 01OV, 01T6, 01OY
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite-type morphism between finite-type schemes over a field is compactifiable:
it factors as an open immersion followed by a proper morphism. -/
theorem hasCompactification_of_finiteType_over_field
    (k : Type u) [Field k] (X S : Scheme.{u})
    [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasCompactification f := by
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  exact (NagataCompactification f).hasCompactification

end AlgebraicGeometry
