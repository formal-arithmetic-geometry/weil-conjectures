# ProjectiveDimensionSESKernel public import migration

## Reason

The quarantined module imported `Sheaf.RingTheory.GlobalDimension`, whose duplicate
`Ring.HasFiniteGlobalDimension` declarations conflict with the adopted upstream
`WeilConjectures.RingTheory.GlobalDimension` declarations re-exported by the bounded
resolution bridge. Migrate this module to the upstream API so it compiles after the
upstream synchronization.

## Old

```lean
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import WeilConjectures.RingTheory.ProjectiveResolutionExtCharacterization
```

## New

```lean
public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
```

The theorem signature and declaration visibility are unchanged. The proof now uses
`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE` from the adopted
upstream bounded-resolution module and Mathlib's short-exact projective-dimension
lemma.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ProjectiveDimensionSESKernel | S4 | restored with upstream imports |

There are no direct active or quarantined importers: a search of all Lean sources
under both `lean/` and `quarantine/` found no import of this module and no use of
`Ring.projectiveDimensionLE_of_shortExact` outside the module itself. The downstream
script reports the item as unknown because its active source is quarantined. No
consumer adaptation is required; the node and theorem are preserved for planned users.

## Status

landed 20261020T151231-L-2651351 2026-10-20 (merge of deliver/S4/Sheaf.RingTheory.ProjectiveDimensionSESKernel)
