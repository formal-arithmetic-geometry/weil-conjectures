# AlgebraicGeometry.exists_etale_affine_cover_stratification

## Reason

Repair X-09b43 D1: restore the original geometric dependency imports and public exports,
delete both clause-restatement modules, and prove the theorem by separated stratification,
fibre-product common refinement, affine refinement, and closed-overlap affine gluing.
Add a proof-only import for compatibility of section restriction with open-subscheme
sections. There is no public interface change relative to the library baseline.

## Old

Original library imports (before the rejected delivery):

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces
import Sheaf.AlgebraicGeometry.SeparatedAffineCoverCriterion
import WeilConjectures.ConstructibleSheaf.Refinement
```

The rejected delivery instead kept only the first public import and imported
`Sheaf.AlgebraicGeometry.EtaleAffineCoverPartition` and
`Sheaf.AlgebraicGeometry.EtaleAffineCoverSeparated` for the two sorry restatements.

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces
import Sheaf.AlgebraicGeometry.SeparatedAffineCoverCriterion
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
```

The declaration's signature is identical to the original library signature; only the proof
and private proved helpers change. Both rejected modules and their nodes are removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | T1 | Full geometric proof; signature and original public imports preserved. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unchanged | Same public declaration and exports; no adaptation required. |

## Status

landed 20261012T085339-L-39704 2026-10-12 (merge of deliver/T1/Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification)
