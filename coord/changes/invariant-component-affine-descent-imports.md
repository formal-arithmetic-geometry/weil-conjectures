# Sheaf.AlgebraicGeometry.InvariantComponentAffineDescent public imports

## Reason

The proof and the unchanged statements do not use any declaration from
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, or geometric integrality or
irreducibility. Keep only the imports required by the statements. No declaration signature,
attribute, instance, or definition body changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| No direct importers | none | An exact import search in both lean/ and quarantine/ returned none. |

The item is held by A3. No other existing module is edited. No target statement or definition
used by a target changes. The parent DAG proofs that may eventually import this module retain
all its existing declarations with their original signatures; only the incidental reexports
of unused imports are removed. There are no direct importers to compile or adapt.

## Status

landed 20261026T091030-L-3300277 2026-10-26 (merge of deliver/A3/Sheaf.AlgebraicGeometry.InvariantComponentAffineDescent)
