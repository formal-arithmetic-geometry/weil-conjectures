# AlgebraicGeometry.exists_affine_etale_split_neighbourhood

## Reason

Prove the existing statement from the unramified decomposition. The delivered file adopts
Lean's required module header and public section. Its four Mathlib statement imports are
public; the decomposition and other proof tools are private imports. Remove the unused
EtaleFibreDiscreteSeparablePoints proof dependency and use the already proved quasi-finite
fibre API instead. No existing declaration signature or instance is changed. The required exposed public
section exports the existing theorem; all new helpers are proved and private. The now
unneeded `warn.sorry false` option is removed.

## Old

```lean
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition

```

The existing theorem's signature is unchanged.

## New

```lean
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

```

The existing theorem is in `@[expose] public section`; the helpers are private theorems.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineEtaleSplitNeighbourhood | U4 | Assigned item; one proof filled. |

There are no current direct Lean importers of the item. Its DAG parent continues to use
exactly the same statement; no parent or other existing module is changed. No changes
are made to any adopted source-library declaration or public import.

## Status

landed 20261026T083215-L-2296247 2026-10-26 (merge of deliver/U4/Sheaf.AlgebraicGeometry.AffineEtaleSplitNeighbourhood)
