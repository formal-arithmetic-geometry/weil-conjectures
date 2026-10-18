# CategoryTheory.Abelian.LeftResolution.totalizedAugmentation_natural_quasiIso

## Reason

The existing source module already proves both conjuncts, so the separate holed
`Sheaf.Algebra.Homology.LeftResolutionBicomplexTotalExists` wrapper is unnecessary.
Remove its public import as required by proof pruning. Also remove the direct
imports of Basic, BicomplexRows and BicomplexColumns, which the retained source
module imports transitively. The theorem's statement and all definitions are unchanged.

This record documents the public import removal requested by the dry-run preflight;
no theorem or definition is being replaced. In particular, no target's statement or
underlying definitions change. The total-existence wrapper's declaration ceases to be
re-exported from this module. Its construction is already available through proved
source instances, and no downstream consumer of this module requires adaptation.

## Old

```lean
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
public import Sheaf.Algebra.Homology.LeftResolutionBicomplexTotalExists
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
```

## New

```lean
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
```

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.LeftResolutionTotalizedAugmentation
--uses totalizedAugmentation_natural_quasiIso` reports 0 downstream modules and
only the theorem's own declaration as a textual use. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LeftResolutionTotalizedAugmentation | E6 | Prove the unchanged theorem; prune unnecessary imports. |

## Status

landed 20261018T140715-L-3103918 2026-10-18 (merge of deliver/E6/Sheaf.Algebra.Homology.LeftResolutionTotalizedAugmentation)
