# WeilConjectures.ReconstructedPairRefinement interface extraction

## Reason

The remaining coherence proof needs independently stated substeps referring to its
actual maps and types. Extract the existing definitions and proved invertibility
and origin helpers verbatim into a data module, then publicly re-export them from
the original module. This removes the import cycle for independent substep modules.
No statement, definition body, visibility, comparison normalization or hypothesis
changes. This is an interface extraction for proof decomposition, not a split to
avoid the compiler time limit.

## Old

The original module's complete prefix, from its copyright header through the end
of `Coherence`, directly defines all the declarations listed in
`def-pur-reconstructed-refinement-data.json`. Its first public imports are:

```lean
public import Sheaf.Paper.PurIntegralRepresentingPair
public import Sheaf.Paper.RingedRefinementCoefficientSquare
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.RefinementFiniteOriginEvaluation
```

The prefix is retained byte-for-byte in the new data module. The main theorem's
signature is retained verbatim:

```lean
theorem reconstructedPairRefinementCoherence : Coherence l E k C X Y f
```

## New

The identical prefix is now `lean/Sheaf/Paper/ReconstructedPairRefinementData.lean`,
followed only by the namespace closure. The original module begins with
`public import Sheaf.Paper.ReconstructedPairRefinementData` and privately imports
its five proof substeps. All original public declarations remain available under
the same fully qualified names and with the same signatures and bodies. The main
theorem is proved from those substeps and existing dependency laws.

## Users

`python3 tools/downstream.py Sheaf.Paper.ReconstructedPairRefinementCoherence`
reported `0 module(s) downstream`. The unfinished parent DAG dependencies and unit
route are retained. No parent or source-library declaration is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | A5 | Same public interfaces by re-export; proof decomposition only. |

## Status

landed 20261025T204354-L-2947874 2026-10-25 (merge of deliver/A5/Sheaf.Paper.ReconstructedPairRefinementCoherence)
