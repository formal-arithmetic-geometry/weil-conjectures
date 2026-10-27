# Constant-extension return and pullback proof imports

## Reason

The assigned parent must import its stated sheet-return and pullback-return results.
ConstantExtensionReturnData and ConstantExtensionPullbackReturnResidue still publicly
imported the parent theorem module even after H5 extracted all their required definitions
into ConstantExtensionWeilHeartData. Those reverse imports make the parent proof cyclic.
Both modules are unclaimed in the local claim snapshot. Replace only those imports with
the existing definition owner. All declarations, signatures, attributes and bodies stay
byte for byte identical. This continues H5's landed data relocation; no definition is
changed, moved, or replaced and no source-library module is edited.

## Old

In both Sheaf.Paper.ConstantExtensionReturnData and
Sheaf.Paper.ConstantExtensionPullbackReturnResidue:

```lean
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
```

## New

In both modules:

```lean
public import Sheaf.Paper.ConstantExtensionWeilHeartData
```

## Users

The prescribed tools/downstream.py scan of ConstantExtensionReturnData lists the four
modules below; the corresponding scan of ConstantExtensionPullbackReturnResidue lists
none. A --uses scan finds no use of constantExtensionWeilHeartEquivalence in either
consumer set; a source scan also finds no use of constantExtensionCyclicSheets. All
required data remain publicly available from the same definition owner. The two theorem
names cease to be incidental transitive exports of these dependency modules; their
proper theorem module remains their public home.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | E1 | Imports its stated return and pullback dependencies without a cycle; same public signatures. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Only the public import above changes; definitions and proofs identical. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Only the public import above changes; definitions and proofs identical. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | All used names remain public; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | All used names remain public; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | All used names remain public; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | All used names remain public; no adaptation. |

## Status

landed 20261026T001308-L-4181986 2026-10-26 (merge of deliver/E1/Sheaf.Paper.ConstantExtensionWeilHeartEquivalence)
