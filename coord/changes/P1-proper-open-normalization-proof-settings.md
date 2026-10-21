# Proper/open normalization: private proof constructions and scoped settings

## Reason

The proof of `properOpenComparisonNormalization` uses generic categorical calculations
before specializing to the strict-tower derived categories. This prevents expensive
unfolding of concrete derived functors and category implementations. Static preflight
requires this record for the added private data and section-level commands.

## Old

The normalization theorem was `sorry`. Its public statement, all other existing public
statements and definitions, and the public imports are preserved. The existing file-wide
settings and the existing local attributes after the normalization section are preserved.
There were no `NormalizationProof` or `PublicNormalization` sections.

## New

The two new proof sections use these scoped settings:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

`NormalizationProof` marks `G R J adj jAdj towers_hasDerivedCategory` locally irreducible,
then marks `gComp jComp jCongr openToR` locally irreducible. `PublicNormalization` marks
`G R J adj jAdj` locally irreducible. Every such attribute is explicitly local and all
section-level options end with their section. Generic private helpers use declaration-
scoped `set_option ... false in` for the same two transparency options.

Four private data declarations have explicit constructions and no postponed data:
`derivedCategoryInstance` names the existing category instance; `alphaComposite`,
`extensionComposite`, and `restrictionComposite` give the categorical composites used
by the existing public definitions. Their defining equations are proved by reflexivity.
All other new helpers are private proved theorems. None occurs in a public signature
or in the body of an existing public definition.

The removed imports are private proof imports; report.md lists them individually.
Mathlib's mates module is the only new private import. No global option, persistent
attribute, public notation, public instance, public definition or signature changes.
The normalization theorem alone disables the unused-variable linter, preserving its
existing named pullback-proof binder in the unchanged statement.

## Users

`tools/downstream.py Sheaf.Paper.ProperOpenTowerComparison --uses
properOpenComparisonNormalization properOpenTowerComparison properOpenRestrictionMap`
reported zero downstream importers and no external textual users. The node's existing
DAG parents still require its statement; none is withdrawn.

| Module | Current holder | Effect |
| --- | --- | --- |
| `Sheaf.Paper.ProperOpenTowerComparison` | P1 | Proved normalization, private helpers and scoped settings. |

No consumer adaptation is needed. The two node copies update only proof descriptions,
proof dependencies, proof origin and the parent's obsolete tool-use entries.

## Status

landed 20261021T011028-L-2030013 2026-10-21 (merge of deliver/P1/Sheaf.Paper.ProperOpenTowerComparison)
