# WeilConjectures.FiniteRestrictionNaturality diagram models

## Reason

The remaining naturality theorem contains two independent arguments: strict-system
transport and constructibility of completed vertices. Their new theorem modules need
the existing diagrams and transport maps, while the main theorem imports those modules.
Move the existing constructions to a models module to avoid an import cycle. This is
an argument decomposition, not a response to a compile-time limit.

## Old

The construction declarations were defined in
`Sheaf.Paper.FiniteRestrictionDiagramNaturality`, whose public imports were:

```lean
public import Sheaf.Paper.FiniteCounitRestrictionTowers
public import Sheaf.Paper.PodCompletionReindexModels
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.CategoryTheory.CommSq
```

## New

The same construction declarations, from `canonicalSiteSmall` through `completed`,
are defined in `Sheaf.Paper.FiniteRestrictionDiagramModels`. Their names, signatures,
attributes and bodies are identical. The proved private product helper moves with
`sum_existsUnique`; the private square-image and square-restriction helpers stay in
the theorem module. Construction docstrings now cite the new definition owner.
The theorem module re-exports every former public prerequisite and construction via:

```lean
public import Sheaf.Paper.FiniteRestrictionDiagramModels
```

The three public naturality theorems stay in the original module with identical
signatures. Only the proof of `finiteRestrictionDiagramNaturality` changes, combining
two strictly smaller statements with finite-point finiteness, completion reindexing
laws and functorial preservation of commutative squares. No definition or theorem
changes its mathematical meaning, and no source-library module is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | S2 | Re-exports models and combines the argument steps. |
| Sheaf.Paper.FiniteRestrictionDiagramModels | S2, new | Owns the relocated, identical constructions. |
| Sheaf.Paper.FiniteRestrictionStrictTransport | S2, new | States only strict transport, before completion. |
| Sheaf.Paper.FiniteRestrictionConstructibleVertices | S2, new | States only completed object constructibility. |

`tools/downstream.py Sheaf.Paper.FiniteRestrictionDiagramNaturality` reports zero
current library users. The DAG attachment is retained: its three final naturality
theorems stay attached to the original node. The construction names are attached to
the new model node. Parents of the original node need no statement change. Existing
constructor and definition bodies are copied without alteration, so every existing
signature is definitionally unchanged, including any target using these constructions.

## Status

landed 20261025T164232-L-976036 2026-10-25 (merge of deliver/S2/Sheaf.Paper.FiniteRestrictionDiagramNaturality)
