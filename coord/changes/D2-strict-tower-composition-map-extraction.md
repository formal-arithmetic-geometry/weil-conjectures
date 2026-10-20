# Strict-tower composition maps and refinement exchange imports

## Reason

The declared proof dependency `refinementExchangeCoherence` uses the canonical
`compositionF`, `compositionC` and `compositionE` definitions. Its module originally
imported the item module containing both these definitions and the theorems to be
proved from that dependency. Importing it back would create a Lean import cycle.
Move the existing definitions, verbatim, into a shared module and publicly reexport
that module from the item. No mathematical definition, signature or target changes. The extracted data get
their own definition node, `def-cbc-strict-tower-composition-maps`; the old coherence
node depends on it and retains only the declarations physically remaining there.

## Old

`Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` contained the definitions
`compositionF`, `compositionD`, `compositionC`, `compositionE`,
`CompositionRefinement`, `compositionH`, `CompositionBaseChange`, `compositionEf`,
`compositionEh`, `compositionEhf` and `compositionHorizontalE` before its first theorem.
Their signatures and bodies are preserved verbatim in the new file; source
docstrings now point to the extracted definition node.

`Sheaf.Paper.RefinementExchangeCoherence` imported these definitions with this line:

```lean
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting
```

## New

The definitions listed above are in the new module
`Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps`. The item publicly reexports them:

```lean
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
```

The sibling module replaces its old import by exactly the same line above. Its
remaining content, including all signatures, proofs and its existing named hole,
is unchanged. The item privately imports the sibling for its proof dependency.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | D2 | Public reexport preserves all existing constructions; proofs may import the sibling. |
| Sheaf.Paper.RefinementExchangeCoherence | H4 | One public import changes to the shared definitions; all declarations are unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | D2 (new) | Contains the existing constructions with their original bodies. |

The downstream checks for `compositionF` and `compositionC` list only the item and
`Sheaf.Paper.RefinementExchangeCoherence`; the latter is the only existing downstream
module. No source-library file is edited. Server preflight identifies H4 as its current holder; the one-line import change
is forced by the source import cycle described in the report. All original
signatures, data and proofs are unchanged.

## Status

landed 20261020T221113-L-4144504 2026-10-20 (merge of deliver/D2/Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting)
