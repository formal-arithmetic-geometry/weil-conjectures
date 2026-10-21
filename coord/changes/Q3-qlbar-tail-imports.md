# Sheaf.Paper.QlbarTailModuleColimit public imports

## Reason

Remove the unused finite-subextension theorem re-export. The published directed-order
instance already supplies the common upper bounds needed by the tail argument.
The coefficient colimit remains the original cocone, restricted along the final tail
inclusion and reflected through the module forgetful functor.

## Old

```lean
public import Sheaf.Paper.FiniteSubextensionsDirected
```

## New

The import is removed. All declaration signatures and both abbreviation bodies remain
verbatim. The finite intermediate fields and their order are supplied by the retained
public Compatibility import. No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QlbarTailModuleColimit | Q3 | Existing theorem proved; unused re-export removed. |

`python3 tools/downstream.py Sheaf.Paper.QlbarTailModuleColimit` reports zero downstream
modules. No Lean consumer needs adaptation. DAG parents retain the same module-colimit
statement and its specified coefficient inclusions.

## Status

landed 20261021T140859-L-2768606 2026-10-21 (merge of deliver/Q3/Sheaf.Paper.QlbarTailModuleColimit)
