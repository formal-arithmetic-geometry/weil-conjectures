# DiagonalOrientationChoiceIndependent elaboration context

## Reason

Restore the complete module from the quarantine path recorded in `coord/rework.tsv`.
The recorded failure was a 60-second compile timeout. In this session the unchanged
archive also compiled, so restoring it with settings alone would not establish a
repair. This delivery instead restores it with a complete combining proof of
`diagonalOrientationChoiceIndependent`, from the existing DNC and trace-gluing
uniqueness theorems and two separately stated normalization results.

The backwards-unification settings match the chart-normalization and vector-integration
modules. They are local proof elaboration controls, preserve all existing public
signatures and definition bodies, and do not increase any compile limit. The two
new private helpers are fully proved and work first in an abstract category, keeping
the normalization-pair argument from unfolding the large geometric constructions.

No existing definition data, declaration attribute, target statement or public
import changes. The only removed imports are three private imports for the old
unimplemented proof plan. The new source lemmas have their own nodes and modules.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
```

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
```

These are elaboration commands local to this module. The definitions
`DiagonalChoiceDncNormalized`, `diagonalChoiceBeta`, and
`DiagonalOrientationChoiceIndependentConclusion` retain their entire archived text.
The theorem `diagonalOrientationChoiceIndependent` retains its original statement
and now has a complete proof combining the named dependencies. Its two new residual
normalization theorems are listed as a decomposition in the report; they do not
alter any existing definition or statement. Target meanings are unchanged.

## Users

`tools/downstream.py` reports the module as unknown because its library source was
quarantined. A direct search of `lean/` and `quarantine/` finds no current Lean
importer and no external occurrence of the theorem name. This does not make the
module unnecessary: the DAG parent still explicitly requires it, and the entire
archived attachment and dependency list are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | S2 (assigned rework) | Complete archived source restored with local elaboration controls. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | Its unfinished proof still cites this node in the DAG. The restored interface and its meaning are identical; no consumer edit is needed. |

## Status

landed 20261024T191000-L-200798 2026-10-24 (merge of deliver/S2/Sheaf.Paper.DiagonalOrientationChoiceIndependent)
