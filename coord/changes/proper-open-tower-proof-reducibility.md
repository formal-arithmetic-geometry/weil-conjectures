# AlgebraicGeometry.ProEtale.StrictTower.properOpenTowerComparison

## Reason

The new proof uses fully proved private adjunction lemmas and explicit specialization
of the strict-tower operations. During proof elaboration, a local reducibility override
prevents Lean from unfolding the concrete derived functors while matching categorical
identities. The added backward-definitional-equality option supports the same matching.

Server preflight classified the added local attribute command as a change to what other
modules see and requested this record. The override is local to this module. It does
not persist to importers and changes no public signature, declaration attribute,
public import, definition body or theorem statement. No source-library file changes.

## Old

The existing module settings, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
```

There was no local reducibility command for the imported strict-tower operations and
no `backward.defeqAttrib.useBackward` setting in this module. All six public definitions
and the theorem signature remain verbatim, so no old public signature is superseded.

## New

The existing settings above remain. These proof-elaboration commands are added in the
same namespace (the reducibility attribute occurs after the existing definitions):

```lean
set_option backward.defeqAttrib.useBackward true
```

```lean
attribute [local irreducible] G R J adj jAdj
```

These commands guide elaboration only; the kernel still checks every proof. No kernel
check, compile timeout or heartbeat limit is disabled or raised. All new helper
theorems are private and proved, and the existing theorem's hole is closed.

## Users

`python3 tools/downstream.py Sheaf.Paper.ProperOpenTowerComparison --uses
properOpenTowerComparison` reports zero downstream Lean modules, and only the item's
own declaration as a textual use. The DAG attachment and its parents are preserved.
No consumer needs adaptation because the public interface is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperOpenTowerComparison | H1 (this assignment) | Private proof helpers and proof-local elaboration settings; existing public interface unchanged. |

## Status

landed 20261020T211726-L-3494060 2026-10-20 (merge of deliver/H1/Sheaf.Paper.ProperOpenTowerComparison)
