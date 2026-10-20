# Sheaf.Paper.SiteTensorLocalModelComparison proof-local instances

## Reason

The proof uses the concrete monoidal and symmetric structures of module sheaves in a private
section. The static parser identifies the two local instance commands as interface additions,
so this record documents their scope. Both declarations precede the public section and are
local instances only; no existing declaration, signature or public instance changes.

## Old

The old module had no private proof-helper section and no local instances there.

## New

```lean
noncomputable local instance : MonoidalCategory A := monoidalCategory ℛ
noncomputable local instance : SymmetricCategory A := symmetricCategory ℛ
```

Here `A` is the local notation `realizationModules J B` in `section Site`. These are concrete
constructions, without holes or choice of data from an existence theorem. They are used only
by private proof helpers. The public theorem keeps its original statement verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SiteTensorLocalModelComparison | E1 | Private helpers use local instances. |

No consumer sees the local instance attributes or needs adaptation. No target definition or
statement changes.

## Status

landed 20261020T051207-L-1591185 2026-10-20 (merge of deliver/E1/Sheaf.Paper.SiteTensorLocalModelComparison)
