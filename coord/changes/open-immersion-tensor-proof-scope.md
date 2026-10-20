# Sheaf.Paper.OpenImmersionTensorPiece proof scope

## Reason

The stage-3 static gate classifies changed `open` and universe commands as an interface
change and requires this record. The proof uses tensor notation and general categorical
helpers with independent universes. It opens `MonoidalCategory` inside the proof namespace,
declares three additional universe names for private helpers, and selects
elaboration options used by the sheaf-tensor proofs. After the ordinary comparison is
proved, `monoidalCategory` is locally marked irreducible to keep later derived proofs
from repeatedly unfolding its large construction. These commands provide proof syntax
and elaboration context. They introduce no public declarations, instances or notation.

The existing five public definitions, including their bodies, and the target theorem's
signature compare verbatim with the original source. All new declarations are private,
proved theorems. All original public imports remain verbatim. The presheaf tensor structures and derived-category instances used inside proofs
are the existing canonical constructions, supplied explicitly to avoid repeated inference.
No consumer adaptation is required. This is a scope-command record, not a definition or statement repair.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
```

After the existing variable command there was no additional universe command.

## New

The added elaboration options and tensor notation are scoped inside the namespace:

```lean
namespace SheafOfModules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory
```

After the unchanged variable command, the private helper universes are declared by:

```lean
universe u₀ v₀ r
```

The proof-local reducibility attribute is:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
```

These settings end with the namespace and are not exported. In particular,
the added unification settings do not affect the delivery tool's appended axiom probe.

## Users

Ran `tools/downstream.py Sheaf.Paper.OpenImmersionTensorPiece --uses` for each of the
six existing declarations. Its name-use results list only the item's module itself for
each name; no other module textually mentions these names. It separately reports 1039
transitive importers, whose signatures and imports are unaffected by these proof-scope
commands. No other module is adapted in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenImmersionTensorPiece | G1 | Private proof helpers and the original theorem proof; public definitions and signatures unchanged. |

## Status

landed 20261020T211714-L-3490672 2026-10-20 (merge of deliver/G1/Sheaf.Paper.OpenImmersionTensorPiece)
