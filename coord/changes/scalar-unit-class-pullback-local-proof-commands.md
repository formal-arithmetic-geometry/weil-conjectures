# AlgebraicGeometry.Scheme.Modules.scalar_unit_class_pullback

## Reason

The preflight conservatively flags the local `open`, `set_option`, and `attribute`
commands used by the private proof helpers as an interface change. This record documents
that they occur inside a new section that ends before the existing public theorem.
No existing signature, visibility, definition, public import, or global instance changes.
No other module needs adaptation.

## Old

Immediately after the existing namespace command there was no helper section:

```lean
namespace AlgebraicGeometry.Scheme.Modules
```

The public theorem had its unchanged statement followed by `:= by sorry`.

## New

The following proof-local command block precedes four proved private helpers:

```lean
section

open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory HasExt.standard
```

The section ends before the original public theorem. Its options and local instances
therefore apply only to the private helpers. Two individual private helper declarations
have scoped, commented heartbeat increases; the complete module compiles within 60 seconds.
The public theorem is proved from those helpers and the existing coefficient-naturality
statement, whose module is added as a plain proof-only import.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ScalarUnitClassPullback --uses
scalar_unit_class_pullback` reports one downstream declaration user. The other 158
transitive importers do not mention the theorem and see the same public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities | unclaimed | Existing statement and proof remain valid; no edits. |

## Status

landed 20261013T100200-L-2496817 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.ScalarUnitClassPullback)
