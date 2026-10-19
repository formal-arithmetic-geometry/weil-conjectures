# AlgebraicGeometry.Scheme.finiteFieldSheafScalarExtension proof imports

## Reason

The original theorem had a `sorry`. Its proof now uses the proved local tensor-model
comparison and the encoding of pro-etale coefficient modules. The theorem statement,
including all binder names, remains byte-for-byte unchanged. The proof-only imports are
plain imports, so downstream modules see the same public API. A new public helper module
is delivered because the local comparison is a separately named DAG result used by the
parent proof.

## Old

The item contained a proof-only `sorry` and imported the generic tensor/sheafification,
inverse-image, stalk, constant-module and pullback comparison modules.
There was no declaration-scoped linter setting.

## New

The theorem is proved from finite-field flatness, the pro-etale encoding equivalence,
the scalar-extension adjunction, the local tensor-model theorem, constructibility
transport along isomorphisms, and exact-functor homology comparison. Unused direct
proof imports are removed and replaced by the narrower interfaces actually used.
`set_option linter.unusedVariables false in` is scoped to the parent theorem, preserving
the original existential binder `e` without an unused-variable warning. This option
affects lint output only, not elaboration or exported instances. The added `open`
commands likewise only resolve names in this file.

## Users

No existing module is adapted. The public theorem signature and all public definitions
are unchanged; only proof bodies, private helpers and proof-only imports change.
The new public declaration
`AlgebraicGeometry.Scheme.finiteFieldScalarExtension_localModel` is recorded by
`lem-sf-finite-field-local-tensor-model` and is used only by this item and its parent
proof closure.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | V7 | Proof completed; signature unchanged. |
| Sheaf.Paper.FiniteFieldLocalTensorModel | V7, new | Proved local comparison, no new hole. |

No public imports, existing instance attributes or public definition bodies change.
No target definition changes, so target statement review is not reopened.

## Status

landed 20261019T034330-L-422210 2026-10-19 (merge of deliver/V7/Sheaf.Paper.FiniteFieldSheafScalarExtension)
