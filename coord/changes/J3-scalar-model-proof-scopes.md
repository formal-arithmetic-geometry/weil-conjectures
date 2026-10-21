# Sheaf.Paper.ScalarModelFiniteFlatResolution proof-local infrastructure

## Reason

Close the two remaining proofs using the existing independent-coefficient scalar
model. The static interface check includes scope commands and attributes, even
when they occur inside a proof-helper section. Record these additions explicitly.
All existing declaration signatures, definition bodies, and public imports are
unchanged. The two new additive structures are private theorems registered
only as local instances in `section ScalarModelProof`; they do not install global
instances for consumers.

## Old

The module had no proof-helper section or additive-instance registrations. Its
shared header was:

```lean
set_option autoImplicit false
universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits
```

## New

The shared header stays verbatim. The new private helpers are enclosed in:

```lean
section ScalarModelProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open HomologicalComplex
open scoped ChangeOfRings
```

Within that section, the proved private additive-structure theorems are
registered using exactly:

```lean
attribute [local instance] scalarExtensionPresheafFunctor_additive
attribute [local instance] scalarExtensionFunctor_additive
```

The section ends before the two public theorems. Each theorem has the two
`backward.isDefEq` options scoped to that declaration using `set_option ... in`.
These elaboration settings do not change any statement or construction.

## Users

`tools/downstream.py Sheaf.Paper.ScalarModelFiniteFlatResolution --uses
scalarModel_finite_flat_resolution_dvr scalarModel_finite_free_field scalarModel`
reports zero downstream Lean modules and only this item's own name occurrences.
The DAG parents with unfinished proofs still keep this item; it is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarModelFiniteFlatResolution | J3 | Private proved helper constructions and local additive instances support the two proofs. Existing public signatures, definitions, and imports are identical. |

No consumer needs adaptation and no target meaning changes.

## Status

landed 20261021T130038-L-2498770 2026-10-21 (merge of deliver/J3/Sheaf.Paper.ScalarModelFiniteFlatResolution)
