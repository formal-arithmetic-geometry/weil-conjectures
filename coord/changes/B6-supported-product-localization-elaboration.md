# Sheaf.AlgebraicGeometry.SupportedProductLocalization

## Reason

The new proofs transport through exact derived functor compositions, supported
coefficient adjunctions and tensor comparisons. They need Lean's elaborator to
unify the reducible comparison expressions without the backward definitional
equality transparency restriction. The option is scoped to this module's
elaboration. Existing declaration signatures, definitions and public imports
are unchanged; the added dependency is a private proof import.

## Old

```lean
set_option autoImplicit false
universe u
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.SupportedProductLocalization
--uses supportedProductLocalization_openFirst supportedProductLocalization_openSecond`
reports zero downstream modules and only the item itself as a user of either
name. This does not withdraw the module or any of its DAG parents.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | B6 | Proof elaboration option; both open identities now have complete proofs from coefficient squares. Existing signatures and definition bodies are unchanged. |

No other module needs adaptation. All eleven sandbox modules compile together.

## Status

landed 20261021T013338-L-2287984 2026-10-21 (merge of deliver/B6/Sheaf.AlgebraicGeometry.SupportedProductLocalization)
