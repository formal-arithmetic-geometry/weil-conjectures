# CategoryTheory.ExactAdjointTowerModels proof elaboration commands

## Reason

Preflight classifies added top-level `set_option` and declaration-local `omit`
commands as an interface change. This record documents those commands explicitly.
They support the new private proofs and remove unused section-instance warnings.
No existing public signature, definition body, attribute or public import changes.
There is no mathematical definition repair and no consumer requires adaptation.

## Old

The existing option command was exactly:

```lean
set_option autoImplicit false
```

There were no private proof helpers or declaration-local `omit` commands.
The public declarations were `tower`, `DerivedModel`, `negativeCoordinates`,
`NormalizedRoos`, `Models` and `exists_models`; they retain their original signatures.

## New

The option commands are exactly:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The new `omit ... in` commands remove unused section-instance binders only from
these private declarations: `derived_exists`, `ordinaryIso_components`,
`productIso_shift`, `computes_one`, `products_compute`, `sign_coordinates`,
`arrowMap_eq_coneMap`, `inclusion_sign` and `q_surjective`.
Their complete signatures and proofs are in the item module. Each `omit` is scoped
to its following private declaration. The options affect elaboration within this
module; they introduce no attributes, instances, notation or declarations into
an importing module.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ExactAdjointTowerModels --uses
CategoryTheory.ExactAdjointTowerModels.exists_models` lists the following downstream
module. Its public import and use of the unchanged model structures remain valid;
none of the private helpers or proof elaboration options is part of its API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactAdjointTowerModels | B4 | Item: private proof helpers and a complete proof replace the single sorry. |
| Sheaf.CategoryTheory.FlatScalarTowerLimitSquare | V6 | No effect; its imports and public model interfaces are unchanged. No adaptation. |

No target definition changes meaning, so this elaboration-only change does not
reopen the statement review of any target.

## Status

landed 20261021T120320-L-3757611 2026-10-21 (merge of deliver/B4/Sheaf.CategoryTheory.ExactAdjointTowerModels)
