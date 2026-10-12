# ModulePullbackTensor proof elaboration scope

## Reason

The proof uses private noncomputable constructions, the existing presheaf monoidal
instance, and elaboration across the definitionally equal module/sheaf APIs.
The stage-3 interface checker conservatively treats the added local attribute and
set_option commands as a change to what importers see. The attribute is explicitly
local and is scoped by the added noncomputable section. Elaboration options govern
this file's declarations only. No existing signature, definition or public import
changes, and no importer needs adaptation.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] presheafMonoidalCategory
```

The added section is closed before the original namespace end. All added declarations
in the item are private. The only new public declaration is the proved theorem in
the new module, recorded by its new DAG node. The existing theorem's signature is
unchanged, so no target-statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModulePullbackTensor | Q2 | Local elaboration only; existing interface unchanged. |

The checker's downstream search for its synthetic name
`(commands such as variable, open, notation or attribute)` has no declaration users.
All importers retain exactly the original public imports and theorem type.

## Status

landed 20261012T135305-L-1687098 2026-10-12 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.ModulePullbackTensor)
