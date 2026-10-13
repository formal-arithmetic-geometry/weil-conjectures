# AlgebraicGeometry.Scheme.exists_etaleAffineTensorSectionsEquiv

## Reason

The static interface check requires this record because file-level elaboration
options and local attributes differ. These settings keep tensor-pullback definitions
folded and prefer the section module instance during elaboration. They are local to
this file. No existing declaration signature, definition, or public import changes;
no downstream module requires adaptation. The new helper `tensorQuasicoherent` is
private and fully proved. The independent reader should check these local settings.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
```

The theorem has a declaration-scoped `maxHeartbeats 200000` option. This changes no
statement or definition and does not raise the single-file wall-clock limit.

## Users

`tools/downstream.py --uses` finds the following explicit users. The theorem's
elaborated type and visibility stay identical, so each user continues to mean and
prove the same statement; there is no forced adaptation. The 170 modules in the
transitive import closure likewise receive no changed existing declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel | unclaimed in this checkout | none; signature unchanged |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan | unclaimed in this checkout | none; signature unchanged |
| Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv | Q4 | proof replaced; private proved helper and local elaboration settings |

## Status

landed 20261013T143550-L-562444 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv)
