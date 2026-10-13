# AlgebraicGeometry.exists_local_koszul_augmented_carrier

## Reason

The completed proof constructs natural isomorphisms across affine charts and the
localized over site. Unfolding tensorPullback and tensorPullbackObj in these comparisons
caused a single-file compile timeout. A local irreducibility annotation keeps elaboration
on the public functor API and brings compilation within the required 60-second limit.
The delivery checker conservatively treats any added attribute command as an interface
change, so this record documents its actual local scope. The annotation does not modify
either definition or its exported reducibility, and the theorem's signature is unchanged.
No definition, target statement, public import, instance or consumer proof is changed.

## Old

The file had no local irreducibility annotation for these definitions:

```lean
namespace AlgebraicGeometry
```

The public theorem's existing signature is retained verbatim in the delivered module.
Its old proof body was `:= by sorry`.

## New

Inside `namespace AlgebraicGeometry`, before the private chart comparison helpers:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
```

This attribute expires at the end of the module. Every private helper is proved,
and the public theorem now has a complete proof. The previously documented `open MonoidalCategory in` command and private
`finiteFree_flat` declaration have been removed; flatness is proved locally
inside the public theorem.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier --uses
AlgebraicGeometry.exists_local_koszul_augmented_carrier` reports the two textual users
below. Its import closure contains 344 modules, all unaffected because no exported
signature, definition body or elaboration registration changes. None needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier | C1 | Local proof elaboration only; original theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.LocalTensorFiniteFreeZeroModel | unclaimed | The existing theorem application keeps exactly its original type. |

## Status

landed 20261013T222359-L-1220971 2026-10-13 (merge of deliver/C1/Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier)
