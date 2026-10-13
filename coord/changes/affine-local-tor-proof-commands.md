# finiteTorAmplitude_of_affine_sheafification_of_open_tor

## Reason

The proof needs the names in `CategoryTheory.Limits`, local exact-functor composition
instances, and elaboration settings used elsewhere by the project for the shared sheaf
categories. The static interface checker conservatively flags changed command text.
No existing declaration's signature or visibility is changed. All original public
imports remain; added proof dependencies are non-public imports. The new general
single-degree helper has its own module and node, with a complete proof.

## Old

```lean
open CategoryTheory
```

All original declarations, signatures and public imports stay identical.

## New

```lean
open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

These commands affect elaboration in this module. The attribute uses `local instance`;
no instance is exported. The affine cancellation helper is private and fully proved, and is absent from every
public signature. The two K-flat/open-pullback helpers are reused through the non-public
`import all Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal`, without duplicate declarations. The main public theorem has exactly its old
signature. No target definition or statement changes meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor | unchanged; no adaptation | Uses the unchanged theorem signature; no effect on its statement or proof. |

`tools/downstream.py` reports this as the only downstream textual user of the theorem.
The changed options, open command and local attributes are confined to this file, so
other transitive importers need no adaptation. No module held by another group is edited.

## Status

landed 20261013T113355-L-3188004 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude)
