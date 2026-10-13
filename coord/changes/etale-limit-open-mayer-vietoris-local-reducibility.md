# AlgebraicGeometry.Etale.etale_limit_open_mayerVietoris_maps

## Reason

The complete assembly exceeded the single-file limit when elaboration unfolded inverse-image
sheaves and cohomology pullbacks while matching the final morphism equalities. Keep those
existing definitions symbolic locally, introduce the statement's let-bindings explicitly,
and check the final equalities pointwise. The complete file now compiles within 60 seconds.

The stage-3 static checker classifies added attribute commands as interface changes and
requires this record. The attributes below are explicitly local: neither the types, bodies,
visibility nor exported reducibility of `upperStar` and `cohomologyMap` changes. The
Mayer--Vietoris theorem's signature and visibility also remain exactly unchanged.

## Old

The item's namespace opened without local reducibility attributes:

```lean
namespace AlgebraicGeometry.Etale
```

All existing signatures and both imported definitions were those of the library.

## New

```lean
namespace AlgebraicGeometry.Etale

-- Keep inverse-image sheaves symbolic while comparing the transported map types.
attribute [local irreducible] upperStar cohomologyMap
```

This command expires at the closing namespace. No definition or statement is replaced.
No target meaning or statement review is reopened, and no forced adaptation is required.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps --uses
AlgebraicGeometry.Etale.etale_limit_open_mayerVietoris_maps` found the two textual users
below, including the declaration itself. It also lists 275 transitive importers; they see
exactly the same theorem type and imported definitions, since these attributes are local.
No downstream module is edited or adapted in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps | T1 | Proof elaboration only; signature unchanged. |
| Sheaf.AlgebraicGeometry.EtaleLimitBinarySuccessorCoconeSegment | unclaimed | No change to its invocation or elaboration environment. |

## Status

landed 20261013T145124-L-697337 2026-10-13 (merge of deliver/T1/Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps)
