# AlgebraicGeometry.Scheme.FiniteCompactScalar.openScalar_transport

## Reason

The static reader-risk heuristic notices the added `attribute` command. It is
explicitly local: it keeps two large categorical constructions abstract during
proof elaboration in this module. It changes no imported module's reducibility
attributes, declaration signatures, instances, or public imports. The public
statement was compared verbatim with the current repository and is unchanged.

## Old

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar
```

## New

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed in current claim records | None: local proof elaboration attributes are not exported; its imported theorem has exactly the same signature. |

No consumer adaptation is needed and no shared definition or statement is changed.
The narrower public import in the new site module concerns a newly introduced module,
which has no pre-existing consumers.

## Status

landed 20261027T034812-L-3688125 2026-10-27 (merge of deliver/Y3/Sheaf.Paper.FiniteOpenScalarTransport)
