# Semilinear pullback cube proof commands

## Reason

The new proof uses the fixed compositor and square comparison through their proved
API. A local transparency attribute prevents elaboration from unfolding their
chosen adjoint constructions. It changes no exported reducibility attribute.

## Old

The original commands immediately after the coefficient variables were:

```lean
attribute [local instance] moduleJAdj_unit_isIso
```

## New

The corresponding commands are:

```lean
attribute [local instance] moduleJAdj_unit_isIso
attribute [local irreducible] moduleGComp moduleSquareG modulePComp moduleAdj
  Functor.leftAdjoint
```

There is also a proof-only import:

```lean
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
```

It exposes the existing private proved section-pasting and mate-transport helpers
to this file's proofs. The category-theory open list also adds `Opposite` for
section indices. The adapted section and associativity lemmas use
`attribute [-instance] CategoryTheory.catToReflQuiver in`, scoped to each private
declaration as in the existing proof being adapted. The original public import, public theorem statement, definitions,
persistent instances and persistent attributes are unchanged. The new private
comparison definitions are explicit compositions of existing isomorphisms; their
associated private helper theorems are proved.

## Users

A source search for direct imports and `moduleSquareG_cube` finds the single
consumer below. This delivery makes no interface change and requires no consumer
adaptation. Unfinished DAG parents and the item's attachment are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SemilinearPullbackCubeCoherence | M5 | Local proof attribute and proved private helpers; original theorem proved. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | unclaimed in shared records | Uses the identical public cube theorem; no source adaptation. |

No target statement or definition changes.

## Status

landed 20261027T050620-L-245264 2026-10-27 (merge of deliver/M5/Sheaf.AlgebraicGeometry.SemilinearPullbackCubeCoherence)
