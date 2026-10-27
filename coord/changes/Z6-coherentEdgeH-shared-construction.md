# AlgebraicGeometry.coherentEdgeH

## Reason

The actual scalar-restricted cohomology module now has a shared constructor,
`topDegreeCohomologyOnBase`. Its body is exactly the old definition on arbitrary
schemes. The edge and coefficient pullback use the same module presentation,
so kernel conversion does not expand chosen fiber products to compare native
cohomology with scalar restriction. No underlying group, scalar action, or map
changes. No data is taken from an existence theorem.

## Old

```lean
abbrev coherentEdgeH {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  (ModuleCat.restrictScalars (pullback.snd f g).appTop.hom).obj
    ((RingedSpace.moduleCohomology (pullback f g).toRingedSpace 1).obj
      (coherentEdgeCoefficient f G g))
```

## New

```lean
abbrev coherentEdgeH {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  topDegreeCohomologyOnBase (pullback.snd f g) (coherentEdgeCoefficient f G g)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | Same cohomology module and scalar action, with a common folded constructor for the edge and coefficient map. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses coherentEdgeH` reports zero downstream modules and this module as the only
user (four occurrences in the current source). The existing edge source and
coefficient-pullback type use the underlying additive groups of these restricted
modules. Those groups are definitionally the old native cohomology groups; scalar
restriction changes only the scalar action. Their exact defining maps are unchanged.
The independent reader should unfold the shared constructor and compare the old
module, its action and the two maps. Any target depending on this definition needs
the prescribed meaning review. No source-library declaration is changed.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
