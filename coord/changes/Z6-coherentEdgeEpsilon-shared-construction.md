# AlgebraicGeometry.coherentEdgeEpsilon

## Reason

The original construction is repeated in the top-degree Leray-square interface.
Repeated conversion between the two full expressions makes the assembled proof
exceed the single-file compiler limit. Keep the explicit construction in
`Sheaf.AlgebraicGeometry.TopDegreeLeraySquare` and make this existing name an
abbreviation of it. The former private comparison theorem compiled with `rfl`
before this refactor: the constructions are definitionally equal.
No object is selected by a new existence hypothesis and no statement is weakened.
The old signature and the value of the map are preserved. The supporting module
is now a public import because this public abbreviation uses its definition.

## Old

```lean
def coherentEdgeEpsilon {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj G) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (coherentEdgeCohomology f G 1)) :=
  (Classical.choose (exists_lerayEdge_isIso_of_vanishing f) 1).app G ≫
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) G 1).inv)
```

## New

```lean
abbrev coherentEdgeEpsilon {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :
    (forget₂ _ AddCommGrpCat.{u}).obj (topDegreeCohomologyOnBase f G) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (coherentEdgeCohomology f G 1)) :=
  topDegreeLerayEdge.{u, w} f G
```

The shared edge and cohomology-map interfaces use the underlying additive groups
of `topDegreeCohomologyOnBase` at their two bases. These are definitionally the
old additive cohomology groups. The source and target scalar restrictions are
explicit real constructions; no map or module action changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | Same map and signature; proofs unfold the shared construction when required. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses AlgebraicGeometry.coherentEdgeEpsilon` reports only this module and zero downstream
importers. No other module needs adaptation. In particular, no current Lean target
imports this module or uses this map in its statement. The DAG statement and source
meaning are unchanged. The independent statement/definition review should verify
this equality of constructions; any target later using the definition remains
subject to the project's target-meaning review. No source-library file is changed.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
