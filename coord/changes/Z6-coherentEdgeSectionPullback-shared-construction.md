# AlgebraicGeometry.coherentEdgeSectionPullback

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
def coherentEdgeSectionPullback {T T' : Scheme.{u}} (h : T' ⟶ T) (M : T.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback h).obj M) :=
  ((Scheme.Modules.tensorPullback h).obj M).val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top h.base).symm))
      (((Scheme.Modules.tensorPullbackSectionAdjunction h).unit.app M).app ⊤ s)
```

## New

```lean
abbrev coherentEdgeSectionPullback {T T' : Scheme.{u}} (h : T' ⟶ T) (M : T.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback h).obj M) :=
  topDegreeSectionPullback h M s
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | Same map and signature; proofs unfold the shared construction when required. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses AlgebraicGeometry.coherentEdgeSectionPullback` reports only this module and zero downstream
importers. No other module needs adaptation. In particular, no current Lean target
imports this module or uses this map in its statement. The DAG statement and source
meaning are unchanged. The independent statement/definition review should verify
this equality of constructions; any target later using the definition remains
subject to the project's target-meaning review. No source-library file is changed.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
