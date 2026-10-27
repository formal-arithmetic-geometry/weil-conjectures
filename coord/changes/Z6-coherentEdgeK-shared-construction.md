# AlgebraicGeometry.coherentEdgeK

## Reason

The derived image is the same actual derived direct image of the degree-zero single
module. Its construction now has the shared name `topDegreeDerivedImage` in
`Sheaf.AlgebraicGeometry.TopDegreeLeraySquare`. The shared definition is irreducible;
its canonical total-to-classical cohomology comparison is exposed by the actual
isomorphism `topDegreeLerayComparison`. The existing name remains an abbreviation
of exactly that construction. This prevents repeated expansion of the derived
image while matching the edge, mate and square interfaces. No value, hypothesis or
conclusion changes; no data comes from a new existence theorem.

## Old

```lean
abbrev coherentEdgeK {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :=
  (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
```

## New

```lean
abbrev coherentEdgeK {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :=
  topDegreeDerivedImage.{u, w} f G
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | All existing signatures and values are retained. The shared delta construction is the original single-degree composite with the same derived-image endpoints. The scalar proof uses the named total/classical comparison. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses AlgebraicGeometry.coherentEdgeK` reports zero downstream importers and only
this module as a user (eight occurrences). No other module needs adaptation. The
supporting module was already a public import for the edge and section maps.
The independent reader should compare the shared image body with the old body and
check the total/classical comparison. Any target later using the definition remains
subject to the project's target-meaning review. No source-library file is changed.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
