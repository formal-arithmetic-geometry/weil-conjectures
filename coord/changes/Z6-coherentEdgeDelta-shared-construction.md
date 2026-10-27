# AlgebraicGeometry.coherentEdgeDelta

## Reason

Keep the existing single-module mate as a named, typed construction on arbitrary
schemes. Its explicit body is precisely the original single-degree composite.
This avoids expanding the derived image and single-module data at chosen fiber
products during kernel conversion. No hypothesis, map or coefficient changes.

## Old

```lean
abbrev coherentEdgeDelta {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :
    (derivedPullback g).obj (coherentEdgeK f G) ⟶
      coherentEdgeK (pullback.snd f g) (coherentEdgeCoefficient f G g) := by
  letI : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition) k
  exact singleDegreeBaseChangeComposite f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition 0 G
```

## New

```lean
abbrev coherentEdgeDelta {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :
    (derivedPullback g).obj (coherentEdgeK f G) ⟶
      coherentEdgeK (pullback.snd f g) (coherentEdgeCoefficient f G g) :=
  topDegreeTensorBaseChange f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition G
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | Same mate, now a shared construction with fixed derived-image endpoints. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses coherentEdgeDelta` reports zero downstream modules and this module as the
only user (three occurrences in the current source). Its proof uses a private,
proved generic pasting interface before specializing at the fiber products. The
new `topDegreeTensorBaseChange` is recorded in the square node and has no holes.
Its defining composite is the old definition, with the same chosen additive proof
family. No source-library declaration or target statement changes. The independent
reader should compare these constructions and review any target using this map.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
