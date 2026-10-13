# AlgebraicGeometry.Scheme.Modules.resolutionSectionClass

## Reason

The returned target took 97 seconds globally. Profiling the previous local repair
identified automatic unfolding of resolutionSectionClass in the final equality check:
the final exact took 35.2 seconds. Keep resolutionSectionClass irreducible locally
alongside sectionCohomologyTheta and moduleCohomologyFMap. Explicitly unfold it only
where the section-class calculation needs its construction. The final exact then
uses the named map; its profiled time is 0.31 seconds. No definition body, type,
public signature, or mathematical meaning changes; no attribute is exported.

## Old

```lean
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
```

## New

```lean
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass
```

Replace `dsimp only [resolutionSectionClass]` in the private comparison helper with
`unfold resolutionSectionClass` followed by `dsimp only`: the local irreducibility
requires explicit unfolding at this one calculation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TargetSectionClassRestriction | Y3 | section-class construction stays named; final compile 38.9 s |
| Sheaf.AlgebraicGeometry.RestrictedResolutionCohomology | new Y3 module | unchanged signature and proof; compiled first in 35.4 s |
| Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassRestriction | unclaimed | unchanged; checked against the complete overlay |

The global attribute change and the forced-unfold adaptations in the earlier sandbox
attempt are removed. All other users of theta retain their original elaboration
behavior because the attribute is local to the item. No target meaning is changed.
The target importer and raw-comparison theorem are delivered and compiled together;
neither public signature changes. Return points 2 and 3 need no further adaptations.

## Status

landed 20261013T113359-L-3189644 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.TargetSectionClassRestriction)
