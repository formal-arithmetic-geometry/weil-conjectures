# AlgebraicGeometry.ProEtale.SpTowerCalculus: restore the section-normalized interfaces

## Reason

The assigned rework row preserves this module in
`quarantine/Sheaf/Paper/CoefficientTowerShriekInterfaces.lean` after a failed cluster
restore. Restore its full original interface to its original Lean path. The archive
now compiles against the published server dependencies without mathematical changes.

The archive globally removes the generic essentially-small sheafification instance
and re-registers it at high priority after elaborating the interfaces. Use a section
for that removal instead: Lean restores the inherited instance at the end of the
section, without an explicit global re-registration. This preserves the intended
coefficient-universe instance search inside the file and avoids exporting a changed
registration. The removal/restoration behavior was checked with a separate single-file
Lean experiment. The incorrect syntax `[local -instance]` was tested and discarded;
it does not occur in this delivery.

## Old

The mathematical declaration block in the archived module is retained verbatim.
The original commands around that block are:

```lean
-- Reuse the inherited coefficient-universe sheafification instead of small-site transport.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
```

and, after the namespace closes:

```lean
-- Restore the inherited instance priority for importing modules.
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

## New

```lean
-- Reuse the inherited coefficient-universe sheafification instead of small-site transport.
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
```

The section ends immediately after the original namespace closes:

```lean
end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
```

All original public imports, declaration signatures, structure fields, definition
bodies, universe parameters, normalization equations and existing options remain.
No definition obtains data from an existence theorem, and no theorem is added or
weakened. No target statement or target-used definition changes its mathematical
meaning. The existing node attachment and dependencies remain valid and unchanged.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientTowerShriekInterfaces --allow-missing`
reports zero current Lean consumers: the item and its four direct consumers are
quarantined. Searching the archived sources finds exactly the following four
importers. They retain the same interface, with no source adaptation required.
Their unchanged archived sources were copied into the sandbox for compilation only;
they are not part of this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | B2 | Restore all definitions; scope instance removal. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same Coordinates interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same operation and coherence records; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same reduction and normalization fields; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public reexport and assembly interface; no adaptation. |

The three lemma nodes still cite `def-sp-coefficient-tower-shriek-interfaces` in
`stmt_deps`; the calculus node retains its parent role. None is pruned or detached.
The unit route remains unchanged. No module held by another group is adapted.

## Status

landed 20261022T145603-L-2020001 2026-10-22 (merge of deliver/B2/Sheaf.Paper.CoefficientTowerShriekInterfaces)
