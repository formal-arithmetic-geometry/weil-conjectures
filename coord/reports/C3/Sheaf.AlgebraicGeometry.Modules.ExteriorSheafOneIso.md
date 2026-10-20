## What changed

The duplicate Sheaf theorem `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso` remains
withdrawn in favor of the proved official
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafOneIso`; the withdrawal is listed in
`deleted.txt`. The quarantined consumer
`Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` was removed from this delivery, so its
proved quarantine copy is preserved unchanged. The exact requested consumer adaptation is
recorded in `coord/changes/retire-exterior-sheaf-one-iso-20261020.md`.

The delivery also fills the existing
`Compactification.exists_overRefinement` proof in
`WeilConjectures.Compactification.Refinement` using the available common-refinement
construction. Its public signature is unchanged.

## Proved and sorry left

The retired item has no remaining hole: its official replacement theorem is already proved.
This delivery closes `AlgebraicGeometry.Compactification.exists_overRefinement`. It adds no
Lean consumer and therefore adds no `sorry`; the quarantined
`smoothProperCurve_dualizing` declaration is outside this delivery and is unchanged.

## No longer needed

The withdrawn duplicate Sheaf module and its consumer adaptation are not included in this
delivery. The quarantined consumer archive remains preserved and is not treated as a source
module. The official exterior-power theorem and its comparison are retained in the DAG and
source library. The `CommonRefinement` import is needed by the retained
`exists_overRefinement` proof.

## Where the brief, the DAG or earlier work was wrong

The previous packet copied the quarantined consumer into the delivery and replaced its proved
body with a `sorry`. That violates the quarantine-preservation rule. This repair drops the
consumer file from the packet, preserves the quarantine copy, and records the exact adaptation
with the restored relative-duality import and proof body in the change record. The prior
change-record claim that the consumer hole was retained as an offset is removed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
