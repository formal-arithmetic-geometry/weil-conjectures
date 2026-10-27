## What changed

Repaired the single 2026-10-22 E3 return against the currently restored module
from A2's 62c1c8e4ed5 landing, rather than recreating the module from the earlier
quarantine snapshot. Kept A2's public imports and all public signatures and
definition bodies. The earlier missing-public-import defect is already fixed.

Specialized the Hom-pin rewrite explicitly at the two fixed objects. The final
theorem maps the core dependent pair under Nonempty.map, using the existing
typed assembly helper. Delta-reducing the target and explicitly unfolding only
the adopted core proposition retain the cached local geometric expressions;
this avoids the old expensive rewriting and elimination. Corrected the
proof docstring and DAG to describe the proved CoreData dependency and the
existing categorical assembly accurately. Current Lean attachment and
maintainer review metadata are preserved in the node copy. The blueprint
unit's statement and proof route are unchanged.

Change record:
`coord/changes/E3-perfect-overlap-object-realization-restoration.md`.

## Proved and sorry left

Actual assigned repair count: **zero existing sorries, zero left, zero added**.
No hole is claimed closed and no statement is split off.

AlgebraicGeometry.perfect_overlap_object_realization has a complete assembly
proof from the proved geometric core and the complete private theorem
perfect_overlap_object_realization_hom_pin. The latter uses pinned_conjugation,
naturality, cancellation and the explicitly specialized core.transition_pin.
The structure PerfectHomObjectRealization and proposition
perfectOverlapObjectRealizationStatement contain no proof holes.

Validation: the actual revised module compiles in 41.5 seconds. A fresh three-file
validation set compiles it in 47.4 seconds, the complete unchanged current
HomPresentation consumer in 46.4 seconds, and the axiom probe in 13.8 seconds.
All four probed declarations (the realization theorem, statement, structure and
CoreData theorem) use exactly propext, Classical.choice and Quot.sound.

## No longer needed

Removed the redundant direct DAG proof dependency
def-pc-perfect-overlap-stage-equivalence. CoreData already supplies the fixed
stage and apex equivalences. This node and its module remain needed
transitively and are not withdrawn.

No public import is changed relative to the current source. The retained
packet's TransportExtension import is not reapplied: the current public
PerfectHomTransport import already exposes perfectLimitMap. No mathematical
module, declaration, archive or unit is pruned. No deleted.txt is used.

## Where the brief, the DAG or earlier work was wrong

The returned packet tried to restore a file created after its base; A2 had
already restored the same complete theorem and repaired its obsolete import.
The new packet starts from that current version and makes an actual proof and
proof-documentation change. It does not claim restoration or hole-closing
credit for A2's work.

The route note predates completion of the geometric core chain. The currently
available CoreData theorem already provides the realization's geometric fields;
there is no unfinished realization chain in this module. Its direct stage-
equivalence DAG edge and old docstring incorrectly described this module as
constructing data it actually receives from that proved theorem. The corrected
route uses the same geometric constructions transitively without changing the
parent theorem or the fixed unit route.

Profiling and resumed compiles isolated expensive unfolding of the large
dependent proposition in the earlier final proof. The retained typed assembly
helper, Nonempty.map and controlled unfolding compile the complete proof in
24.4 seconds in a scratch check. The original elaboration settings and budgets
are retained; no definition, file or proof is split to evade the limit.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
