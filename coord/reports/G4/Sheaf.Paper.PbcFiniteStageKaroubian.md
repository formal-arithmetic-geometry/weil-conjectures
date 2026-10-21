## What changed

Restored `lean/Sheaf/Paper/PbcFiniteStageKaroubian.lean` verbatim from
`quarantine/Sheaf/Paper/PbcFiniteStageKaroubian.lean`, as assigned by its
`coord/rework.tsv` row (cluster restore, 2026-10-20). The original module is absent
from the live library. This delivery restores its actual public theorem and full
proof, rather than withdrawing its mathematical content or submitting an empty module.
The quarantine archive remains intact.

The theorem `AlgebraicGeometry.Scheme.finite_stage_karoubian` extracts the bounded
t-structure from `pbc_localized_tstructure`, converts `t.bounded = ⊤` into objectwise
boundedness, and applies the two existing general bounded-t-structure Karoubian
results. The third conclusion concerns the canonical `toKaroubi` functor with the
existing induced triangulation. No extra Tor hypothesis is used.

The restored module compiled cleanly through `lcompile.py` in 2.9 seconds.
All signatures, universes, visibility, public imports, instances and mathematical
meaning agree with the archived source. No definition or interface was changed,
so no consumer adaptation or definition change record is needed. There are no
current live Lean importers; quarantined parents `PbcQbarIdempotentComplete` and
`RationalPurityPresentation` and their dependency links are preserved. The node's
Lean attachment and all three proof dependencies are unchanged, matching the proof.
The unit `sk-rem-rest` has no realized statement or proof steps to bypass.

## Proved and sorry left

`AlgebraicGeometry.Scheme.finite_stage_karoubian`
(node `thm-weil-pbc-finite-stage-karoubian`) is restored with its complete proof.
The archived module has zero holes; the delivered module has zero holes.
Holes closed in this repair: 0. Holes added: 0. Split off: 0.
There are no remaining `sorry` declarations in the delivery.
This is a quarantine restoration, not a newly closed proof hole.

## No longer needed

None. No imports, nodes or modules are pruned. The proof still uses
`def-weil-pbc-rational-category`, `prop-weil-localized-tstructure`, and
`thm-weil-karoubian-bounded-t`. Public imports are retained verbatim to preserve the
archived interface. No DAG dependency or Lean attachment is removed.

Searches of Mathlib and the two library roots found the existing general
Karoubian theorem, which the proof already uses. The similar theorem
`WeilConjectures.rationalization_idempotent_complete` concerns a different
finite-field category and does not replace this arbitrary-base assertion.
LeanFinder returned general triangulated-equivalence declarations; Loogle found
no combined bounded-t-structure/idempotent-completeness match. None shortens this
already complete three-step argument.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module with holes, but the current rework assignment
is the restoration of an absent, quarantined module whose archived theorem is
already proved. Its `coord/rework.tsv` entry records a cluster restore, rather
than an error in this theorem. The current return file has no item-specific
numbered repair requests. Restoring the archived proof compiles against the current
library without changes. No mathematical statement, definition, or proof-plan
error was found.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
