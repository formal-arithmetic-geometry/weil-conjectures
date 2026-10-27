## What changed

Repaired the listed rework item `Sheaf.SixFunctors.RationalVerdier`. The original
`completionChain` traversed nested existential witnesses for a derived tensor and
representative comparison before reaching its cochain map. Kernel checking expanded
the tensor totalization and coefficient quotient tower beyond the single-file limit.
The repaired definition permutes the same theorem's existential witnesses with
`Exists.imp` and `exists_comm`, then chooses the cochain map directly. The entire
original normalization predicate remains attached to that witness. No import is
added. The canonical residue-field inverse proof uses `map_natCast` explicitly.
Existing theorem and structure signatures, including `coef_rational_verdier`, are
preserved. The module remains attached to its existing DAG nodes.

The Mathlib-only variant compiled cleanly in 40.2 seconds during diagnosis.
Final validation compiled the delivered file and the unchanged direct consumer
`Sheaf.Paper.RationalTensorSymmetry` together in import order (both exit 0).
The delivery tool performs its own compile and axiom probe.

The change record is `coord/changes/H7-rational-verdier-completion-projection.md`.

## Proved and sorry left

The item has one existing hole, unchanged:
`WeilConjectures.coef_rational_verdier` (`thm-coef-rational-verdier`).
This is a definition repair: 0 of the item's 1 holes closed, 0 holes added, and
0 split off. No anonymous, private or definition hole was introduced.

## No longer needed

No DAG node or module is withdrawn. The seven-step Verdier argument and its unit
route remain required. Experimental generic localization and exactness lemmas were
kept in scratch files only; they are not part of the delivered library.

## Where the brief, the DAG or earlier work was wrong

The rework row records a transitive `ProjectiveLineGenusZero` import failure. The
current source was present and its archived copy was preserved. After dependencies
became available, the item itself still exceeded the 60-second single-file limit.
Diagnostics isolate the nested completion-witness projection; the repair changes
that data access, rather than withdrawing a quarantined statement or changing the
limit.

The current blueprint update describes condensed coefficient categories, while the
published Lean interface still uses the recorded raw scalar localizations. This
repair preserves that published interface and does not claim to resolve the
separate statement-review issue.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
