## What changed

Restored the complete quarantined `Sheaf.Paper.DlLocallyConstructibleAdicHeart` to its
original Lean path in the delivery. The rework claim remains held by D4 (confirmed by
the server claim tool). Preserved all declarations, signatures, definitions, visibility,
public imports, and DAG attachments and dependencies.

Repaired `WeilConjectures.dlAdicLocalCompatible_zero`: explicitly type the zero argument
to the common-stage representative specification as
`GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩`. Its cached abelian-group
instance supplies zero without asking instance synthesis to unfold `toStage`.
The complete repaired module compiles cleanly through `lcompile.py` in 27.2 seconds.
The node records this same proof elaboration detail. Change record:
`coord/changes/D4-dl-adic-heart-quarantine-stage-zero.md`.

## Proved and sorry left

This is a quarantine restoration and proof elaboration repair. The archived input
already has zero textual holes. Closed zero holes; added zero holes; split off zero
statements. No `sorry` remains in the item. The repaired declaration is
`WeilConjectures.dlAdicLocalCompatible_zero`, under
`def-dl-a1-locally-constructible-adic-heart`.

## No longer needed

None. All archived declarations, imports, dependency nodes, and unit steps are retained.
The quarantine archive is preserved; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned branch 3b62d471490 was based on a version still present in `lean/`, but
current main has moved the item to quarantine. The current rework row reports the
missing zero instance at the common-stage representative formula. This delivery
restores the archived item and fixes that exact failure, rather than deleting it or
repushing a cosmetic proof edit. The prior report incorrectly credited D4 with closing
five holes already proved before its delivery; the actual hole count for this repair
is zero. The previous cosmetic `rfl` to `exact rfl` edit is discarded.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
