## What changed

Restored `lean/Sheaf/Paper/VectorPurityScalarSingle.lean` verbatim from the
quarantine path explicitly assigned in `coord/rework.tsv`. This repairs the
missing module/API after the cluster restore. All ten definitions and all four
public imports are preserved. The module is a zero-hole definition restoration,
not a theorem-proof delivery.

The construction uses ordinary sheafified scalar extension and its published
adjunction, the fixed derived scalar extension and adjunction, the exact
restriction/single comparison, and the normalized tensor, unit and pullback
identifications. The generic helper transposes the ordinary unit followed by
the inverse exact-single comparison. The unit helper transports the published
normalized unit isomorphism along the two single/unit identifications.

Read the assigned node, all five statement-dependency nodes and their Lean
interfaces, the unit record and the current blueprint proof. Loogle and LeanFinder
found no replacement for the specialized comparison; repository and Mathlib
searches confirm reuse of `Functor.mapDerivedCategorySingleFunctor` on exact
restriction. No alternate route or new scalar functor is introduced.

Validation: `lcompile.py` compiled the restored module cleanly in 20.5 seconds.
Compared its complete text with the quarantine source; checked all lines are at
most 100 characters and that the source has no sorry. The delivery tool performs
the declaration/axiom preflight. Consumer check: no live importers; the quarantined
finite-reduction and vector-bundle-purity modules still use the identical restored
interface, and their DAG dependencies remain intact. No hypotheses of flatness,
finiteness, nonzero rings or nonempty schemes are added: these are constructions
for arbitrary stated rings, ring maps and schemes, including identity maps,
zero modules, zero rings and empty schemes. No general invertibility of the
scalar/single map is asserted.

Change record: `coord/changes/N2-vector-purity-scalar-single-restoration.md`.

## Proved and sorry left

Original archived holes: 0. Holes closed: 0. Holes added: 0. Holes remaining in the
restored item: 0. No statements are split off. All ten archived definitions are
restored as actual constructions; no definition contains a sorry. No dependency
proofs are claimed to have been completed by this delivery.

## No longer needed

None. No import, node, dependency or module is pruned. In particular, the lack of
live importers is due to quarantine, not a reason to withdraw the assigned item.
The unit route and the existing node attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The queue presents a repair slot with a numeric hole count, but the authoritative
archived source contains zero sorries. The rework row identifies the real defect:
the module was removed by the cluster restore. Its archived source already fits
the current dependencies, so restoring its full API is the repair; no mathematical
statement or canonical construction needs to be altered. No numbered return
points for this item appear in the local N2 return record.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
