## What changed

Restored the quarantined Sheaf.Paper.TensorAdjunctionExchange module and its
previously reviewed definition owner Sheaf.SixFunctors.TensorHomTranspositionData.
The owner contains the ten definitions assigned by
`def-sf-tensor-hom-transposition-data`; the parent imports it instead of repeating
them, as the node's independent review requires. All 28 original declarations
remain exactly once, with unchanged data and mathematical interfaces.

Made the coefficient universes explicit and restored normal transparency for
elaboration to repair the archived record-field timeouts. No limits are raised.
The two-file lcompile.py --all check succeeded with no warnings. The wrapper
reported 52.9 s and 73.2 s respectively; its duration includes waiting for the
shared cache, while each actual Lean subprocess has the unmodified 60 s timeout.
The 28 declaration blocks match the archive after normalizing explicit universe
arguments, and a source import walk found no cycle.

The change record is
`coord/changes/J8-tensor-adjunction-definition-ownership.md`.

## Proved and sorry left

Assigned build/definition repair. Holes closed: 0. Holes added: 0.
The existing hole is
`WeilConjectures.TensorAdjunctionExchange.tensor_adjunction`
(node `fix-lem-tensor-adjunction`), unchanged with its full source and proof docstring.
The restored shared definition module has zero sorry occurrences. Nothing is split off.

## No longer needed

Replaced the parent's public import of `Sheaf.Paper.VerdierExchange` by the reviewed
transposition definition owner, which imports `Sheaf.SixFunctors.VerdierExchangeData`.
Only the Verdier definition interface is used; the Verdier theorem/package is not
needed here. No DAG dependency, node, module or unit route is withdrawn.
No other import is removed.

## Where the brief, the DAG or earlier work was wrong

The archived parent predates the reviewed extraction of its ten definitions.
The current DAG records their shared ownership, but that source file is absent
without a rework row or quarantine copy. Restoring the old parent unchanged would
ignore the review instruction and prevent the signed-transposition dependency from
using the independent definitions. The shared owner is reconstructed from the
archive and its existing node attachment is preserved.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
