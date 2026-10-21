## What changed

Restored the assigned module from its rework.tsv quarantine path, verbatim, to
its original library path. This repairs the missing source after the merge-queue
cluster rollback. The module exports the transparent abbreviation
`AlgebraicGeometry.ProEtale.CondensedRing.bcoOpenAdjunction` for the existing
upstream bounded-constructible open-immersion adjunction. All hypotheses, the
public import, and the body remain exactly as archived.

The restored file compiles cleanly through lcompile.py. A temporary example also
checks by `rfl` that the alias equals the canonical `restrictFullyFaithful`
construction, with the ambient right adjoint transported along the existing
open-immersion derived-pullback isomorphism. The temporary example is not part of
the delivery. The construction works under precisely the original general
commutative-coefficient hypotheses; no extra coefficient condition is needed.

Change record: `coord/changes/F4-restore-bco-open-adjunction.md`.

## Proved and sorry left

The archived item has zero `sorry`; the restored item has zero `sorry`.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
`AlgebraicGeometry.ProEtale.CondensedRing.bcoOpenAdjunction` remains the real
existing construction, not a witness chosen from an existence theorem.
Its node is `def-sfb-dc-open-lower-shriek-adjunction`.
This is a restoration delivery, not new proof progress.

## No longer needed

None. No imports, nodes, modules, or declarations are pruned. The existing
upstream declaration already implements the node's plan, so the alias needs no
new proof imports. All existing DAG dependencies and its Lean attachment are
preserved. No `deleted.txt` is supplied and the archive is untouched.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole alias, not an unfinished theorem. The rework
row explicitly asks for restoration after a cluster rollback; this delivery
restores its missing implementation instead of treating its absence as pruning.
The published construction still matches the blueprint and the unit's prescribed
restriction/transport route. Exact searches find no live Lean importers and one
quarantined importer, `Sheaf.SixFunctors.IntegralRestrictionLine`; its import and
all DAG parent references remain valid for its separate restoration. No consumer
adaptation, statement change, new node, or new mathematical assumption is needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
