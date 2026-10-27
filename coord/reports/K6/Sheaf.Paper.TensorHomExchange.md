## What changed

Restored the complete quarantined module `Sheaf.Paper.TensorHomExchange` from
`quarantine/Sheaf/Paper/TensorHomExchange.lean` and repaired repeated elaboration
of its coefficient categories. Explicit universe arguments keep both site universes
at the already specified `u`, avoiding universe metavariables that made instance
comparison expand coefficient and derived constructions. The inclusion shift
structures are supplied directly by Mathlib's `ObjectProperty.commShiftι`.
The existing local rational functor restrictions are retained. Both
backward-unification transparency options now respect the existing local
abstraction boundaries; the chosen coefficient valuation ring is locally
irreducible. All three elevated heartbeat limits are removed. Every import,
mathematical construction, normalization equation and theorem proof is retained.

Change record: `coord/changes/K6-tensor-hom-exchange-elaboration.md`.
The node's Lean statement is updated only to record the explicit universe arguments;
its mathematical statement and proof route are unchanged.

Validation: the final source compiled through `lcompile.py` in 31.4 seconds,
under the unchanged 60-second limit and without elevated heartbeat limits.
Static comparison with the quarantine archive confirms the same 36 declaration
names, identical imports, one theorem hole, and no Lean line over 100 characters.
The downstream check found no modules requiring adaptation.
The subsequent delivery attempt failed before pushing: the compile server's
`stdbuf` could not create its `/tmp` directory (`No space left on device`,
exit 125). The independent final-path compile had the same infrastructure error.
Neither failure reached Lean elaboration; the successfully compiled candidate
and delivery source are byte-for-byte identical.

## Proved and sorry left

Holes closed: 0. Holes added relative to the quarantine archive: 0. Split off: 0.
The only remaining hole is
`WeilConjectures.ConstructibleTensorHom.exists_family`, attached to
`sk-thm-sf-tensor-hom`, with its existing source and complete proof in words.
This delivery repairs the assigned compile failure; it does not claim a proof
of that theorem. No data definition contains a hole.

## No longer needed

None. Every archived declaration, public import, proof dependency and node attachment
is retained. No module is withdrawn, and no mathematical pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined for a 344-second global
compile, not because its statement was withdrawn. Raising the heartbeat budget on
three declarations did not meet the unchanged 60-second file limit. Diagnostics
showed repeated unification of coefficient/category instances and expansion of
the chosen valuation-ring and rational-localization data. This repair supplies
the missing elaboration information and keeps the same constructions.

The current blueprint has additional duality formulas. This repair restores the
existing Tensor--Hom exchange interface and does not assert those extra formulas.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
