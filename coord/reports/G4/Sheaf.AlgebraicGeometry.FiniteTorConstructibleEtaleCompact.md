## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Etale.finiteTorConstructible_etale_compact` with the specialization
of `AlgebraicGeometry.Etale.finiteRing_compactGenerators` planned by
`det-ctf-finite-compact-etale`. Added the proof-only import
`Mathlib.Algebra.CharP.CharAndCard`.

The proof recovers characteristic `D.p` from `D.card_base` and `D.cardinality_eq`,
using `charP_of_card_eq_prime_pow`. The injective algebra map transfers this
characteristic to `D.k`; `CharP.cast_ne_zero_of_ne_of_prime` makes the other prime
nonzero, hence a unit. The algebraic-closure instance supplies algebraic closedness.
The proof then retains the coproduct witness and compactness clause, passing the
constructibility and Tor-amplitude assumptions as their required conjunction.

No statement, definition, visibility, public import, or DAG route changed. No
consumer adaptations or change records are needed. The source dependency is
compatible with the assigned module's import direction. Remote single-file
compilation passed without warnings in 2.8 seconds.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Etale.finiteTorConstructible_etale_compact`
(node `det-ctf-finite-compact-etale`). No holes remain in the assigned module, and
no holes were added or split off. This is a proof from the existing named
`AlgebraicGeometry.Etale.finiteRing_compactGenerators` declaration (node
`lem-pur-etale-finite-ring-compact-generators`), whose separate proof obligation
remains in its own module.

The same coproduct witness is reused, preserving its indexing universe, the empty
family case, and the general theorem's zero-ring and empty-scheme cases. The
coefficient ring acquires no extra hypotheses.

## No longer needed

None. All original public imports support the statement; the original proof-only
`Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` import is used. The
single declared proof dependency remains necessary. No nodes or modules are
pruned. Searches of Mathlib and the source library found no shorter theorem than
the existing generalization already named in the DAG.

## Where the brief, the DAG or earlier work was wrong

None. The one-step specialization in the DAG and the existing docstring match
the Lean proof. Its field-characteristic verification needs the additional
proof-only Mathlib import, since that lemma is not publicly re-exported by the
finite-field datum's dependencies.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
