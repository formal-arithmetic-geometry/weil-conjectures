## What changed

Retired `Sheaf.Topology.StalkDirectSums` using `deleted.txt`. Redirected the
`lem-pc-stalk-direct-sums` Lean record to the existing, proved theorem in
`WeilConjectures.Topology.StalkDirectSums`. Replaced the single private import in
`Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` with the source twin. All its
statements and proofs remain byte-for-byte unchanged. The adopted source tree is
unchanged. Change record: `coord/changes/U4-stalk-direct-sums-retirement.md`.

The scratch example instantiates the source theorem at the full original signature,
including its commutativity binder, with a single exact application. The source
axiom check prints only `propext`, `Classical.choice`, `Quot.sound`.

Single-file server checks all passed: the original module (4.7 s), the upstream
specialization and axiom check (1.5 s), the adapted ConormalGradedAlgebra (5.7 s),
ConormalGradedAlgebraHomExt (4.1 s), ConormalAlgebraFlatBaseChange (4.0 s), and the
unchanged source SupportedCompactDetectorModel (13.4 s). The latter three were
compiled from unchanged verification copies and are not delivered. The downstream
conormal checks used the sandbox's compiled adapted consumer.

## Proved and sorry left

Retirement repair, not a new proof: the assigned module has 0 initial holes,
0 holes closed, 0 holes added, and 0 holes remaining. No split-off lemmas.
`SheafOfModules.exists_stalk_directSum_linearEquiv` remains fully proved in the
adopted source library (node `lem-pc-stalk-direct-sums`). No other proof body changes.

## No longer needed

The duplicate module `Sheaf.Topology.StalkDirectSums` and its consumer's import
of it are no longer needed. The source twin supplies the result with the exact
same germ formula and without the unused commutativity argument. Its proof
dependencies and the existing DAG node remain needed; no DAG node is removed.
No new node is introduced, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not identify the retirement assignment, but
`coord/queue.tsv` and the 2026-10-20 retirement hand-off do: this item has zero
holes and is a duplicate to retire. The inventory's second consumer,
`Sheaf.AlgebraicGeometry.SupportedCompactDetectorModel`, is already absent from
the current tree; the adopted source replacement already imports and uses the
source theorem. The upstream statement omits `_hcomm`, so its signature is
stronger than the retired copy; there are no old-signature theorem calls to adapt.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
