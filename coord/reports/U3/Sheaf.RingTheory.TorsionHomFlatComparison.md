## What changed

Completed the retirement assigned by `coord/retire-items.tsv`: withdrew
`Sheaf.RingTheory.TorsionHomFlatComparison` using `deleted.txt`, redirected the sole
consumer `Sheaf.RingTheory.TorsionExtensionFlatDescent` to the existing upstream
`WeilConjectures.RingTheory.TorsionHomFlatComparison`, and repointed the existing
node's Lean attachment. Only the consumer's one proof import changes; its two
applications, public imports, definitions, signatures and proofs stay identical.
The consumer is unclaimed.

The existing upstream theorem has the same fully qualified declaration name,
universes, hypotheses and conclusion. Normalizing the four underscore-prefixed
hypothesis names makes the signature text identical. Its proof is the same direct
primary-component comparison argument. No upstream file is edited.
Validation: the redirected consumer compiles in 7.0 seconds without warnings.
A text comparison confirms its sole change is line 14, the proof import.
`#print axioms` for the upstream theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The replacement import introduces no cycle according to `tools/import_direction.py`.
Change record: `coord/changes/U3-retire-torsion-hom-flat-comparison.md`.

## Proved and sorry left

This is a duplicate retirement with zero initial holes, zero holes closed,
zero holes added, and zero holes remaining in the assigned module. The existing
upstream `LinearMap.baseChange_bijective_of_ideal_power_torsion`
(node `lem-weil-pbc-torsion-hom-flat-comparison`) supplies the proved result.
No new theorem or split-off statement is introduced. The consumer remains sorry-free.

## No longer needed

Retired module: `Sheaf.RingTheory.TorsionHomFlatComparison`.
Removed consumer import: `Sheaf.RingTheory.TorsionHomFlatComparison`;
replacement: `WeilConjectures.RingTheory.TorsionHomFlatComparison`.
The blueprint node and its mathematical proof dependencies stay needed; only the
redundant Sheaf attachment is removed. No source-library declaration is removed
or weakened. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not identify the specific retirement, but the current
`coord/retire-items.tsv` lists it explicitly. The older kept-twins inventory says
DIFFERENT and suggests the upstream declaration may be missing; reading the current
upstream module shows it is present with the exact same type, up to binder names.
The item was already proved, so this delivery claims pruning rather than a newly
closed hole. The existing DAG proof accurately describes the retained upstream proof.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
