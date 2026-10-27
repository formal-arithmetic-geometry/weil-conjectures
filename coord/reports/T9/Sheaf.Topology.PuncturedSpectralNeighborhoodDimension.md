## What changed

Replaced the sole proof hole in
`Sheaf.Topology.PuncturedSpectralNeighborhoodDimension` without changing its
statement, public imports, definitions, or visibility. The existing proof-only
imports are both used. The compact open neighborhoods of Z, ordered by reverse
inclusion, give the directed system of punctured compact opens. The existing
spectral-limit theorem supplies spectrality after checking the transition maps,
compatible tuples, and initial topology explicitly.

For dimension, Mathlib's strictly monotone map on irreducible closed sets lifts
any chain to the ambient space. Choose a point in its first member and a
specialization in Z; the closure of that specialization is strictly smaller
than the first lifted member. Prepending it proves the dimension drop. Updated
steps 4–5 of the existing node to record this simplification. No interface
change or consumer adaptation is needed.

Validation: the full item compiled cleanly through `lcompile.py` in 2.2 seconds
(exit code 0), with no warnings or remaining holes.

## Proved and sorry left

Closed 1 hole:
`Topology.spectralSpace_puncturedGeneralizations_and_dimension`
(node `lem-sfb-punctured-spectral-neighborhood-dimension`).

No sorry remains in the item. Added 0 holes; split off 0 statements.

## No longer needed

No imports, dependency nodes, or modules are pruned. Both
`WeilConjectures.Topology.SpectralGeneralizations` and
`Sheaf.Topology.SpectralDirectedLimit` are used. The dimension argument needs
neither generic points nor sobriety of the punctured subspace, but this removes
no dependency because spectrality still uses the spectral-space structure.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken interface was found. The generic-point argument
in steps 4–5 is correct but unnecessary: closing each chain member directly
and choosing any point of its first member suffices. The three empty endpoint
cases are covered without a separate case split. A related dimension-only
lemma in `TopDegreeAbelianNeighborhoodZero` is private and cannot be reused;
it also uses generic points. The current proof establishes the same dimension
drop directly from Mathlib's chain API.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
