## What changed

Retired `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`, following
its explicit retirement assignment in `coord/retire-items.tsv`. Both public
statements already have complete proofs upstream. The directed-order theorem
is in the upstream twin; the filtered-category theorem is in its extension.

Changed the sole current direct consumer,
`Sheaf.AlgebraicGeometry.ConstantTorsionAcyclicDevissage`, to import
`WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension`.
Only that proof import changes; all its declarations and proof bodies are
identical. Repointed the existing DAG node's Lean attachment to the upstream
directed theorem. The mathematical statement, dependencies, and unit route
stay the same.

Change record: `coord/changes/E9-retire-etale-directed-cohomology-colimit.md`.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: none (0).
Holes added: none (0). Sorries left in the delivered consumer: none (0).
No split-off statements or new nodes.

The two already proved declarations are retained upstream with identical
signatures: `AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isDirected`
and `AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isFiltered_coefficientSize`.

The migrated consumer compiled successfully through `lcompile.py` (9.3 s).
All four downstream modules then compiled together against the migrated consumer:
`ConstantTorsionAcyclicDevissage` (9.5 s),
`LocallyConstantTorsionLocalAcyclicity` (11.2 s),
`SmoothProperPrimeSpecialization` (6.1 s), and
`ModuleSpecializationAbelianIso` (6.7 s). The three unchanged sources were
copied temporarily for verification and are not part of this delivery.
Text comparison also verified identical signatures for both upstream theorems.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`.
Removed its only current import, from `ConstantTorsionAcyclicDevissage`, and
replaced it with the upstream extension import. Its duplicate private helper
`sections_isColimit` and duplicate public theorem bodies are no longer needed
in Sheaf; the complete upstream proofs remain intact. No mathematical node
or dependency is pruned: the existing node remains attached to the upstream
theorem. The historical `created.item` field of the acyclicity node is retained.

Current-source search and downstream inventory found no other direct or
quarantined importers. The other four consumers listed in the retirement
row had already migrated or retired before this session.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief described a proof obligation and earlier splits,
but the current item contains no holes. Its explicit retirement assignment
is the remaining work. The retirement table says the upstream twin lacks
the filtered-index theorem; it exists in the upstream extension module,
so no new proof, statement, or upstream modification is necessary.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
