## What changed

Restored Sheaf.Paper.AdicTorFlatCohomology from its assigned quarantine archive.
Changed the single obsolete LocallyClosedStratification reference in
PbcSuppliedModelCohomologyFlat to Stratification, the defining type of that retired
abbreviation. The current common-tower interface and supplied-model criterion use
this type already. Every existing proof, public import, declaration name, universe
and theorem signature is preserved.

The original archived module fails remote compilation with an unknown stratification
name, a subsequent heartbeat error, and an unknown supplied-model predicate.
The repaired module compiles through lcompile.py and lcompile.py --all with no
errors or warnings (6.3 seconds in the final all-files check). No resource limit
was increased. Local source searches found no external live or quarantined consumer
of this module's declarations. The final exact application also checks that the
independently stated supplied-model equivalence agrees with the repaired predicate.

Change record: coord/changes/A4-adic-tor-flat-stratification-restoration.md.
The existing DAG node lem-weil-pbc-adic-tor-flat-cohomology and its dependencies are
unchanged: expanding a retired abbreviation changes neither statement nor route.

## Proved and sorry left

Assigned interface restoration, with zero original holes and zero remaining holes.
Holes closed this session: none. Holes added: none. No statements were split off.

The complete existing proofs of AlgebraicGeometry.Scheme.pbc_adic_tor_flat_cohomology
and AlgebraicGeometry.Scheme.pbc_adic_flat_cohomology_reduction are restored and
compile unchanged from their existing declared dependencies. There are no sorry
occurrences in the delivered module, including definitions or private helpers.
The imported lower statements are not claimed proved by this restoration.

## No longer needed

None. No imports, nodes or modules are removed or claimed pruned. In particular the
quarantined item remains mathematically needed by its DAG parent, so it is restored
with its existing Lean attachment and dependencies, rather than withdrawn.

## Where the brief, the DAG or earlier work was wrong

The queue assigns a repair: the quarantined source already has complete proofs.
The actual defect is an obsolete abbreviation left behind by stratification API
retirement. F9's landed record shows that the alias was exactly Stratification;
J2's landed supplied-model restoration record specifically identifies this item
as needing the same replacement. This is the one-line restoration repair, not a
new proof or a change to the mathematical criterion.

The shortest-route searches found generic module flatness and adic-completion
lemmas, not a replacement for this sheaf-derived equivalence. Its existing route
already compiles after the alias expansion, so no mathematical rerouting is needed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
