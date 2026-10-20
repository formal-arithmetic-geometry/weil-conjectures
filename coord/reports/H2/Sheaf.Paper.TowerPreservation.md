## What changed

Restored the assigned quarantined `Sheaf.Paper.TowerPreservation` in full. Repaired
`AlgebraicGeometry.Scheme.HasConstructibleAdicTowerModels` by using the existing
`FiniteLocallyClosedStratification` instead of the undefined
`LocallyClosedStratification`, with a public import of its owning module.
The replacement retains finite locally closed partitions and all scheme immersion
data without adding a constructibility hypothesis on strata. All seven public
declaration signatures, four completed-coefficient tower operations, quotient
structures, local-model fields, normalization requirements and AMP quantifiers stay.

The node's Lean note records the repair; its attachment and all statement and
proof dependencies are retained. There is no proof route to update: this is a
definition node with empty proof and proof_deps. Change record:
`coord/changes/H2-tower-preservation-finite-stratification.md`.

Validation: the final module compiled through lcompile with no errors or warnings
(2.0 seconds). The unchanged quarantined direct consumer AmplificationProper then
compiled in the same two-file set against the new sandbox output (2.6 seconds).
Live downstream analysis finds zero users because the item is quarantined; a combined
live/quarantine import traversal finds nine consumers, all listed and checked in
the change record. Only AmplificationProper mentions the public predicate directly;
its theorem signature requires no adaptation. No consumer source is delivered.

Searches: msearch grep `LocallyClosedStratification` returned no Mathlib hits;
Loogle `"Stratification"` returned zero hits; LeanFinder for a finite locally closed
scheme partition returned eight open-cover/prespectral/partial-map results, none
replacing the existing project interface. Direct rg located the exact finite
partition interface in Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification,
and its fields were read. Its existing node is def-constructible-stratification,
already reached through the bounded-constructible-tower statement dependency.

Edge cases: n=0 strata allow the empty scheme; no Noetherian or nonempty assumption
is added; arbitrary locally closed strata need not be constructible; all local
covering and AdicTowerLocalModel data remain exactly the archived ones. The positive
quotient indexing, all four source/target directions and all amplitude intervals
are unchanged. The unit's realized nodes and route are untouched.

## Proved and sorry left

Definition repair, with zero original holes and zero remaining holes. Holes closed:
none (0). Holes added: none (0). Split-off statements: none (0).
No declaration in this delivery contains sorry. The seven restored definitions and
abbreviations are towerFinitePullback, towerFiniteDirectImage, HasAdicLevelAmplitude,
HasConstructibleAdicTowerModels, HasTowerAmplitudeCompatibleModels,
PreservesBoundedConstructibleAdicTowers and HasTowerPreservation, in namespace
AlgebraicGeometry.Scheme. Imported existing theorem holes are unchanged. The
consumer's existing amplification_of_isProper hole is unchanged and not delivered.

## No longer needed

None. No imports, declarations, modules, nodes or dependency edges are removed.
Both existing public imports remain necessary for the coefficient tower operations
and AMP predicate. No quarantined module is withdrawn or replaced with an empty file.

## Where the brief, the DAG or earlier work was wrong

The rework diagnostic is accurate: the archive refers to the nonexistent
LocallyClosedStratification at line 65. The current canonical finite locally closed
interface has the name FiniteLocallyClosedStratification. The upstream Stratification
interface additionally requires constructible strata, so merely substituting that
name would strengthen this helper on non-Noetherian schemes. The delivered repair
uses the exact finite locally closed interface instead. There is no mathematical
statement change, new node, target edit or source-library edit.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
