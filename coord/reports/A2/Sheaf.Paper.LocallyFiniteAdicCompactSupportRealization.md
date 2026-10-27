## What changed

Restored lean/Sheaf/Paper/LocallyFiniteAdicCompactSupportRealization.lean from
its quarantine archive, preserving every public declaration and import.
In WeilConjectures.LocallyFiniteAdicCompactSupport.IntegralNormalization,
share the rationalized input and its common-stage inclusion using two local let
bindings. These replace five occurrences of the rationalized input and four
occurrences of the common-stage input. Every prescribed arrow and the final
six-arrow composite remain identical after zeta reduction.

This is the assigned quarantine/build repair, not a proof delivery for the
remaining existence theorem. No new statement, dependency, or axiom is introduced.
Change record: coord/changes/A2-native-compact-support-normalization-sharing.md.

Validation: the archived formula compiled against the current published build;
its normalization took 81,504 heartbeats. The revised formula took 52,347
heartbeats (about 36% less), and compiled without increasing the default
200,000-heartbeat limit or the single-file time limit. A temporary rfl check
compares the entire old and new predicates, including all implicit arguments.
The delivered file contains neither diagnostic imports nor profiling commands.

## Proved and sorry left

Holes closed: none (0 of 1). Holes added: none. Split off: none.

The one original hole remains:
WeilConjectures.LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization,
node lem-sf-locally-finite-adic-compact-support-realization. Its original complete
proof plan and source remain in its docstring and DAG record. No definition has a
hole. The existing native transport constructions are retained.

## No longer needed

None. No import, module, declaration, node, proof dependency, or unit step is
pruned. The mathematical route remains unchanged, so no node edit is necessary.
The quarantine archive and the item's Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The source is absent from lean/ because it was quarantined, not because its
mathematics was withdrawn. The rework row names the preserved source and reports
an elaboration timeout in IntegralNormalization followed by unavailable later
declarations. Against the current published build, the unchanged archive already
compiles; this delivery additionally reduces the repeated term elaboration that
made the normalization sensitive to dependency changes. Local irreducibility of
operationTransport and alternate backward transparency settings did not reduce
the measured heartbeat cost, so neither experiment is retained.

The consumer search finds zero current Lean importers, but the three DAG parents
still cite the item. They remain supported by the restored, definitionally equal
interface. No statement is disputed or weakened.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
