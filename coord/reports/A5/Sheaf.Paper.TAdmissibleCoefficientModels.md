## What changed

Restored `Sheaf.Paper.TAdmissibleCoefficientModels` from its quarantine archive, verbatim.
The assigned defect is the missing source after the cluster-restore rollback, as recorded
in `coord/rework.tsv`; the preserved definitions themselves need no mathematical change.
All nine declarations and four public imports are reinstated, including the canonical
section-ring/scalar map, t-admissibility, scalar local models, ordinary derived ambient
category, dualizability, local component condition, and restricted standard t-structure.

Change record: `coord/changes/A5-t-admissible-coefficient-models-restoration.md`.
The existing definition node and all parent dependencies remain unchanged.

The restored module compiles via `lcompile.py`. A separate, excluded `__probe.lean` file
elaborates the full four-conjunct statement of the quarantined direct consumer using only
the restored public import. It also prints axioms of all nine restored declarations:
every one uses only `propext`, `Classical.choice`, and `Quot.sound`.
Source comparison confirms byte-for-byte equality to the archive. Live downstream scan
reports no importers; the quarantined direct consumer is recorded in the change record.

## Proved and sorry left

Definition restoration, not a theorem proof or decomposition. Original item holes: zero.
Holes closed: zero. Holes added: zero. Holes remaining in the delivered module: zero.
No new theorem, split, axiom, or hollow definition is introduced.
The quarantined consumer theorem `tAdmissible_dualizable_truncations` is outside this
packet and retains its separate assignment; this packet checks its statement only.

## No longer needed

None. No imports, declarations, nodes, modules, or unit steps are pruned. All twelve
statement dependencies of `def-zl-t-admissible-coefficient-models` remain necessary.
No archive or DAG attachment is withdrawn.

## Where the brief, the DAG or earlier work was wrong

This is the listed zero-hole restoration, rather than a module with a postponed proof.
The live source was absent after the cluster rollback, but the preserved archive
compiles against the current dependencies. No false statement or definition repair was
found. The missing live module is repaired by reinstating its actual definitions.
Searches for the specialized package find no replacement; existing generic dualizability,
section-ring reconstruction and finite constant local models are already reused.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
