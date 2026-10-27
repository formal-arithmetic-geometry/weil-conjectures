## What changed

Repaired declaration-name collisions in the restored small-colimit strict-local comparison
and its original-stalk total-cohomology dependency. Both Sheaf theorem names now carry
_smallModel, matching the abelian small-model comparison's existing convention. Updated
the sole proof application and both existing DAG Lean records. All mathematical signatures,
proofs, imports, docstrings, dependencies and the sk-thm-p1 unit route are preserved.
The dependency module is unclaimed. No source-library file or archive is changed.

The item's existing proof applies the original-stalk total-cohomology comparison and
strict-local total-cohomology exchange, composes the first equivalences with the inverses
of the second, and uses injectivity and the two exchange equations. Both dependencies
remain necessary. Mathlib searches found no replacement: Loogle confirmed trans_apply,
LeanFinder returned generic additive-equivalence congruences, and grep found no
strict-henselization stalk comparison.

Change record: coord/changes/A3-projective-line-small-model-comparison-names.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off. No sorry remains
in either delivered module. The complete existing proofs are retained as:

- AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel
  (lem-weil-pbc-p1-strict-local-stalk-exchange-comparison).
- AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel
  (lem-weil-pbc-p1-original-stalk-total-cohomology-exchange).

This is a collision repair, not net proof-hole progress.

## No longer needed

None. No import, mathematical dependency, node or module is pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

C3 had already restored the quarantined item before this session; its zero-hole theorem
compiles on the server in 25.9 seconds. The restoration left a distinct small-model theorem
with the exact same name as its adopted canonical-model counterpart. A combined-import
check fails with the environment-already-contains error quoted in the change record.
The original-stalk dependency has the corresponding duplicate name, so both are repaired
in this packet. The archived modules are historical records and remain untouched.

The first lcompile attempt selected a local mirror missing Mathlib.olean. Server checks
use the supported LCOMPILE_NO_LOCAL=1 setting. No launcher tools are edited.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
