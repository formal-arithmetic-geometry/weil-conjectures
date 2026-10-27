## What changed

The main theorem now performs real existential elimination from two strictly simpler
construction statements.  `ExceptionalProCompactSupportConstruction` states existence
of the pro-etale compact-support package, and
`ExceptionalSystemCompactificationComparisonConstruction` states existence of the
proper/open comparison for a fixed package.  The item imports both modules and combines
their results.  The two split statements retain the Construction 5.15 and Lemmas 4.10,
5.16 and 5.22 proof obligations in their own DAG nodes.

## Proved and sorry left

The original `exceptionalProperOpenOriginConstruction` hole is closed.  Two strictly
simpler holes are split off: `exceptionalProCompactSupport_exists` and
`exceptionalSystemCompactificationComparison_exists`, respectively in the two new
modules and recorded by the two new DAG nodes.

## No longer needed

The item proof does not directly import or use the four former proof dependencies
`lem-coef-semilinear-derived-sections`, `lem-weil-pbc-comparison-pullback`,
`lem-cbc-proetale-extension-zero-comparison`, and
`lem-weil-pbc-comparison-direct-image-canonical-mate`; those are now dependencies of
the split construction nodes.  No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG assigned the complete geometric construction and comparison to one
module, although the available interfaces naturally separate package construction from
comparison-data construction.  The delivered route makes that decomposition explicit;
the target statement and all interface definitions are unchanged.

## New nodes

`lem-sf-exceptional-pro-compact-support-exists` records the package-existence
subproblem and is stated in `Sheaf.Paper.ExceptionalProCompactSupportConstruction`.
`lem-sf-exceptional-system-comparison-exists` records comparison-data existence for a
fixed package and is stated in
`Sheaf.Paper.ExceptionalSystemCompactificationComparisonConstruction`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalProCompactSupportConstruction": "dba58252dda22fc83354194ad07929c79b0450bb", "Sheaf.Paper.ExceptionalProperOpenOriginConstruction": "5f1c67497084e7d29e64c928dcf18e941dfcb2cd", "Sheaf.Paper.ExceptionalSystemCompactificationComparisonConstruction": "d2928e7daaf968e22ec1ec1dda2d220e6a91dfc3"}, "results": {}, "time": "2026-10-28T03:25:58+0800", "transitive": 0, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
