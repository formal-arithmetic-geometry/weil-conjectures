## What changed

The item theorem now combines two split-off public statements: construction of the
normalized geometric squares and proper comparisons, and the independent composition
and identity laws for those comparisons. The item imports these proof-only helper
modules and combines their conclusions. The helpers remain `sorry` for parallel proof
work.

## Proved and sorry left

The item declaration `systemProperRestrictionCoherence` is proved by combining the two
strictly simpler helper statements. Two new named theorem holes remain:
`systemProperRestrictionData` in `lem-sp-system-proper-restriction-data` and
`systemProperRestrictionLaws` in `lem-sp-system-proper-restriction-laws`.

## No longer needed

No existing proof dependency import was removed. The item uses the compact-support
restriction data directly through the two new helper modules; the seven planned proof
nodes are not imported because no compiled declaration in the current library exposes
their exact system-level statements.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes a complete construction but the current library contains
only the data structures and the generic derived-comparison composition theorem. It
has no declaration that constructs the required arbitrary coefficient-map proper
comparisons, so the proof is reduced into construction and coherence-law statements.

## New nodes

`lem-sp-system-proper-restriction-data` records the construction subproblem.
`lem-sp-system-proper-restriction-laws` records the cocycle and unit subproblem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SystemProperRestrictionCoherence": "3e84d371eb82797e30c9f6b74a1c27ef1f90570d", "Sheaf.Paper.SystemProperRestrictionData": "8f4f503571ff32a51f4cb19f93ae3ee96b30fd32", "Sheaf.Paper.SystemProperRestrictionLaws": "f649ad621054314afe72ebacb4f314db1925f450"}, "results": {}, "time": "2026-10-28T00:58:10+0800", "transitive": 0, "version": 1}
```

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
