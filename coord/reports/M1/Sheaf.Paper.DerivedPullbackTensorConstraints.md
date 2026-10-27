## What changed

Closed the uniqueness halves of the common-stage composition, associator, and
braiding constraints. Each uniqueness proof obtains the existence witness from a
strictly simpler named existence theorem and compares both isomorphisms at a
common finite coefficient stage. The three existence halves are recorded as new
named theorems in the item module and remain admitted for a subsequent worker.

## Proved and sorry left

Closed 3 of the original 6 holes:

- `WeilConjectures.pullbackTensorCommonComposition_existsUnique`
- `WeilConjectures.pullbackTensorCommonAssociator_existsUnique`
- `WeilConjectures.pullbackTensorCommonBraiding_existsUnique`

New existence holes remain in:

- `WeilConjectures.pullbackTensorCommonComposition_exists`
- `WeilConjectures.pullbackTensorCommonAssociator_exists`
- `WeilConjectures.pullbackTensorCommonBraiding_exists`

The original holes `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`,
`WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`, and
`WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique` remain unchanged.

## No longer needed

None. No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The parent constraints bundle existence and uniqueness. The uniqueness clauses are
strictly simpler once the corresponding representative existence is named: the
stagewise equations identify any two candidates at a common finite compositum.

## New nodes

- `lem-pur-derived-pullback-tensor-constraints-common-composition-existence`
- `lem-pur-derived-pullback-tensor-constraints-common-associator-existence`
- `lem-pur-derived-pullback-tensor-constraints-common-braiding-existence`

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 2 INFRA, 2 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.DerivedPullbackTensorConstraints": "389a178620ab9ccce1322285b1296454a60bfdf6"}, "results": {"Sheaf.Paper.DerivedPullbackTensorIso": {"hash": "94b352bd0fa17727d2fce8268ad5ee6ddcedc0c4", "status": "INFRA"}, "Sheaf.Paper.PullbackTensorCompositionCoherence": {"hash": "4c78efdf0eabfdb36779c5e21041679107812138", "status": "OK"}, "Sheaf.Paper.PullbackTensorUnitCoherence": {"hash": "bc27d0e58208dd5a5fa5afd3e50fef26671bde5b", "status": "OK"}, "Sheaf.Paper.RationalPullbackTensorAssociatorNaturality": {"hash": "8c27942322a017b58d2df33d3ec1594fd9150e6f", "status": "INFRA"}}, "seconds": 168, "time": "2026-10-28T03:06:01+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
