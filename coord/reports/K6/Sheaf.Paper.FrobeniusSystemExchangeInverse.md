## What changed

The item module now constructs the inverse finite compact exchange by conjugating
the already proved whole-system isomorphism through its specified evaluation
comparisons. Its forward map is identified by the new proof dependency
`Sheaf.Paper.SystemCompactExchangeEvaluation`.

The two integral inverse formulas use the private elementary lemma
`inverse_realization`: equality of forward maps identifies the integral
isomorphism with alpha, the functorial image of the system isomorphism, and beta;
reversing this composite yields precisely the stated inverse. No signature,
public definition, existing public import or target statement changes.

Change record: `coord/changes/K6-frobenius-system-inverse-proof-tools.md`.
The item module compiles in 33.2 seconds with one original sorry and one split-off
sorry. The new compatibility module compiles independently, and the unchanged
direct consumer `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` compiles in 8.8
seconds against the sandbox module.

## Proved and sorry left

The original holes addressed on
`lem-weil-frobenius-system-exchange-inverse` are:

- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_inverse`.
- `WeilConjectures.FrobeniusExchange.frobeniusSystemCompact_inverse_evaluation`.

The direct integral formula is proved without new assumptions. The compact system formula is a decomposition:
the parent constructs an isomorphism, identifies its hom by forward compatibility,
and calculates its inverse. Its strictly smaller forward compatibility step is
split off as one new hole:

- `WeilConjectures.FrobeniusExchange.systemCompactExchange_evaluation`, node
  `lem-weil-system-compact-exchange-evaluation`, in the new module
  `Sheaf.Paper.SystemCompactExchangeEvaluation`.

The compact integral inverse remains as one original sorry; its geometric-fiber
presentation mismatch needs a separate transport lemma and was deliberately left
untouched. Two original holes are closed, one hole is added for the decomposition,
net one hole removed. No data
is defined by an unproved existence statement. The new theorem asserts equality
of already constructed morphisms and carries a complete proof in words.

## No longer needed

No existing imports, modules or DAG nodes are removed. Every existing dependency
is retained, including the specified strict-tower realization functor and the
unit route. Only the new forward-compatibility proof import is added; the new
module is not publicly re-exported by the item.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The old plan still left the compact
forward evaluation calculation implicit; it is now named separately, with the
proper/open mate argument, exact comparisons and arbitrary unbounded domain.
It does not assume invertibility of the horizontal scheme maps. The identity,
empty-open, zero-system and positive index n+1 cases introduce no extra premise.

The current server queue row is a stage-3 proof item with three holes, with no
rework row or active return. Its build-error record reports an earlier bad import
of FrobeniusGeometricExchange. The present proof compile reaches all declarations
through that import. No missing or quarantined source was withdrawn.

## New nodes

`lem-weil-system-compact-exchange-evaluation` states only the forward evaluation
identity of the actual proper/open system composite through the two specified
operation comparisons and pullback-coordinate isomorphisms. It neither supplies
an inverse nor asserts system invertibility, and is a genuine proper part of the
parent argument. Its source is Zheng Construction 4.1 and Lemma 4.10, with the
explicit mate calculation written by the agent and Deligne Weil II (1.1.14) as
motivation. LeanSearch, LeanFinder and Mathlib source search found only generic
mate-pasting or sheaf-evaluation statements, not this normalized compatibility.
The new module compiles; the proof of this one named theorem remains deferred.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusSystemExchangeInverse": "6b3ed27640bd21a9ebfe16e8f35373c3fb5e0d09", "Sheaf.Paper.SystemCompactExchangeEvaluation": "bbfe912320a6f4d92e595e269de0e71a4f69677d"}, "results": {"Sheaf.Paper.NativeWeilScalarFrobeniusCounit": {"hash": "744aa481959f2b15900ab73a5dbb0a8c7018ac42", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T04:41:53+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
