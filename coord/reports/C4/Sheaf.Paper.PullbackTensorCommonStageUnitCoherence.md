## What changed

Proved `WeilConjectures.pullbackTensorCommonStageUnitCoherence` from the existing rational
unit coherence and normalized finite-stage representative formulas. Construct the comparison
at a finite stage, check both equations there, and use cancellation at the source unit to
identify all such constructions. The left rational unitor naturality proof is a private
faithful-reduction and scalar-localization calculation. Generic private lemmas carry out
the two representative conjugations and unit cancellation.

Reused the proved right-unitor naturality calculation after replacing its unnecessary parent
import with `DerivedPullbackTensorConstraints`. Its Lean signatures and proof bodies stay
unchanged. Local category caches reduce its compile from 111 seconds to about 22 seconds.
Corrected its DAG's owning-definition citation correspondingly. Change record:
`coord/changes/C4-unit-naturality-import.md`.

## Proved and sorry left

Closed one hole: `WeilConjectures.pullbackTensorCommonStageUnitCoherence`
(`lem-pur-pullback-tensor-common-stage-unit-coherence`). Zero holes added; zero holes left in
the item or adapted module. Validation: the full proof compiled in 29.2 seconds with profiling removed. The adapted
right-unitor module compiled in 22.1 seconds. Its unchanged direct consumer
`Sheaf.Paper.CommonStageTensorLineCoherence` compiled against the sandbox modules in 13.4
seconds; its temporary source copy was removed after checking. The proof uses the existing holed
rational coherence and
constraint declarations; they remain their existing items. All helpers are proved.

## No longer needed

The right-unitor naturality module does not need its former public import
`Sheaf.Paper.DerivedPullbackTensorIso`, or the corresponding parent theorem node
`lem-pur-derived-pullback-tensor-iso`; it needs the existing constraint module instead.
The parent module remains used elsewhere and is not withdrawn.

No item dependency is pruned. The separate scalar-tower calculation in the former proof plan
is unnecessary: each finite-stage comparison is identified by its left equation at the
source unit. No new unproved transport obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The right-unitor naturality DAG retained a citation to the parent comparison theorem after
its unit and unitor definitions had moved to the constraints module. Its Lean parent import
likewise introduced an avoidable cycle for using naturality to prove unit coherence.
The corrected citation and import preserve exactly the same objects and theorem.

The current live queue lists this item as a proof with one hole, and has no build-error or
rework record. There is no assigned zero-hole repair. No theorem statement or target changes.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CommonStageTensorRightUnitorNaturality": "bc16e017909fd71327f96e22e866dcaa16130d6c", "Sheaf.Paper.PullbackTensorCommonStageUnitCoherence": "b8abb575605641e4569ea7ba59889943872c1828"}, "results": {"Sheaf.Paper.CommonStageTensorLineCoherence": {"hash": "dcced6590728bd42d162c71f4d692e0c275b740a", "status": "OK"}, "Sheaf.Paper.PullbackTensorUnitCoherence": {"hash": "80f1958454b53c03abd72e2c5dfdf52abe087d96", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T06:35:18+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
