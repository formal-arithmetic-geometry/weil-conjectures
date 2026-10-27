## What changed

Completed all previously proved portions of `Sheaf.Paper.SpecifiedHomScalarEvaluation` and assembled
`specifiedHomScalarChain` from strict existence and uniqueness substatements. The rational naturality,
rational unit, and rational tower clauses are assembled from corresponding strict substatements; the
rational evaluation clause remains proved by reflexivity. Added five statement-only modules carrying the
remaining representative-chain and rational coherence obligations, and updated the sandbox DAG copy to
record these proof dependencies.

## Proved and sorry left

The item module has zero `sorry`s. The following declarations are proved:
`specifiedHomScalarEvaluation`, `specifiedHomScalarChain`, `specifiedHomScalarCoherence`,
`specifiedHomScalarRational`, and `specifiedHomScalarRationalEvaluation`.

Five strictly smaller obligations are split off, one in each new module:

- `specifiedHomScalarChain_exists` (`lem-zl-specified-hom-scalar-chain-existence`)
- `specifiedHomScalarChain_unique` (`lem-zl-specified-hom-scalar-chain-uniqueness`)
- `specifiedHomScalarRational_naturality` (`lem-zl-specified-hom-scalar-rational-naturality`)
- `specifiedHomScalarRational_unit` (`lem-zl-specified-hom-scalar-rational-unit`)
- `specifiedHomScalarRational_tower` (`lem-zl-specified-hom-scalar-rational-tower`)

Each split declaration has exactly one documented `sorry`; none occurs inside a definition.

## No longer needed

None. The parent route still uses the declared integral operation and completion dependencies; the
new modules retain the representative and localization dependencies needed by their statements.

## Where the brief, the DAG or earlier work was wrong

The original DAG grouped the full chain construction, arbitrary localized naturality, and both rational
coherence equations into three large theorem holes. Their Lean interfaces are independent strict clauses,
so the parent is now a real assembly of five strictly simpler statements. No target statement or
mathematical definition was changed.

## New nodes

The five nodes listed under “Proved and sorry left” are new stage-3 split nodes. Their Lean files and
node records are included in this delivery.

New node identifiers: `lem-zl-specified-hom-scalar-chain-existence`,
`lem-zl-specified-hom-scalar-chain-uniqueness`,
`lem-zl-specified-hom-scalar-rational-naturality`,
`lem-zl-specified-hom-scalar-rational-unit`, and
`lem-zl-specified-hom-scalar-rational-tower`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SpecifiedHomScalarChainExistence": "5be5b579e3bd031f2464bb371d1dcc49db5ce5c5", "Sheaf.Paper.SpecifiedHomScalarChainUniqueness": "e448738fa98fadb958626a57b6765b5020755e79", "Sheaf.Paper.SpecifiedHomScalarEvaluation": "835e9cd05e3d1b1d2f94bc804c63c84ebeefa92a", "Sheaf.Paper.SpecifiedHomScalarRationalNaturality": "f015a2348706a32814959c24dc2c3d4c1a419023", "Sheaf.Paper.SpecifiedHomScalarRationalUnit": "f9d3b869e0b696cb9cb156106c13c868afc22c90", "Sheaf.Paper.SpecifiedHomScalarTower": "6803aba5f03e5147d802a7d82d583c0e32f780e0"}, "results": {}, "time": "2026-10-28T04:45:10+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
