## What changed

The item theorem now assembles two strict subclaims.  The data subclaim constructs an
etale derived complex with the required bounded cohomology and finite local constancy;
the comparison subclaim supplies its fixed-realization comparison with the pulled-back
object.  The item module imports these two new modules and proves the original theorem
by unpacking and reassembling their conclusions.

## Proved and sorry left

`AlgebraicGeometry.Scheme.lisse_finite_level_etale_model` is proved by a real Lean
assembly proof.  Two strict subclaims remain as named sorries:

- `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_properties`, node
  `new-lem-weil-pbc-lisse-finite-level-etale-model-data`;
- `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison`, node
  `new-lem-weil-pbc-lisse-finite-level-etale-model-comparison`.

No definition contains a sorry.

## No longer needed

The item proof no longer needs the direct imports
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.Paper.ProEtaleLisseOrigin`, or
`Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection`; their planned work is now
encapsulated by the two strict subclaims.  The original statement dependencies remain
available through `Sheaf.Paper.LisseTowerEtaleDescentData`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated construction of the etale model and its
fixed-realization comparison as one monolithic step.  The route is valid after splitting
those clauses into two strictly smaller statements; no target or existing statement was
changed.

## New nodes

`new-lem-weil-pbc-lisse-finite-level-etale-model-data` records the etale model with its
bounded and finite locally constant cohomology, stated in
`lean/Sheaf/Paper/LisseFiniteLevelEtaleModelProperties.lean`.

`new-lem-weil-pbc-lisse-finite-level-etale-model-comparison` records the separate
fixed-realization comparison, stated in
`lean/Sheaf/Paper/LisseFiniteLevelEtaleModelComparison.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleModel": "e08b1ea5be1ff4d763c3228fafbd29d12625ce23", "Sheaf.Paper.LisseFiniteLevelEtaleModelComparison": "397aa860781f459f9c7cec2f32c75c25e4e7a105", "Sheaf.Paper.LisseFiniteLevelEtaleModelProperties": "9931f4f52f0ac09cf380cb99bc244869c82f0706"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleDescent": {"hash": "bdcdcb3186f0e12e37a1aae23babc13c1f097fcf", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T06:29:26+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
