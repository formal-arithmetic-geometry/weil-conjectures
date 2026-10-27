## What changed

The assigned theorem now proves `Nonempty (FiniteCompatibility d)` by explicit assembly. The two `LevelComm` families are proved from `Scheme.proEtaleConstantInverseImageMap_naturality`; the four remaining compatibility fields are provided by four strictly smaller named statements in the new proof-only modules `OpenIso`, `OpenNormalized`, `OpenEvaluation`, and `ProperEvaluation`.

## Proved and sorry left

Closed the sorry in `systemRestrictionFiniteNormalization`. Four strictly smaller field statements remain sorry: `finiteCompatibility_openIso`, `finiteCompatibility_openNormalized`, `finiteCompatibility_openEvaluation`, and `finiteCompatibility_properEvaluation`, each with its own DAG node under `dag/nodes/sec-smooth-purity/`.

## No longer needed

The original six proof dependencies listed by the parent node were not needed for the explicit assembly and were removed from its `proof_deps`; the proof uses the four split field nodes and the existing constant inverse-image naturality declaration.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan treated the four finite compatibility fields as one monolithic calculation. The Lean structure exposes them as independent fields, so the delivery reduces the target to those four strictly smaller statements and proves the assembly itself. No target statement or definition was changed.

## New nodes

Added `lem-sp-system-restriction-finite-open-iso`, `lem-sp-system-restriction-finite-open-normalized`, `lem-sp-system-restriction-finite-open-evaluation`, and `lem-sp-system-restriction-finite-proper-evaluation`, each stated in a separate module with source and proof obligations documented in its docstring.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SystemRestrictionFiniteNormalization": "c871b2c48d1c58967fd85dcf8a8a76e3ea81ed3c", "Sheaf.Paper.SystemRestrictionFiniteNormalization.OpenEvaluation": "0fecf9e2720687c8d3e4b6c5aeaa29469e29f4c5", "Sheaf.Paper.SystemRestrictionFiniteNormalization.OpenIso": "6f0c7858de517520df1e0533209f3779efc3f2e2", "Sheaf.Paper.SystemRestrictionFiniteNormalization.OpenNormalized": "9298fbe90bbf0fd2222a845909bd127c99e0acc5", "Sheaf.Paper.SystemRestrictionFiniteNormalization.ProperEvaluation": "6080e904ecb614b56b2af42f27636dd12b5eeb07"}, "results": {}, "time": "2026-10-28T01:05:33+0800", "transitive": 0, "version": 1}
```

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
