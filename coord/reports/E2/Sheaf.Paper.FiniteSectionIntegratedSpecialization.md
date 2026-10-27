## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.integratedSpecialization_baseChange` by
constructing a normal-cone exchange witness, applying the normalized specialization factor,
then applying the inverse normal-bundle integration factor and reassociating the composites.
The three strict intermediate factors are in the new modules
`FiniteSectionIntegratedSpecializationNormalExchange`,
`FiniteSectionIntegratedSpecializationSpecializationBaseChange`, and
`FiniteSectionIntegratedSpecializationIntegrationBaseChange`. The item imports these modules
privately for the proof.

## Proved and sorry left

Closed the item theorem `integratedSpecialization_baseChange` (one hole). The delivery adds
three named split-off theorem holes: `normalExchange_exists`,
`specialization_normalExchange`, and `normalExchange_integration`, in the three new modules
and DAG nodes listed under `## New nodes`. The existing `normalSectionMap_isIso` and
`integratedSpecialization_normalization` declarations remain proved.

## No longer needed

The item's direct proof route no longer needs the former unsplit proof dependencies
`lem-trf-section-rees-base-change-etale`, `lem-trf-section-exceptional-fibre-coherence`, and
`lem-pur-vector-trace-geometric-descent`; their roles are represented by the strict factor
nodes and the imported APIs used by those factors.

## Where the brief, the DAG or earlier work was wrong

The previous item left the full arbitrary finite-coefficient base-change equality as one
unsplit theorem. The proof naturally separates into the normal exchange, specialization, and
integration equations, so those strict components are recorded as parallel stage-3 nodes.

## New nodes

`lem-sp-finite-section-integrated-specialization-normal-exchange` records the canonical
normal-cone exchange witness and is stated in
`Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange`.

`lem-sp-finite-section-integrated-specialization-specialization-factor` records the
normalized zero-fibre specialization square and is stated in
`Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange`.

`lem-sp-finite-section-integrated-specialization-integration-factor` records the inverse
normal-bundle integration square and is stated in
`Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteSectionIntegratedSpecialization": "c255dd8fd464dab1fe38f6c1174284eb808974ff", "Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange": "1b7bcf71d71fdab9583bd4b4098a4b39759c23dc", "Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange": "ce3ef66c73f0d26461d6a58152302217eec07254", "Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange": "a6b8f4464897c9c5202d41a48d590aee77363bcf"}, "results": {}, "time": "2026-10-28T01:31:36+0800", "transitive": 0, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
