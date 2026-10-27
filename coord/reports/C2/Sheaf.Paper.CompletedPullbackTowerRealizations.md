## What changed

Restored `set_option Elab.async false` and the original direct bodies of the exposed
`pullbackTensorReferencePullbackModel` and `pullbackTensorReferenceTensorModel` definitions.
The finite level definition remains in its measured compile-time module. Replaced the
fixed-level naturality theorem with the actual adjacent `n+1 → n` transition square.
Proved the tower existence construction with `NatTrans.ofOpSequence` and
`NatIso.ofComponents`, and proved the target uniqueness by `Iso.ext` and
`NatTrans.ext`. Removed the six continuation modules and their marker declarations.

## Proved and sorry left

Closed `WeilConjectures.pullbackTensorTensorTower_existsUnique` (1 of 1 item sorries).
The existence construction `WeilConjectures.pullbackTensorTensorTower_exists` is also
fully proved in its strictly simpler helper node. One sorry remains, in
`WeilConjectures.pullbackTensorTensorTowerLevel_transition`; it states the genuine
adjacent transition square and records the component calculation needed by the
construction.

## No longer needed

The old fixed-level naturality theorem and node
`lem-pur-completed-pullback-tower-transition-square` are removed. The six continuation
modules (`CompletedPullbackTowerRealizationsBase`, `Helpers`, `Middle1`, `MiddleIso`,
`Middle2`, and `End`), their `partitionMarker` declarations, the duplicate existence
core, the public helper copies, and the NaturalCoherentTensorLevel/Base split are not
needed. The unforced async flip and exposed model-body rewrites are reverted.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified that a fixed-level `.hom.naturality` equation
was not the adjacent transition square. The prior existence-only sorry was not a proof;
this repair proves that existence construction and leaves only the strictly simpler
transition square for follow-up. The item node now records the level transition and
existence helper used by its target proof.

## New nodes

`def-pur-completed-pullback-tower-tensor-level` records the moved finite component.
`lem-pur-completed-pullback-tower-level-transition` records the adjacent transition
square. `lem-pur-completed-pullback-tower-iso-existence` records the fully proved
existence construction.

## Related modules compiled before delivery

21 related module(s) compiled against this delivery by deliver3.py: 20 OK, 1 SLOW.

```json
{"capped": false, "direct": 21, "left_out": 0, "own": {"Sheaf.Paper.CompletedPullbackTowerIsoExistence": "5efec888f968452ddb6187ba4e4cf2bbf1a2aaa1", "Sheaf.Paper.CompletedPullbackTowerRealizations": "12f6b85e5b37923fb0273cbb36b0833c83668a58", "Sheaf.Paper.CompletedPullbackTowerTensorLevel": "77d77d570d8a52407962542fa339f1cf6d241e51", "Sheaf.Paper.CompletedPullbackTowerTransitionSquare": "349e8bbf8f6170af09f57f664178afc99855da1b"}, "results": {"Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives": {"hash": "75e9ccdbca18a51593a3b5c976468f97340718c4", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorConstruction": {"hash": "77c9c7f0e7c8b256cb97d10f80c8c680d46039f4", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorEvaluationCube": {"hash": "5bea46e70c7c60f91238c0a4e55791c40eae92c8", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives": {"hash": "b3e5cb10406f66f5afc14a0ba7dc1e6ce9ce1258", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorProofImplementations": {"hash": "3be0afc15cba9bf9669411c55a1941f9b5479df3", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorSignedRepresentatives": {"hash": "1ae46c1d5ee0363cf21b46d354c775db2bcab068", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorUnitFromAssociativity": {"hash": "85fdbf49bec38a1ec7f905621779e3cba4ae7ae2", "status": "OK"}, "Sheaf.Paper.IntegralPullbackReductionAugmentation": {"hash": "beab41e42c31ad37776a8dd78423905ca1de8615", "status": "OK"}, "Sheaf.Paper.IntegralPullbackReductionAugmentationDescent": {"hash": "fdaff29408cae3b89555b6e3617c9724df00cc67", "status": "OK"}, "Sheaf.Paper.IntegralPullbackReductionAugmentationGood": {"hash": "f80701fafa98351ef3504442773722289477988b", "status": "OK"}, "Sheaf.Paper.IntegralTensorReductionAugmentation": {"hash": "52c812bc6b1f1a034f5c38e845038fdccc13332c", "status": "OK"}, "Sheaf.Paper.LimitUnitRoosNormalization": {"hash": "1d33de3fbb3c86090bb8c322ae41307a15aad7fd", "status": "OK"}, "Sheaf.Paper.PodReindexingReductionTensorSquare": {"hash": "5d319dce971fb8068cf45dfb1bb25c9f5b856453", "status": "OK"}, "Sheaf.Paper.ScalarExtensionTensorModelNormalization": {"hash": "4b57fb2dac2a53c8e5e04c3e71fe33455eb50ccf", "status": "OK"}, "Sheaf.Paper.TensorReductionCanonicalSquare": {"hash": "5f030e97c3e8e34ed87a0ffd9aad11080aacb68b", "status": "OK"}, "Sheaf.Paper.TensorReductionFiniteDegreeLift": {"hash": "5f16b7cf520eb8a4a2a966701d86ec0bcda38f69", "status": "OK"}, "Sheaf.Paper.TensorReductionFiniteProjection": {"hash": "b865264c5ecad525ee6338e6c65489dd54edbc54", "status": "SLOW"}, "Sheaf.Paper.TensorReductionOrdinaryModel": {"hash": "8a8228a0055375017bcc58f6c1da7f261aed35a7", "status": "OK"}, "Sheaf.Paper.TensorReductionOrdinaryTranspose": {"hash": "1104d56d2b3925ab4627133914dff54d285c5c55", "status": "OK"}, "Sheaf.Paper.TensorReductionStrictDerivedSquare": {"hash": "a884df23f43c5290a5d22698f754e4858e84e441", "status": "OK"}, "Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation": {"hash": "f775c24c6c23208f7bd0d8baa36dc0ae86ea076b", "status": "OK"}}, "seconds": 139, "time": "2026-10-28T06:24:36+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
