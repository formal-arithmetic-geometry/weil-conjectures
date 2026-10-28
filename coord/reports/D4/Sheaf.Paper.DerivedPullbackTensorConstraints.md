## What changed

Proved `WeilConjectures.pullbackTensorCommonComposition_exists` from the existing
`commonStagePullbackCompComponent` and its every-stage representation theorem. At each
finite coefficient field, the explicit compositor agrees with the chosen normalized
compositor by `pullbackTensorRationalComposition_existsUnique`.

Added the proved helper
`WeilConjectures.commonStagePullbackRationalComposition_localization` in
`Sheaf.Paper.CommonStagePullbackCompositionLocalization`. It specializes
`CategoryTheory.conj_eqToHom_iff_heq` to the explicit finite-stage compositor. This
calculation is isolated because profiling found about 14 seconds spent elaborating
its equality transports in the large item file. The item imports the helper only for
its proof. All existing statements, definition bodies, public attributes and public imports
are unchanged. The composition proof locally treats the component, explicit rational
compositor and scalar-localization category as irreducible, avoiding expansion of
their constructions during unification. Updated the composition-existence node's proof route and dependencies.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.pullbackTensorCommonComposition_exists`
(`lem-pur-derived-pullback-tensor-constraints-common-composition-existence`).
Added zero holes. The new localization helper is proved.

The five remaining original holes are:

- `WeilConjectures.pullbackTensorCommonAssociator_exists`
  (`lem-pur-derived-pullback-tensor-constraints-common-associator-existence`).
- `WeilConjectures.pullbackTensorCommonBraiding_exists`
  (`lem-pur-derived-pullback-tensor-constraints-common-braiding-existence`).
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
  (`lem-pur-derived-pullback-tensor-constraints`).
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
  (`lem-pur-derived-pullback-tensor-constraints`).
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`
  (`lem-pur-derived-pullback-tensor-constraints`).

The composition proof uses the existing, still admitted
`commonStagePullbackCompComponent_stage_representation` from
`lem-zl-common-stage-pullback-comp-stage-representation`. It adds no new assumption
or split-off obligation in place of that existing theorem.

## No longer needed

No import or module was removed. The original scalar-extension construction is reused
through the existing component representation theorem rather than reconstructed in
this item. Its underlying dependencies remain needed by that theorem.
`lem-h3-common-stage-pullback-composition-transition` is not needed by this proof:
component naturality along an arbitrary arrow is unnecessary for the representative
existence statement. No withdrawal is proposed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The existing component representation theorem
already supplies the common-stage construction required here, leaving only the
finite-stage normalization identification. The unit has no prescribed realized proof
steps to bypass.

## New nodes

`lem-pur-common-stage-pullback-composition-localization` records the proved localization
identity for the explicit finite-stage compositor. Its source is the finite-stage
composition convention (Stacks 07A4, 0941), and its proof is equality transport using
Mathlib's `conj_eqToHom_iff_heq`. LeanFinder, LeanSearch, Loogle and grep searches are
recorded in the node. This is a proved helper, not a new admitted intermediate theorem.

## Related modules compiled before delivery

31 related module(s) compiled against this delivery by deliver3.py: 10 INFRA, 21 OK.

```json
{"capped": false, "direct": 31, "left_out": 0, "own": {"Sheaf.Paper.CommonStagePullbackCompositionLocalization": "bd9c904065645ca48c73f78696e08f57cb5bf150", "Sheaf.Paper.DerivedPullbackTensorConstraints": "1494a8ef1b0bed3a423f556e93d36aa574e90faf"}, "results": {"Sheaf.Paper.CanonicalRationalPullbackTensorCompositionLeftLocalization": {"hash": "432f3d6d3cc50d38db7c9faa930a7f5d1e21530e", "status": "OK"}, "Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization": {"hash": "4722ee032a97965840a8547ba8eb07f117b6a17f", "status": "OK"}, "Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation": {"hash": "88513d8437f5750840c6a135535f048cae1f0ca7", "status": "OK"}, "Sheaf.Paper.CommonStageCompositorIntegralNormalization": {"hash": "745d65f1b68344e45b623d84221885a608215d44", "status": "INFRA"}, "Sheaf.Paper.CommonStageCompositorRepresentative": {"hash": "3fd98161cbb4fab422191dae697c57b59c56fff0", "status": "INFRA"}, "Sheaf.Paper.CommonStageCompositorWord": {"hash": "4985ebb1fa8d4a49becb163eb5484b8fed748e98", "status": "OK"}, "Sheaf.Paper.CommonStageNormalizedComposition": {"hash": "9e28eb631312fe093148d0bd328b6714174aae7d", "status": "OK"}, "Sheaf.Paper.CommonStageRationalCompositionNaturality": {"hash": "1d5140cd42012d563faa3c4e2b1ad8aa7a9b521b", "status": "OK"}, "Sheaf.Paper.CommonStageTensorRightUnitorNaturality": {"hash": "bc16e017909fd71327f96e22e866dcaa16130d6c", "status": "OK"}, "Sheaf.Paper.DerivedPullbackTensorIso": {"hash": "94b352bd0fa17727d2fce8268ad5ee6ddcedc0c4", "status": "INFRA"}, "Sheaf.Paper.IntegralBraidingNaturality": {"hash": "1aff23e248dc3fa5a5a484b67fc66abb6b5cbd3d", "status": "OK"}, "Sheaf.Paper.IntegralPullbackTensorAssociatorNaturality": {"hash": "c565b0606864513f7091ea13580d322f0fcb4fd9", "status": "INFRA"}, "Sheaf.Paper.IntegralPullbackTensorCompositionReduced": {"hash": "1ae82b80992d4412acd53bd91e60b963840ee7f4", "status": "INFRA"}, "Sheaf.Paper.IntegralPullbackTensorCompositionReducedFiniteStage": {"hash": "6a6c3518f42bb688a0a58d5f3300213c4c3175bc", "status": "OK"}, "Sheaf.Paper.PodCommonStageCompositorNaturality": {"hash": "1518b88eb26ca5542fc1fec38a56b7266ff35584", "status": "OK"}, "Sheaf.Paper.PodReindexingTensorFamilyTensorConstraints": {"hash": "a75f7a2a220c64d791c5969e915fd1ed2367a36e", "status": "INFRA"}, "Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence": {"hash": "c0051d160e71344224dd4886fa4ed67dd6cb8748", "status": "OK"}, "Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative": {"hash": "3f0baed801312cc0af5d0874b2fce9b9c548c124", "status": "OK"}, "Sheaf.Paper.PullbackTensorCommonStageUnitCoherence": {"hash": "b8abb575605641e4569ea7ba59889943872c1828", "status": "OK"}, "Sheaf.Paper.PullbackTensorCompositionCoherence": {"hash": "d76c6e6b4b555f3c5799a14f929dbdd77b749070", "status": "OK"}, "Sheaf.Paper.PullbackTensorIntegralCompositionCoherence": {"hash": "91bc7233903b5dd77047a87b82b079efd8f37b7e", "status": "OK"}, "Sheaf.Paper.PullbackTensorIntegralUnitCoherence": {"hash": "3d4ebd50f7e09972fa743a624fe135508a855687", "status": "OK"}, "Sheaf.Paper.PullbackTensorIntegralUnitExistence": {"hash": "8b1f2623aa2e1e03f9a110aa7506ae433153534b", "status": "INFRA"}, "Sheaf.Paper.PullbackTensorIntegralUnitUniqueness": {"hash": "24f26f6bbd44ad3dfd039b1c3d90f81e7407148c", "status": "OK"}, "Sheaf.Paper.PullbackTensorRationalCompositionCoherence": {"hash": "320b5e606cf5d317950133d9d54cab76098a9853", "status": "OK"}, "Sheaf.Paper.PullbackTensorRationalUnitCoherence": {"hash": "f099bf9bd432d2e4aa96cbc8ddc5141355de6857", "status": "INFRA"}, "Sheaf.Paper.PullbackTensorUnitCoherence": {"hash": "80f1958454b53c03abd72e2c5dfdf52abe087d96", "status": "OK"}, "Sheaf.Paper.RationalBraidingScalarCompatibility": {"hash": "70a32f7d1bed1bef7b7ed1d330b0d91c6de1f1f4", "status": "INFRA"}, "Sheaf.Paper.RationalBraidingScalarSquare": {"hash": "82ab57e819a125b773cea6a25e89057ea29558d0", "status": "OK"}, "Sheaf.Paper.RationalPullbackTensorAssociatorNaturality": {"hash": "8c27942322a017b58d2df33d3ec1594fd9150e6f", "status": "INFRA"}, "Sheaf.Paper.RationalTensorAssociatorScalarSquare": {"hash": "09471931e1ac7d8bd455488d04b9997bf7d945a0", "status": "OK"}}, "seconds": 156, "time": "2026-10-28T11:33:29+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
