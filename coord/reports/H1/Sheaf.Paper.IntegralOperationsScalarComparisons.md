## What changed

Reduce `WeilConjectures.scalarPullbackOrdinary_existsUnique` to the new
`WeilConjectures.integralScalarPullbackRoosQuasiIso`. The parent now proves
Roos naturality, naturality on good representatives, invertibility after
localization, the prescribed representative square, and uniqueness in Lean.
The remaining lemma concerns only the chain quasi-isomorphism on one good
complex, with its finite generator and two Roos coordinate normalizations.

Add the fully proved generic
`CategoryTheory.functorSquareRepresentativeDescent`, using Mathlib
`FullyFaithful.preimageIso`, its map-preimage equation, and cancellation.
No scalar comparison is assumed in that general theorem.

Profiling and local abstraction still left the combined file over 60 seconds.
Extract the existing finite models into `IntegralOperationsScalarComparisonModels`,
the unchanged generic Roos construction into `ScalarRoosComparison`, and the
proved chain naturality and quasi-isomorphism specialization into
`IntegralScalarPullbackChainProperties`. The original module publicly re-exports
the existing declarations. A fresh parser comparison against the shared source
confirms all 46 original public signatures, all data bodies, and all previously
proved public proofs. A public-import audit also confirms that no original
public dependency is lost; only the two files containing relocated declarations
are newly public. The two finite-level holes are relocated, not added.
No existing Lean module other than the assigned item is edited.

All six delivery modules compile without debug options. The final private
cone-coordinate proof also compiles without warnings
(`d4047d29b019e5afae8ccd04`); its last changes replace flexible simplifications
with explicit lemmas and do not affect any signature, definition or attribute. The
six-module request `f9aab651b0822ca0c8a388ef` has exit code 0, without warnings.
The finite models retain all original private proof imports in their original
order, preserving the context in which their implicit instances elaborate.
Fresh consumer checks then pass for `LocalFrobeniusTransportNormalization`
(32.0 seconds, `80566d620f4f2a9c1ec3a6f7`) and
`AdicPurityScalarNaturalityData`
(53.7 seconds, `994c7f230803261abf2ed1cf`).
The consumer-inclusive request `b3f1535986124074d5be5153` also passed.
The earlier combined-model attempts took 66 and 71 seconds; the extracted generic
Roos and finite-model files now pass. The reachable project import graph has no
cycle. All six delivery Lean files have lines of at most 100 characters.

All 51 direct importers were checked. Across the completed sweep and fresh
clean checks, 41 pass; the remaining ten exceed the limit against both the
packet and the unchanged original item. The detailed comparisons below record
those cases rather than claiming that all importers pass. No source error
remains after the two missing-object attempts were superseded by actual checks.
All validation copies match their original hashes and are removed before
delivery. No consumer adaptation is included.

## Proved and sorry left

Baseline: five holes. Close
`WeilConjectures.scalarPullbackOrdinary_existsUnique`
(`lem-pur-integral-operations-scalar-extension`), and add only
`WeilConjectures.integralScalarPullbackRoosQuasiIso`
(`lem-pur-integral-scalar-pullback-roos-quasi-iso`). This is one decomposition,
not a net hole reduction. The parent supplies the complete descent argument;
the lower statement is strictly the quasi-isomorphism of a specified chain map.

The five holes left in the packet are:

- `WeilConjectures.scalarPullbackLevel_existsUnique`, relocated to the finite
  models (`lem-pur-integral-scalar-finite-comparison-models`).
- `WeilConjectures.scalarTensorLevel_existsUnique`, relocated to the same node.
- `WeilConjectures.scalarTensorOrdinary_existsUnique`, unchanged in the item
  (`lem-pur-integral-operations-scalar-extension`).
- `WeilConjectures.scalarOperationsOrdinary_tower`, unchanged in the same node.
- `WeilConjectures.integralScalarPullbackRoosQuasiIso`, the one new hole.

The original strict tower assembly clauses and `scalarGood` remain proved.
The new generic Roos coordinate/naturality helpers, chain naturality,
`scalarPullbackChainQuasiIso`, and general square-descent theorem are complete.
No axiom declaration, hollow definition, or arbitrary existential data choice
is introduced.

## No longer needed

No mathematical dependency, declaration, or module is pruned or withdrawn.
The unit route is unchanged. Existing proof dependencies remain needed by the
retained arguments, sometimes in an extracted module.

Remove these proof imports from the original file because only the extracted
finite-model proofs use them: `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Sheaf.Paper.IntegralScalarPullbackLevelReduction`, and
`Sheaf.Paper.IntegralScalarTensorLevelReduction`. They remain in the finite models.
The Roos tower-coordinate formula is proved directly from the mapping cone API;
`IntegralAmbientOperationModels` is not imported. This avoids adding twelve
existing project dependencies brought in by that larger exploratory import.
Those modules were not in the original item's closure, so this is not reported
as pruning existing target work.
Only the chain-property file imports `IntegralScalarPullbackRoosQuasiIso`.
The generic descent module needs only `Mathlib.CategoryTheory.Whiskering`;
its preliminary localization-predicate import was removed.

## Where the brief, the DAG or earlier work was wrong

The initial extraction omitted some original private proof imports from the
finite models. All seventeen original private import lines are now retained in
their original order. This adds no existing module to the original import
closure. Before restoring that context, unchanged `LocalFrobeniusTransportNormalization`
took 73 seconds against the packet, versus 32.8 seconds against the original
item. The fresh final check passes in 32.0 seconds. Likewise the unchanged
`AdicPurityScalarNaturalityData` initially took 60.5--67 seconds; its original
baseline passed in 37.4 seconds. The final-context check passes in 53.7 seconds.
An exploratory local opacity annotation in that consumer was not stable and
was reverted; no consumer source change is delivered.

No statement correction is needed. Both existing DAG records change only
permitted fields: the additive-Roos node changes its Lean attachment; the main
node changes its attachment and proof route. No quarantined declaration is
withdrawn or silently restored by this packet.

Compatibility timing failures are recorded explicitly. `CanonicalTateComparisons`
takes 79 seconds in the restored-set batch and 85 seconds in its final clean
single-file check; the original-item baseline had also failed at 90 seconds.
Its profile takes 81 seconds against the packet and passes at 46.3 seconds
against the original item, so timing varies substantially. No source error is
reported, and no consumer source is adapted.
`CanonicalTateArrowNaturality` initially takes 63 seconds against the packet and
62 seconds against the unchanged original item
(`9f9b9f6bdfcb87f0f743b2c0`). After profiling and removing the options, its clean
packet check passes (`69f49d86b9ce703c5ccbd14e`, exit code 0).
`IsomorphismComparisonScalarExtension` takes 87 seconds against the packet;
the original-item counterfactual reaches the 120-second diagnostic stop
(`c5c051251a5602593e5f2c4c`). These are unchanged validation sources.
`CommonStageRestrictionTensorDescent` reaches the diagnostic stop against both
the packet and the original item (`5413a8da8a722859a1ad3e17`).
The first three persistent timeout sources also have existing rows in
`coord/rework.tsv`, recording the earlier `SfP1ChartExchange` build quarantine.
`FiniteProductFieldCoefficientDescent` reaches the diagnostic stop against the
packet and takes 116 seconds against the original item
(`41eec234618c4b3c3955a537`). All baseline consumer source hashes match the
packet validation snapshots.
`FrobeniusPullbackOrdinaryExchange` takes 72 seconds in the final-context sweep
(`7da2c238e482a44c10305280`) and
97 seconds against the original item (`46b18c593a9f31579d081ebb`).
`PodReindexingHomCoefficientDescent` reaches the diagnostic stop in both
contexts (`764d93ca5b02bf738dbfb62a` for the original item).
`FiniteClopenDerivedDecomposition` takes 97 seconds in the newer sweep;
the unchanged-original baseline also fails at 86.5 seconds
(`37da5f1c3941c2c34af84139`). Its earlier packet check had passed, further
illustrating the timing variation.
`GeometricFrobeniusInternalHomComparison` takes 95 seconds against the restored
final six-module objects (`2e4b99916877da7b59fdb627`); the original-item baseline
also fails at 101.9 seconds (`fd5d9ce9fd6cd4149f42d97f`). An earlier missing-object
attempt is superseded by this actual compilation.
`IntegralCompactSupportCoefficientComparison` takes 65.5 seconds against the
restored objects (`b9585cc251dded0a9084629c`); its unchanged-original baseline
also fails at 68.3 seconds (`748cde9996a42cc953d6dba4`). Its earlier missing-object
attempt is superseded by this compilation.
`CoefficientDualModelTransport` initially takes 62 seconds, versus 54.7 seconds
against the original item (`69c8260f0b59c0a0be29ca50`). Its profile passes at
53.8 seconds, and the clean unchanged-source check passes at 54.3 seconds
(`88798b3e02fcec0c470e8827`). All profiling options are removed and the source
hash is restored exactly.
`TraceBoundedQuotientStalkRealization` initially takes 62 seconds, versus
57.2 seconds against the original item (`bf2e46bcbcb1feab0a37ea92`). Its profile
passes at 44.9 seconds, and the clean unchanged-source check passes at 46.7 seconds
(`18372597029f3dea049e856a`). All profiling options are removed and its source
hash is restored exactly.
`SfScalarExtensionComposition` takes 90 seconds in the sweep and 83.1 seconds
in the fresh final-context check (`e586f10fa552572b0bc7d43f`); its
unchanged-original baseline also fails at 89 seconds
(`b2f0396927ffb3746f7fb381`). No source error is reported.
`PointRationalFamilyCommonStageNaturality` also passes against the final package
in 12.1 seconds (`fdc64c5f579707a57c9dcc97`). The earlier exploratory ambient import
had brought twelve unnecessary existing project modules into the closure; it is
now absent. The completed compatibility results above include all 51 direct importers.

`OpenRoosUnitAdjunction` initially takes 71 seconds in the sweep. Its original
baseline passes in 56.7 seconds (`5cf001cb7c821ec05b84dc99`), the profile passes
in 40.2 seconds, and the final clean check passes in 38.9 seconds
(`5608363fdba6675b0d324db3`). No profiling option or consumer edit is retained.

The latest source-definition blueprint is under
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`.
New nodes trace through the assigned node to
`def-weil-derived-pullback-tensor-hom`, whose final paragraph locates
reduction/scalar compatibility at `sk-prop-scalar-six`. The current blueprint
uses condensed coefficients; this packet preserves the assigned legacy Lean
finite-reduction definitions and statements. The lower chain lemma is an
agent-formulated specialization of the recorded cofinal-filtration argument,
not a verbatim theorem claimed from Stacks Tag 099N.

## New nodes

`lem-pur-integral-scalar-pullback-roos-quasi-iso` records the one remaining
chain quasi-isomorphism. Factor the source uniformizer as a unit times a positive
power e of the target uniformizer, identify scalar reductions with target
subsequence e(n+1)-1, commute finite free scalar extension with products, and
apply strict Roos cofinality. Exact conservative forgetting to abelian sheaves
allows the existing cofinality tool to detect the completed-module result.
Index one, zero complexes, and empty sites satisfy the formulas; no completeness
hypothesis on the input is added. The parent separately proves normalized
unique descent.

`lem-pur-functor-square-representative-descent` records the fully proved
normalized comparison-square descent through fully faithful precomposition.
It adds no hole.

`lem-pur-integral-scalar-finite-comparison-models` records the compile-time
relocation of the existing finite models, their two existing holes, the proved
strict tower assembly, and good-representative preservation. It adds no
mathematical statement or hole. The existing `def-sf-additive-roos-map` node owns
the unchanged boundary, coordinate characterization, and chosen map in
`ScalarRoosComparison`.

`lem-pur-integral-scalar-pullback-chain-quasi-iso` records the fully proved
specialization to the prescribed chain comparison. The finite-level chosen maps
discharge its generator hypothesis, and the chosen Roos map discharges both
coordinate hypotheses. It adds no hole.

Change record: `coord/changes/H1-integral-scalar-models-extraction.md`.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
