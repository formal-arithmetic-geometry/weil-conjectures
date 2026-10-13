## What changed

Proved `AlgebraicGeometry.torAmplitude_of_quasiCoherent_tests` with its original signature,
visibility, universes and hypotheses. Its proof now extends local quasi-coherent test sheaves by
open pushforward, transfers vanishing through exact restriction, invokes affine detection, and
glues zero cohomology over all affine opens. Local derived categories use standard localizations
in independent universes. Both modules reuse the existing private `tensor_vanishes_iff` from
`TorAmplitudeOpenLocal` through a proof-only `import all`, rather than duplicate it.

Added `Sheaf.AlgebraicGeometry.AffineQCohTorAmplitudeDetection` with the fully proved theorem
`AlgebraicGeometry.affineQCoh_torAmplitude_detection`. It computes module Tor amplitude from
associated-sheaf tests and constructs a bounded flat K-flat representative for arbitrary sheaf
tests. It uses existing module representatives and chart comparisons rather than introducing
new model existence holes. New proof imports are non-public; original public imports stay.
Updated the item's DAG proof and dependencies to match this route.

Repair of the returned delivery: deleted the duplicate private `tilde_preservesKernel`
proof and reused the existing theorem through
`import all Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`.
Removed the now-redundant direct QuasicoherentKernel and LeftExact imports from the
affine helper, and updated its node to cite the existing comparison node.
The delivery tool rebuilds the commit on the current server `sheaf-dag` base.
A fresh second reading is needed after this repair.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.torAmplitude_of_quasiCoherent_tests`
(`lem-pc-tor-amplitude-qcoh-test`). Also proved the new affine theorem
`AlgebraicGeometry.affineQCoh_torAmplitude_detection`
(`lem-pc-affine-qcoh-tor-amplitude-detection`). No new private theorem helper remains.
No `sorry` remains in either delivered module; no holes were added or split off.
The second reader checked `#print axioms` for both public theorems: each depends only on
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Both repaired modules are checked with `lcompile.py --all` and the delivery dry run.
The dry run also checks the current server base, compilation, and axiom probes.

## No longer needed

Deleted the duplicate private helper `AlgebraicGeometry.tilde_preservesKernel`.
The second reader also deleted the duplicate private
`AlgebraicGeometry.isZero_derivedTensor_homology_of_vanish`; its single use now unpacks
the K-flat witness directly, without restoring the pruned affine criterion import.
The affine helper no longer directly imports
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` or
`Mathlib.CategoryTheory.Preadditive.LeftExact`; both remain available through the reused
comparison module. Their nodes remain transitive dependencies.

Removed these original proof imports:

- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
  (`lem-pc-affine-derived-pullback-tensor-tilde`): use the universe-independent open tensor
  comparison and the canonical affine chart tensor comparison instead.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (`lem-pc-affine-qcoh-derived-equivalence`): the existing module representative uses the core
  equivalence; its shift normalization is unnecessary here.
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`
  (`lem-pc-affine-tor-amplitude-criterion`): the affine helper supplies the needed direction
  directly from module tests and the existing flat-model criterion.

A source import-closure comparison, including Mathlib transitive imports, removes
60 project modules from this branch; other targets may still need them. This list
was regenerated after the second reader replaced duplicate proofs with shared helpers.
It supersedes the first worker's longer list.

- `Sheaf.Algebra.Homology.BaseDerivedExtensionLinear` — `lem-pc-base-derived-extension-linear`
- `Sheaf.Algebra.Homology.BaseDerivedExtensionResolution` — `lem-pc-base-derived-extension-resolution`
- `Sheaf.Algebra.Homology.BaseDerivedExtensionScalar` — `lem-pc-base-derived-extension-scalar`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyAction` — `lem-pc-base-derived-tensor-cohomology-action`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` — `def-pc-base-derived-tensor-cohomology-model`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCounitLinear` — `lem-pc-base-derived-tensor-counit-linear`
- `Sheaf.Algebra.Homology.BaseTensorOrdinaryDegreeIso` — `lem-pc-base-tensor-ordinary-degree-iso`
- `Sheaf.Algebra.Homology.BaseTensorOrdinaryIso` — `lem-pc-base-tensor-ordinary-iso`
- `Sheaf.Algebra.Homology.CoproductKProjective` — `lem-pc-coproduct-kprojective`
- `Sheaf.Algebra.Homology.FilteredFreeKProjective` — `lem-pc-filtered-free-kprojective-stage`, `lem-pc-filtered-free-kprojective`, `lem-pc-filtered-free-kprojective-telescope`
- `Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly` — `lem-pc-filtered-free-kprojective-assembly`
- `Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep` — `lem-pc-filtered-free-kprojective-step`
- `Sheaf.Algebra.Homology.FilteredFreeResolution` — `lem-pc-derived-filtered-free-resolution`
- `Sheaf.Algebra.Homology.FilteredFreeTelescopeSplitting` — `lem-pc-filtered-free-telescope-splitting`
- `Sheaf.Algebra.Homology.FreeComplexCover` — `lem-pc-derived-free-complex-cover`
- `Sheaf.Algebra.Homology.FreeCoverBicomplex` — `lem-pc-derived-free-cover-bicomplex`
- `Sheaf.Algebra.Homology.FreeCoverColumns` — `lem-pc-derived-free-cover-columns`
- `Sheaf.Algebra.Homology.KFlatTensorProduct` — `lem-pc-kflat-tensor-product`
- `Sheaf.Algebra.Homology.LargeFilteredFreeResolution` — `lem-pc-large-filtered-free-resolution`
- `Sheaf.Algebra.Homology.TensorActionOfAdditiveFunctor` — `lem-pc-tensor-action-additive-functor`
- `Sheaf.Algebra.Homology.TotalFreeFiltration` — `lem-pc-derived-total-free-filtration`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelEven` — `lem-pc-derived-total-filtration-cokernel-even`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOdd` — `lem-pc-derived-total-filtration-cokernel-odd`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOddAux` — `lem-pc-derived-total-filtration-cokernel-odd-core`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective` — `lem-pc-derived-total-filtration-even-quotient-bijective`, `lem-pc-derived-total-filtration-even-quotient-surjective`, `lem-pc-derived-total-filtration-even-quotient-injective`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap` — `lem-pc-derived-total-filtration-even-quotient-map`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationExhaustive` — `lem-pc-derived-total-filtration-exhaustive`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective` — `lem-pc-derived-total-filtration-odd-quotient-bijective`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientMap` — `lem-pc-derived-total-filtration-odd-quotient-map`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationQuotients` — `lem-pc-derived-total-filtration-quotients`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationStepRetraction` — `lem-pc-derived-total-filtration-step-retraction`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationTerms` — `lem-pc-derived-total-filtration-stable`
- `Sheaf.Algebra.Homology.ZeroDifferentialFreeCoproduct` — `lem-pc-zero-differential-free-coproduct`
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` — `lem-pc-affine-derived-pullback-tensor-tilde`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` — `lem-pc-affine-qcoh-derived-equivalence`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift` — `new-affine-qcoh-derived-equivalence-shift`
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion` — `lem-pc-affine-tor-amplitude-criterion`
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` — `lem-pc-derived-pullback-kflat-tensor-model`
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` — `lem-pc-derived-pullback-tensor-comparison-descent`
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct` — `lem-pc-derived-pullback-tensor-product`
- `Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent` — `lem-pc-kflat-bifunctor-iso-descent`
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor` — `lem-weil-pbc-module-pullback-tensor`
- `Sheaf.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport` — `lem-pc-inverse-image-stalk-scalar-transport`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` — `lem-weil-pbc-module-stalk-pullback`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso` — `lem-weil-pbc-module-pullback-tensor-iso-criterion`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` — `def-pc-derived-direct-image`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` — `lem-pc-module-pullback-adjunction`
- `Sheaf.AlgebraicGeometry.TensorPullbackTilde` — `lem-weil-pbc-tilde-pullback-base-change`
- `Sheaf.Paper.DerivedTotalResolutionColumnZero` — `lem-pc-derived-total-resolution-column-zero`
- `Sheaf.Paper.DerivedTotalResolutionHomologyInjective` — `lem-pc-derived-total-resolution-homology-injective`
- `Sheaf.Paper.DerivedTotalResolutionHomologySurjective` — `lem-pc-derived-total-resolution-homology-surjective`
- `Sheaf.Paper.DerivedTotalResolutionQuasiIso` — `lem-pc-derived-total-resolution-quasi-iso`
- `Sheaf.Paper.TotalResolutionCycleFiniteSupport` — `aux-total-resolution-cycle-finite-support`
- `Sheaf.Paper.TotalResolutionCycleReduction` — `lem-pc-derived-total-resolution-column-zero-cycle-reduction`
- `Sheaf.Paper.TotalResolutionCycleSupportStep` — `aux-total-resolution-cycle-support-step`
- `Sheaf.Paper.TotalResolutionCycleSupportZero` — `aux-total-resolution-cycle-support-zero`
- `Sheaf.Topology.InverseImageStalk` — `lem-weil-pbc-topological-inverse-image-stalk`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` — `lem-weil-pbc-pushforward-spec-global-sections`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`

## Where the brief, the DAG or earlier work was wrong

The first delivery repeated an existing private kernel-preservation proof word for word.
The second reader also found four duplicate private vanishing/model helpers and replaced
them with existing proofs from `TorAmplitudeOpenLocal`; both nodes now cite that module.
This restores some imports the first worker had proposed to prune; the final list above
records the actual closure.
The landing check correctly refused it. This repair imports and uses the existing helper
without changing its visibility or adapting its module.

The old affine criterion accepts tests against every sheaf, so its reverse implication cannot
be applied directly to the quasi-coherent test hypothesis. Its computation does use only
associated-sheaf tests; the new proved affine helper makes that direction available for any
affine scheme via its canonical spectrum chart. This is an interface gap, not a false theorem.
The original same-universe open comparisons cannot supply arbitrary local derived categories
at the target's unconstrained localization universe. Existing independent-universe exact
restriction comparisons solve this without changing the target signature.

Stacks Tags [08EA](https://stacks.math.columbia.edu/tag/08EA),
[08E9](https://stacks.math.columbia.edu/tag/08E9), and
[0651](https://stacks.math.columbia.edu/tag/0651) were read on the official site because the
cited local perfect.tex is absent. The proof follows their affine test and bounded flat-model
route. The unit's realized statement/step lists are empty and no unit route was changed.
Edge cases: empty X is covered by the same zero-sheaf cover lemma; empty affine opens and zero
rings admit the same chart equivalences; unbounded E is handled by K-flat resolutions; a=b
uses the same bounded-flat model. No nonempty-space or strict-interval assumption was added.
LeanSearch was unavailable (HTTP 500); LeanFinder, Loogle and grep searches ran and are recorded
in the new node. Blueprint search for Tor amplitude found no matching affine detector.

## New nodes

`lem-pc-affine-qcoh-tor-amplitude-detection`: the affine portion of Tag 08EA, already proved in
its new module, with four steps matching the module representative, module-test computation,
bounded flat model, and zero-term homology argument. It adds no remaining work item with a
hole. Existing definitions, signatures, public imports and public instances are unchanged.
No forced adaptation is needed. The static proof-context flag is documented in
`coord/changes/TorAmplitudeQCohTestProofContext.md`.


## Second reading by J4

1. Statements: PASS. Diffed the original target module against the repository; its
   complete theorem signature is byte for byte identical, including universes and every
   hypothesis. Its public imports, visibility and docstring are unchanged. The affine
   theorem is new, in its own module. The existing change record covers only local
   instances and proof-elaboration context, not mathematical interface changes.
2. Proofs: PASS. Both final modules compiled and the delivery dry run passed preflight.
   Refreshed scratch `#print axioms` checks by importing the final compiled pair: both
   public theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. The delivery tool also probed every delivered declaration. Text searches
   found no holes or forbidden constructs in either file. Models are eliminated inside
   proofs of propositions; no definition chooses arbitrary mathematical data from an
   unproved mere existence statement. The conclusion supplies a real K-flat witness.
3. New statement: PASS. No statements were split off with sorry. The affine detector
   is strictly the affine part of the original argument, with a complete docstring and
   matching node. Checked X empty, zero rings, E zero, a=b, and unbounded E: exact
   faithful charts, K-flat resolutions, and bounded flat models apply without added
   assumptions. Read official Stacks Tags 08EA and 08E9. Fresh LeanFinder query about
   associated-module tests and bounded flat complexes found module flatness criteria
   only; Loogle `IsZero, Functor.Faithful` had no match (unknown identifier); Mathlib grep
   `flat_model|torAmplitudeIn` had no match. Broader repository searches found related
   affine criteria whose hypotheses test every sheaf, plus existing private helpers
   in TorAmplitudeOpenLocal, now reused.
4. Route and pruning: PASS after repair. Read the proof downward: extend local tests
   by open pushforward, transfer them through exact derived restriction, compute the
   affine module tests, construct a bounded flat representative, and glue zero homology
   on the affine cover. The unit record has empty realized statement/step lists and
   remains unchanged. Regenerated the source import closure after helper reuse;
   every removed module and old direct proof dependency is listed above.
5. Nodes: PASS. Both proof descriptions match the Lean, each proof_deps is exactly
   the union of step uses, and all dependency ids exist. The existing node changes
   only permitted proof fields. The new node has self-contained statement, source,
   searches, creation/blueprint records, unit/chapter and the exact Lean signature.
   No statement, definition or unit route was weakened.

Second-reading repairs: removed the affine helper's duplicate
`isZero_derivedTensor_homology_of_vanish`, and the target's duplicate
`exists_kFlat_model`, `tensor_model_iso`, and `tensor_vanishes_iff`. Both modules reuse
TorAmplitudeOpenLocal's existing vanishing equivalence via proof-only import all.
Annotated the affine composite functor and single-complex comparison, and normalized
the representing isomorphism to the existing composite-complex notation, to avoid
repeated expansion of the same chart data during elaboration.
Removed the resulting unused direct KFlatResolution/KFlatDerivedTensorComparison
imports; updated both nodes and regenerated pruning. The earlier kernel-preservation
repair remains. No hole or signature change was added. Temporary import-removal trials
and subsequent dry runs encountered the unchanged 60-second per-file limit under load
around 140 on 64 CPUs; no limit was increased and no module was split to evade it.

Final verification: `deliver3.py --no-push` printed OK for the repaired pair; explicit
axiom checks of the final compiled declarations were clean. The compile wrapper now
limits concurrent jobs to 28; the dry run waited for a slot and passed without any
increase to its per-file timeout.
