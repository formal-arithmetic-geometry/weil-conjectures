## What changed

Replaced the single sorry in `AlgebraicGeometry.SingleComplexBaseChange.isIso_stalkComparison_iff_coordinates` by a complete proof from two strictly smaller intermediate theorems. The statement and visibility are unchanged. The only additional import of the item is the proof-only `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality`.

`StalkComparisonSourceTransport` implements exact derived stalks, their cohomology localization identification and its naturality, exact derived restriction to the base stalk, model input identifications, the counit-compatible isomorphism between the two model derived functors, and the resulting canonical B-linear source cohomology isomorphism. The remaining theorem lifts this specified isomorphism uniquely to the tensor algebra; it assumes no K-flatness and contains no final target or morphism phi.

`StalkComparisonPullbackNaturality` constructs the localized comparison into the cohomology of the derived pullback, using the actual tensor-stalk identification and the inverse pullback counit. Its remaining theorem states naturality for K-flat representatives. It contains neither a target representative nor phi, and asserts no invertibility of the comparison itself.

The item's proved private normalization lemma uses naturality of the derived stalk cohomology identification, each coordinate's `represents` equation, and cancellation of its invertible counit. The main proof combines the two intermediate theorems with this normalization and removes the invertible source and target factors in both directions. No definition obtains data from a new unproved existence theorem: the source isomorphism is obtained only inside the final propositional proof, and its specification is unique in any event.

## Proved and sorry left

Closed: `AlgebraicGeometry.SingleComplexBaseChange.isIso_stalkComparison_iff_coordinates` (node `lem-pc-stalk-comparison-coordinate-invariance`). Its module contains no sorry. Also proved the normalization helper and all exact-stalk instances, localization identifications and naturality in `StalkComparisonSourceTransport`.

Added exactly two named theorem holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.SingleComplexBaseChange.exists_comparisonSourceIso`, node `lem-pc-stalk-comparison-source-transport`, module `Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport`.
- `AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality`, node `lem-pc-stalk-comparison-pullback-naturality`, module `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality`.

This is a decomposition: one hole closed and two added, net -1 holes closed. It is not a sorry-free proof of the dependency closure. The new holes isolate tensor-algebra linearity and derived-comparison naturality; the entire normalization involving phi, the represents equations, and the final invertibility argument are proved in Lean.

Local compilation of the three modules passes without warnings. The delivery dry run verifies the module set, declaration probes and preflight; its result is recorded by the delivery tool.

## No longer needed

No original import, node or module is pruned from the dependency closure. The old direct proof dependencies `lem-weil-pbc-module-stalk-exact`, `def-pc-base-derived-tensor-cohomology-model`, `lem-pc-kflat-stalk-criterion`, and `def-pc-derived-pullback` move below the new transport/naturality nodes; `def-pc-single-complex-base-change-stalk-condition` remains a direct dependency. The original exact-stalk, tensor-model, stalk-condition, K-flat-stalk and derived-pullback dependencies are still mathematically needed, now below the two new nodes. No unit statement or unit proof step is bypassed (`sk-thm-picard-semicon.realized` contains no nodes for this item).

Removed the unused draft proof import `Sheaf.Algebra.Homology.KFlatStalkCriterion` from `StalkComparisonPullbackNaturality`: its current proof is deferred, and its signatures already get K-flatness through the shared stalk-condition module. The corresponding node remains an explicit proof dependency of the new naturality node and is not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies provide stalk exactness, K-flatness and the tensor model, but no declaration states tensor-algebra linearity of transport for these models or naturality of this localized comparison for arbitrary derived isomorphisms. `DerivedTensorActionNaturality` uses a different balanced-model interface; `DerivedTensorLocalizationCohomology` compares localized resolution models and does not directly supply either required statement. These are the two gaps split off here. The existing theorem is not marked disputed and its hypotheses are unchanged.

The local repository contains the literature indexes but not the cited TeX or unit markdown. Read the unit record and checked the primary Stacks sources online: equation the project server (Tag 0DJ7), the discussion and lemma at Tag 0DJ8, derived change of rings at Tags 06Y5/06Y6, and K-flat stalks at Tag 06YB. The new proof plans are the original node's transport argument written by this worker from these constructions. In the source-transport docstring, Tag 06Y6 is correctly cited as More on Algebra rather than derived.tex.

Edge cases checked: the source-transport theorem permits arbitrary complexes and requires an actual derived isomorphism; it makes no assertion that the comparison is an isomorphism. The naturality theorem requires K-flatness and invertible pullback counits but imposes no base flatness, Tor-independence or chain-map representative for the derived isomorphism. Zero complexes, negative cohomological degrees and empty schemes cause no extra hypothesis. Equality of the restricted source homomorphism determines its lift uniquely by faithfulness.

## New nodes

`lem-pc-stalk-comparison-source-transport` records the unique tensor-algebra lift of a canonically specified B-linear cohomology isomorphism, with complete transport, scalar-linearity, inverse and uniqueness steps. It records the source transport module's proved infrastructure as auxiliary declarations.

`lem-pc-stalk-comparison-pullback-naturality` records naturality of the comparison into derived pullback before any morphism to the final target. Its proof uses the original K-flat stalk and derived-pullback nodes together with tensor-model equations and source transport.

Updated only `proof`, `proof_deps` and `proof_origin` of `lem-pc-stalk-comparison-coordinate-invariance` to match the implemented normalization and conjugation. No existing signature, definition, statement, source, unit or chapter was changed. No change record or forced adaptation is required.


## Second reading by G3

1. **Existing interfaces: PASS.** Read the full diff against the repository module and checked the declaration table. The existing public theorem's signature, visibility and docstring are byte for byte unchanged; only its proof, a private normalization helper and a proof-only import are added. There is no existing definition change, forced adaptation or change record.

2. **Lean proof and data: PASS as a decomposition.** Compiled all three modules in import order with `lcompile.py`: 15.0 s, 8.2 s and 10.3 s, without errors or warnings. Scanned every delivered source: exactly the two reported public theorem holes, both `:= by sorry`, no forbidden declarations and no hole in a definition. A scratch `#print axioms` check of the main theorem, both new holes and `comparisonSourceUnderlyingIso` reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter also occurs through unfinished upstream dependencies. The new definitions explicitly compose existing functors, localization factors, counit-compatible isomorphisms and inverse counits. They do not choose an arbitrary witness from either new hole. The uniquely specified source isomorphism is obtained only within the final propositional proof.

3. **Split statements: PASS.** Read both signatures, word proofs and nodes against the model fields `universal`, `cohomologyIso_smul`, `comparison_eq`, and `localized_eq`, and against the fixed degreewise `tensorStalkIso` equations. Source transport is linearity and uniqueness of a specified underlying isomorphism; comparison naturality is a square before any target complex or morphism phi. Neither restates coordinate invariance. For source transport, multiplication by a stalk element is a natural endomorphism on A-module complexes and commutes with roofs in D(A); this statement is applied after exact derived stalks. Tensor induction then supplies tensor-algebra linearity, and faithful restriction supplies uniqueness. For naturality, roofs between K-flat representatives are valid because stalk K-flatness and the invertible pullback counits identify ordinary and derived extension; the model comparison equations fix the maps. Checked zero complexes, identity derived isomorphisms, arbitrary integer degrees and empty schemes (there is no point to quantify over). No extra flatness of A over R is needed. Independently read Stacks Tags [0DJ7](https://stacks.math.columbia.edu/tag/0DJ7), [06Y6](https://stacks.math.columbia.edu/tag/06Y6), and [06YB](https://stacks.math.columbia.edu/tag/06YB). Repeated searches with different words: LeanFinder query “An isomorphism in the derived category of A-modules induces an A linear map on Tor over a smaller ring R” returned general Tor results, not this interface; Loogle query `"leftDerivedNatIso", "naturality"` had no hits; grep query `restrictScalars.*faithful|leftDerived.*naturality` returned restriction faithfulness and projective-resolution naturality. Local `rg` and reading `DerivedTensorActionNaturality` and `DerivedTensorLocalizationCohomology` confirm that those use different balanced/localized resolution interfaces, not these statements. No short closure of either new hole was found.

4. **Route and pruning: PASS.** Read the proof from its concluding invertibility argument back through normalization and the two intermediate results. The proved normalization uses the actual `represents` equation, not an assumed commuting square. The source extension and target identifications are isomorphisms, so cancellation works in both directions. Public imports of the new files are used by their definitions or signatures; proof imports are private. All five old proof dependencies remain needed in the new dependency closure. The four that are no longer direct dependencies are now explicitly listed above. The unit `sk-thm-picard-semicon` has empty `realized.statement` and `realized.steps[0]`, so no recorded unit route is bypassed.

5. **DAG agreement: PASS.** Checked the existing node's changed `proof`, `proof_deps`, and `proof_origin` against the Lean steps, and the new nodes' statements verbatim against their theorem signatures. Their dependency lists are the unions of their proof-step uses; their sources, word proofs, searches, creation records, blueprint ancestry, chapter, unit and Lean records are present. Source transport's auxiliary declarations and the construction `comparisonIntoPullback` are recorded. The net remains one original hole closed and two added, not a proof of the import closure.

**Changes by the second reader:** clarified the pruning report by listing all four old dependencies moved below the new nodes; added this independent review and verification evidence. No Lean proof, statement, definition or node required repair.
