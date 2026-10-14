## What changed

The original item hole is replaced by a categorical pasting proof using target-transition normalization, the higher-image coefficient square, and underived inverse-image coherence. Existing declaration signatures are byte for byte unchanged. The comparison remains the same canonical target-functor comparison, pullback-associativity transition, and mapped coefficient isomorphism. The explicit endpoint APIs construct these existing maps and isomorphisms; their equations are reflexive. The changed proof in targetPullbackComparisonInv changes only the commutativity witness. These definition-body adjustments and the public support API are recorded in coord/changes/baseChangeTargetSheafComparison-proof-api.md.

The second reader proved upperStar_coefficient_square from the existing component associativity lemmas in WeilConjectures.SixFunctors.BaseChange.Pasting, naturality, equality transport, and cancellation. No additional statement or hole was introduced. Its proof-only import replaces the narrower Coherence import. Removed redundant public imports of HigherDirectImageTransitions from HigherDirectImageCoefficientSquare and of SmoothBaseChange.Coefficients from BaseChangeTargetTransitionHigherImage; both remain publicly available through HigherDirectImageTransitionIsIsoOfLower.

## Proved and sorry left

Closed the original item hole: AlgebraicGeometry.Etale.baseChangeTargetSheafComparison_naturality (node lem-sbc-target-sheaf-comparison-naturality).

Proved supporting declarations: AlgebraicGeometry.Etale.targetPullbackComparison_snd, higherDirectImageTransition_isIso_of_lower, higherDirectImageMap_eq, higherDirectImageOverMap_eq, higherDirectImageMapIso_hom_eq, higherDirectImage_coefficient_square, and upperStar_coefficient_square. The second reader closed the sandbox hole AlgebraicGeometry.Etale.upperStar_coefficient_square (node lem-sbc-upper-star-coefficient-square).

Added one remaining named hole: AlgebraicGeometry.Etale.baseChangeTargetTransition_higherImage, in Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage, node lem-sbc-target-transition-higher-image. Its docstring gives the normalization calculation using exact single-complex composition, transition naturality, and homology. The item itself has no sorry, and no definition contains sorry or chooses data from an unproved existence theorem. This is a decomposition of one original hole into one strictly smaller normalization hole, with net holes closed minus holes added equal to zero. It does not yet establish the target without sorryAx.

Axiom checks of all 20 public declarations in the five modules show only propext, Classical.choice, and Quot.sound, with sorryAx allowed only for the remaining normalization statement and results depending on it. The original comparison definitions and the higher-image coefficient-square theorem are sorry-free. Final compilation and delivery preflight check the repaired five-module set.

## No longer needed

Removed direct item imports: Sheaf.AlgebraicGeometry.BaseChangePullbackComparisonComp, Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp, Sheaf.AlgebraicGeometry.HigherDirectImageTransitions, and WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs. The last two remain available through public dependencies and their definitions are still used.

Every old proof dependency absent from the new item proof_deps is listed here: lem-sbc-pullback-comparison-comp and lem-sbc-lower-star-plus-transition-comp. The new proof uses the existing higher-image composition theorem through lem-sbc-higher-image-coefficient-square. The lower-star composition machinery may still be used by that theorem. No module is pruned from the whole TargetsCheck import closure: a source-graph comparison found an empty removed-module set.

The unit sk-lem-failure-field and its realized fields remain unchanged. The new calculation is below the unit level and proves the same canonical restriction comparison used in its limit step.

## Where the brief, the DAG or earlier work was wrong

The first report omitted explicit names of the two removed proof dependencies and did not distinguish decomposition from net progress. The second reader corrected both. The report's superseded second-reading paragraph was not a current independent review.

The first worker's direct derived-category unfolding approach exceeded the single-file limit. The delivered endpoint API and categorical pasting avoid that expansion. A further scratch attempt at the remaining normalization calculation also exposed expensive reduction of single-complex object presentations; no partial scratch proof is delivered.

The earlier dedicated repair return reported an import collision between DerivedTensorPreservesQCoh and SchemeTensorShiftBinaryLocalizationSquare in unchanged dependencies. It is not reproduced against the current compiled library: all five delivered modules and the independent axiom scratch compile. Neither unrelated module is edited in this delivery.

The source context was checked at [Stacks Tag 0F07](https://stacks.math.columbia.edu/tag/0F07), its canonical pullback restriction diagram and limit argument, and [Stacks Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1), the higher-image continuity context. The general module-coefficient coherence calculation is a formal categorical argument; these sources motivate the canonical maps rather than explicitly state every generalized helper.

## New nodes

lem-sbc-target-transition-higher-image: the remaining normalization equality for an arbitrary commutative coefficient square and coefficient morphism. It contains no iterated-pullback comparison or naturality target; its proof is the exact single-complex compatibility calculation. It is true for identity arrows, zero coefficient morphisms, zero sheaves, arbitrary commutative rings, and all integer degrees.

lem-sbc-upper-star-coefficient-square: the underived coefficient equality. Now proved by the second reader from existing upperStarComp component associativity and naturality; it involves no derived direct image or target comparison.

lem-sbc-higher-image-coefficient-square: proved by applying higher_direct_image_transition_composition to the two paths and mapping the supplied coefficient equality. It requires no arrow to be invertible.

lem-sbc-higher-image-transition-isIso-of-lower: proved by preservation of isomorphisms by derived direct image and homology. Its module also constructs explicit endpoint APIs for the same target and coefficient maps, with reflexive equations. No new axioms or arbitrary coefficient choices are used.

Change record: coord/changes/baseChangeTargetSheafComparison-proof-api.md.

## Second reading by J2

1. PASS. Compared the delivered item with the repository version by diff and checked every existing signature byte for byte, including the original theorem and all comparison definitions. Only the two declared definition bodies change, as documented by the change record. The inverse map's data are identical up to proof irrelevance. The sheaf comparison has the same three isomorphism factors: the new target API is the original targetFunctorIso, and the mapped-isomorphism API has the same coefficient morphism under the same functors. No hypotheses or conclusions change. The downstream scan found 122 transitive importers and one external direct user of baseChangeTargetSheafComparison, BaseChangeTargetStalkHigherImageComparison, which continues to use the same comparison and theorem.

2. PASS. Read all five modules, including the structural congruence and pasting elaborators. They construct proof terms from equality, heterogeneous congruence, proof irrelevance, functoriality, and the supplied categorical pasting theorem; the Lean kernel checks the terms. No trust-bypassing declarations, forbidden axiom, unsafe/opaque implementation, or sorry in data occurs. The initial five-module set compiled within 60 seconds per file; the repaired coefficient theorem compiles in about 3 seconds. Independent #print axioms checks cover all public declarations; the final delivery tool repeats the compiler and axiom probe.

3. PASS. Both initially split statements are true and strictly part of the argument. Checked identity-arrow, zero-sheaf, zero-map and negative-degree cases; no invertibility or cartesian assumption is hidden. Searched Mathlib again with different wording using leanfinder, loogle and grep, and searched the project for coefficient-square, single-complex and transition APIs. Found the existing BaseChange.Pasting associativity components and used them to close upperStar_coefficient_square. The remaining normalization statement has its source, full proof docstring and matching node; it is not a renamed target. LeanSearch was unavailable and is recorded as unavailable.

4. PASS AFTER CORRECTION. The top proof computes the geometric pullback square, supplies underived coefficient coherence, applies the existing proved higher-image composition law, then pastes with target-transition normalization. Removed redundant new-module public imports and used a plain import for the extra proof-only associativity API. Completed No longer needed with both removed old dependency ids. Verified that sk-lem-failure-field.realized remains unchanged and that no module actually leaves the whole target import closure.

5. PASS AFTER CORRECTION. Read the five node records alongside their declarations. Every proof_deps is the union of the proof-step uses, existing node statements are unchanged, and new nodes carry the required source, searches, creation, blueprint, unit and Lean fields. Updated the coefficient-coherence node to describe the proof now written, corrected proof_origin to acknowledge the second reader, and refreshed the recorded searches. The Lean signatures agree with their records.

Changed by this second reading: proved upperStar_coefficient_square; removed two redundant public imports; updated node proof/provenance/search records; corrected the downstream count, decomposition accounting, removed-dependency list and global-pruning claim; wrote this independent review. Existing theorem signatures, comparison data, and unit route are preserved.
