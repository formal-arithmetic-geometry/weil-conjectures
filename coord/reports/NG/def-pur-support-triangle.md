# Stage-1 report: def-pur-support-triangle

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-support-triangle.json`: definition, split using existing notions; no whole-definition Mathlib match.
- `citations.json`: empty list, because this is a definition with no proof steps.
- `report.md`: this report. The required search wrapper also recorded its actual results in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact id, support-localization terminology, supported-section complexes and cone names, and read `SixFunctors/OpenClosed/Supports.lean` in full. `AlgebraicGeometry.Etale.supportsShortComplexOfIsGE` (line 224) and `AlgebraicGeometry.Etale.supportsCone` (line 235) explicitly use the small etale site. They do not give the present pro-etale definition, even though their bodies are explicit. `Sheaf/AlgebraicGeometry/SupportTriangleConstruction.lean` already implements the pro-etale constructions with the required quasi-compactness assumption; it is not an attachment under the brief's WeilConjectures-only rule. Its Lean record is preserved.

## WANTED

None. The current blueprint item and its supported-sections definition are present under `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/`. The historical split_report's statement that the source was unavailable has been replaced with the result of actually reading these files.

## Statement corrected

STATEMENT-DISPUTED: the imported definition writes `A=s_*s^!I` and calls its map to `I` the inclusion without requiring quasi-compactness of the complementary open immersion. In the current pro-etale category, `s^!M=s^{-1}ker(M→j_*j^*M)`, and the supported-kernel comparison need not be invertible for arbitrary complementary opens. The current statement of `def-pur-flasque-support` explicitly supplies the comparison only for quasi-compact j and explicitly records its failure otherwise. The blueprint still makes the unrestricted identification in `def-pur-flasque-support.md`.

Here is the concrete counterexample already analyzed in that node and `lem-pur-infinite-clopen-pair`: take R=product over n∈N of F_2, X=Spec R, coordinate idempotents e_n, J=(e_n:n∈N), Z=Spec(R/J), and U=union D(e_n). The complementary open is not quasi-compact. For nonzero finite coefficients Lambda=F_2 let H_n be the pushforward from the coordinate clopen of its constant rank-one module sheaf, and M=coker(direct-sum H_n → product H_n). The tuple of ones gives M≠0: any locally finite-support representation on the affine base has a finite refinement, so misses a coordinate. However j^*M=0 and s^{-1}M=0. Thus G_ZM=M≠0 while s_*s^!M=0. This is the existing supported-sections counterexample, not a new claim packaged as a node.

Restricting attention to injective resolutions does not justify silently assuming this comparison: if the comparison of the two left exact functors were invertible on every injective, apply it to an exact sequence 0→M→I^0→I^1 with injective I^0,I^1. Taking the two kernels would force it to be invertible on M as well, contradicting the example. At least one of those injective terms is therefore a counterexample. A single injective in degree zero is itself K-injective and can be its own specified resolution.

The corrected definition makes j quasi-compact, exactly the scope of the already corrected `lem-pur-support-localization-triangle`, and specifies u by the inverse canonical comparison followed by the actual kernel inclusion. Its finite coefficient ring, small pro-etale site, all-module-sheaf category, chosen resolution, three complexes and cone signs are retained. This is the closed-open scope needed for the unit's zero section in the affine line, whose open complement is principal; no unit proof route changes. The definition does not assert the localization theorem, constructibility, or a comparison with exceptional inverse images on other coefficient categories.

All direct citers were read:

- `lem-pur-support-localization-triangle` already assumes j quasi-compact, so its use is unchanged.
- `lem-pur-proetale-support-global-boundary` already assumes j quasi-compact, so its use is unchanged.
- `def-pur-triangle-meaning` describes canonicality, functoriality and etale base change for the construction; these now explicitly have this construction's scope. Quasi-compactness of j is preserved by that base change. No claimed construction on an unrestricted pair is used there.

## Split and searches

This is a definition-only split in the sense of stages/1-dag.md §3(2). Its proof and proof_deps are empty and proof_origin is null. The stale proof_origin about a stage-3 refactor does not describe a natural-language proof of this definition and was cleared. No theorem was replaced by a restatement in a helper.

I opened each existing ingredient's statement:

- `def-pur-flasque-support` fixes precisely the finite constant-coefficient pro-etale category, the underived inverse/direct images, the supported kernel and its inclusion, and the quasi-compact-only canonical comparison. The inclusion used here is its inverse followed by that kernel inclusion. It is natural, so applying it termwise gives a cochain map; the composite with the unit is zero by the kernel equation.
- `def-pur-kinjective-complex` defines K-injectivity and a quasi-isomorphic resolution for modules on an arbitrary ringed site, so it applies here. The etale-only `def-weil-pbc-kinjective-resolutions` is not used.
- `prop-pur-kinjective-resolutions-exist` states existence of functorial K-injective resolutions with injective terms for module sheaves on a small site. The small pro-etale site and a sufficiently large module universe are the setting here. Only choosing such a supplied resolution is needed; no new strictly bounded-below or constructibility condition on I is asserted.
- `def-weil-abstract-derived-category` explicitly gives cochain complexes, shifts and the cone terms and signed matrix. Its convention is exactly B^m⊕A^{m+1} with d(b,a)=(d_Bb+u(a),-d_Aa).
- `def-weil-finite-type-morphism` includes the meaning of quasi-compact morphism, used for the one necessary scope clarification.

The current searches were made only through msearch.py. `searches.jsonl` contains their exact queries and results; the new mathlib_searches entries were generated from that log. Earlier search records in the repository copy were retained as historical records. LeanFinder was tried with two different phrasings: support localization after a K-injective resolution, and forming the kernel of the open unit on a ringed site. Both return resolution/factorization ingredients, not this support-specific package. Loogle `CochainComplex.mappingCone, CochainComplex` returns the generic cone API. The two source-grep patterns find no supported construction, and find the generic cone at MappingCone.lean:57. LeanSearch is available in this run: its actual eight results include `DerivedCategory.triangleOfSES` and ordinary injective resolutions, not a full match. I read the returned signatures and the relevant CM5b, KInjective, MappingCone and DerivedCategory/ShortExact source. No failed service was recorded as absence.

I also ran `tools/blueprint_refs.py search 'support-localization'` and searched the whole DAG by support/cone terminology. The three blueprint matches are this concrete construction, the meaning-of-properties definition, and the localization theorem. The latter two use this construction; neither duplicates it. `blueprint.same_as=[]`, `blueprint.is` remains the imported id, and `blueprint.from=null` remains appropriate to an imported node. No new node, tag-sharing pair or unattached helper is introduced.

## Unfinished work

None for this stage-1 definition split. Dependencies retain their own existing stage status; this delivery neither proves their Lean nor claims the localization theorem.

## Review by NG

I read the current item and supported-sections blueprint files, the entire DAG statements of all five statement dependencies, the chapter record, the unit statement and its five steps, the existing localization theorem and global-boundary statements, and the project and Mathlib sources described above. This is a definition, so there are no numbered proof steps whose non-elementary uses could be hidden: C1/C4 are checked on the construction's ingredient statements instead. In particular, I did not take the invertibility of the supported comparison from its definition without checking its hypothesis; that check found and repaired the missing quasi-compactness. The general K-injective notion supplies the correct site, and the existence statement really includes injective terms. The cone convention is stated in the cited abstract-derived-category node itself, not merely in its proof.

The termwise construction is elementary from the cited definitions. Naturality of the unit makes its kernel stable under differentials. For a sum f+g, the induced kernel map, after composition with the monic kernel inclusion, equals the sum of the two induced composites; cancelling the inclusion proves additivity (and likewise for zero). Module inverse image and direct image are additive, hence the displayed termwise complexes and u are well-defined. Direct computation gives d²(b,a)=(d_Bu(a)-u(d_Aa),0)=(0,0), since u is a cochain map; this checks both cone signs without a new lemma. These routine checks belong to the definition and report, not new unsplit nodes.

I tested U=X,Z=empty (A=0 and the cone is B), U=empty,Z=X (A=B, u=id and the usual contractible identity cone), and the zero complex (all complexes zero). The zero coefficient ring also causes no exception. The non-quasi-compact example above checks why the added scope is necessary; no ordinary restriction is identified with derived shriek. Mathlib orders the two cone summands as A[m+1]⊕B[m]; swapping them gives exactly the blueprint's displayed formula, as verified from d_fst_v at line 275 and d_snd_v at line 288. I checked delivery-errors B through E: no new incomplete statement, no new or fabricated search, no duplicate, no hidden non-elementary proof step, no circular localization dependency, and no SGA source. All written files stay in this item's sandbox; no Lean or compiler/build tool was run.
