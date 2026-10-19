# Worker report: lem-trf-fitting-ideal-direct-sum

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fitting-ideal-direct-sum.json: statement, split into three proof steps; unchanged statement; no Mathlib match for the item.
- New nodes: none. New Mathlib leaves: none. The existing Mathlib leaves def-weil-finitely-generated-module and def-weil-pbc-matrix-determinant are reused.
- citations.json: verbatim statement quotations for every step/node citation.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id, FittingIdeal and fitting found no relevant declaration; the only fitting occurrence was an unrelated English use in Blowup/QuasiAffineGeneralReduction.lean. The read-only master source likewise supplies no relevant Fitting-ideal declaration. The existing side-project presentationFittingIdeal theorem is only a statement with postponed proof and does not prove this item.

## WANTED

None. The source is available in literature/stacks-project/more-algebra.tex.

## Corrections and route

The imported statement is correct; it is exactly the zeroth-ideal equality in Stacks Tag 07ZA, lemma-fitting-ideal-basics, part (2). The source's proof appeals to the block-minor formula in Tag 07Z7, lemma-ideals-generated-by-minors, part (4), whose proof is omitted. I supplied the relevant maximal-minor argument explicitly, using the kernel-row description of Tag 07Z8, lemma-fitting-ideal. In particular, the argument does not replace finite generation of M and N by finite presentation, or choose finitely many generators for their kernels.

The item belongs to sk-i-curve-zero and is a supporting algebra fact under the existing etale-fitting-trick ancestry. I read the chapter and unit records, and retained this route and the existing blueprint.from place and via chain. The exact formula is used at the final Fitting-ideal product paragraph of the etale-fitting-trick's Stacks 0812 source. It is not a new proof of the unit's statement, so no unit realization fields change. There is no SGA source in this split.

## Mathlib and duplicate searches

The command-generated searches.jsonl records all five new searches: LeanFinder for the module formula; LeanFinder for the maximal minors of a block diagonal presentation; Loogle for "fitting"; grep for fittingIdeal|FittingIdeal|fitting_ideal|determinantal|minorIdeal; LeanSearch for the direct-sum formula. All services returned results successfully. The module query returned Jacobson radicals, torsion decompositions and Lie-module Fitting decompositions, which are different assertions. Loogle likewise returned only Lie-module Fitting components; grep returned no hits. LeanSearch returned Module.Presentation.directSum_R, DirectSum.ker_map, finite generation and flatness declarations, none asserting equality of ideals. I read Presentation/DirectSum.lean: it constructs direct-sum presentations but has no Fitting-ideal statement. The second LeanFinder phrasing returned Matrix.det_blockDiagonal; I read Determinant/Basic.lean at that declaration (line 612), and the two-block theorem det_fromBlocks_zero₂₁ (line 675). These compute one determinant, not ideals of all kernel-row determinants, and therefore do not match the item. The two elementary determinant calculations in the split are written from the Leibniz formula already supplied by the existing determinant node.

Whole-DAG searches for 07ZA, kernel-minor, block-diagonal, Cauchy-Binet, Laplace and determinant expansion found the existing independence/base-change node and minor-inclusion node. I read their full statements. The latter has only the three inclusion clauses of 07Z7, not the block-diagonal equality; the former supplies exactly the independent kernel-row definition needed here. The Cauchy-Binet, characteristic-polynomial direct-sum and top exterior-power nodes were also read; none states this item. Whole-blueprint searches using tools/blueprint_refs.py for Fitting, zeroth and block diagonal found no matching blueprint statement (the lone zeroth hit concerns a different six-functors statement). The ancestor command confirms lem-trf-local-term-locality. There are no new nodes to test for duplicate pairs.

## Not duplicates

No new nodes; no new/existing pairs.

## Unfinished work

None for this one-level split. Proofs of the pre-existing dependencies remain their own DAG work.

## Review by N2

I read More on Algebra Tag 07ZA (lemma-fitting-ideal-basics), its statement and proof of (2), Tag 07Z8 (lemma-fitting-ideal) and its kernel-row description, and the omitted block-minor assertion in Tag 07Z7 (lemma-ideals-generated-by-minors), part (4). The item has exactly the source's commutative ring and two finite modules. It asserts only the zeroth equality, so it does not need the higher-Fitting convolution formula or a finiteness assertion for the ideal. No new statement-only lemma or definition was introduced.

Step 1 uses the actual definition in def-weil-finitely-generated-module to form the two surjections. The combined generating family explicitly proves that the direct sum is finite, and the kernel equality is checked coordinate by coordinate. I opened lem-trf-fitting-ideal-independence-base-change and verified that its statement defines I_k using all kernel rows and states independence for any two finite free surjections; taking k=0 supplies exactly A, B and C used here. No base-change or localization clause is used. This is the only non-elementary theorem invoked.

Step 2 cites def-weil-pbc-matrix-determinant, whose statement gives the permutation sum with the same column indexing and the multiplicativity of permutation sign. The proof does not quote Laplace expansion as a black box: it writes the unique decomposition of every permutation according to its first n image rows, with the two internal permutations, then distributes the finite sums. Thus the products in the resulting sum really are n-row kernel determinants for K and m-row kernel determinants for L. The row indices in each subset are placed in increasing order. This gives the first inclusion by the defining closure properties of the product ideal. It uses no statement of the minor-inclusion node and no lemma hidden in that node's proof.

Step 3 again uses the determinant node's formula: off-block permutations have a zero entry, and block-preserving ones correspond to pairs, giving ab. The rows of this determinant really lie in K direct sum L. I wrote the distribution argument for products of arbitrary elements of A and B, so the reverse inclusion is for the entire product ideal, not just its generating products. Equality then follows from the two inclusions and Step 1. The determinant computations are elementary regroupings of finite sums in this fixed presentation, rather than new general lemmas. Each step is below 2000 characters.

I checked zero generating ranks n=0, m=0 and both zero: the empty determinant equals 1 in the determinant node and both combinatorial decompositions remain valid. Thus the zero module contributes the unit ideal, as required. Over the zero ring all equations still hold. For cyclic modules R/I and R/J with arbitrary, possibly infinitely generated ideals I and J, the n=m=1 expansion gives x_1y_2-x_2y_1 in IJ and the reverse products xy, agreeing with I_0((R/I) direct sum (R/J))=IJ. For a nonzero free summand the kernel may be zero: the corresponding determinants vanish and the same expansion gives zero on the other side. No noetherian, nonzero-ring, injectivity, flatness or finite-kernel-generation hypothesis was used.

I checked B--E against the written files: unchanged self-contained item statement; source tags and labels verified in tags/tags; all cited nodes opened and their exact clauses checked; all citation quotations copied verbatim; proof_deps is exactly the union of uses; no new nodes, circular replacement or missing non-elementary fact. I corrected the first citation quotation to include the actual independence clause, in addition to its kernel-row definition. The report and split retain the recorded searches and imported metadata.
