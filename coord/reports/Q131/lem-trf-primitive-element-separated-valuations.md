## Files written

- `dag/nodes/sec-trace-formula/lem-trf-primitive-element-separated-valuations.json`: statement, split; no exact Mathlib match for the full simultaneous primitive-element and residue assertion.
- `citations.json`: verbatim statement quotes for every node used in every proof step.
- No new nodes and no new Mathlib leaves. Existing leaves supply all non-elementary inputs.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and primitive-element/valuation terminology found no declaration stating every clause. `Algebra.exists_monic_aeval_eq_zero_aeval_derivative_ne_zero` constructs an integral primitive generator, but imposes none of the simultaneous residues, so it is not an attachment. The primitive-element use in `BoundaryNeighbourhoodExistence.lean` is likewise only an input to a different assertion.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Proposition 2.2.1, printed p. 11, for lem-trf-primitive-element-separated-valuations. The named PDF is absent from this read clone. I read the primary HTML at https://arxiv.org/html/0707.3953v3#S2.SS2. (the two converse-proof paragraphs choosing the primitive element and its perturbation), and marked the expanded proof agent-written as required for a missing local document. Nothing was downloaded or written in the repository.

## Issues found

The imported statement is correct; no statement dispute or alteration. Its proof was empty. Temkin's compressed assertion that one can choose a sufficiently small scalar hides two details that are now explicit: a monic polynomial rescaling places a primitive generator in C, and each proper intermediate field excludes at most one scalar on the chosen affine line.

The existing CRT node's source field labels Chinese remainders as Tag 00U3. That tag is actually `algebra-lemma-etale-over-field`; the correct source is Tag 00DT, `algebra-lemma-chinese-remainder`, read in `literature/stacks-project/algebra.tex` starting at line 2615. Its mathematical statement and Mathlib match are correct; I cite the existing node, use the correct tag in my step source, and report the metadata error without modifying another worker's node.

## Unfinished work

None in the stage-1 split. No Lean was written, compiled or built. Independent maintainer review remains the delivery protocol's next stage.

## Not duplicates

No new node pairs: this split creates no nodes. Whole-DAG searches found and reused `lem-weil-pbc-finite-separable-extension-primitive-element`, `lem-zl-finite-intermediate-fields`, `lem-pc-crt-ideal-quotient-product`, and `lem-weil-pbc-integral-maximal-contracts-maximal`. The other existing primitive-element node, `lem-weil-pbc-finite-separable-primitive-element`, is equivalent; it was not recreated. Whole-blueprint searches for `primitive element`, `Chinese remainder`, `intermediate fields`, and valuation terminology yielded no blueprint statement giving this full item. I read the current `latest` local-term-locality proof and unit, and kept the inherited Temkin input beneath its semistable-alteration route.

## Review by Q131

I checked the item against Temkin's Proposition 2.2.1 converse proof in its primary HTML. It chooses a nonzero primitive residue on one branch, vanishes on the other branches, and preserves these conditions by a small primitive perturbation. The present assumptions explicitly provide residue separability and the finitely many maximal ideals that this paragraph uses. No completeness, discrete valuation, excellence or henselian hypothesis is introduced. The proof does not need the valuation-localization assumption beyond the given setup; retaining an unused hypothesis is faithful to the supplied statement.

For step 1 I opened the complete statements of the existing primitive-element leaf and CRT leaf. The first provides a generator for the finite separable residue extension, not just for E/F. The second gives the actual canonical quotient-to-product isomorphism, which gives the required simultaneous lift after choosing a quotient representative. I checked the distinct-maximal-implies-coprime argument explicitly, rather than taking a property not in that node. I read Stacks 030N (`fields-lemma-primitive-element`) and 00DT (`algebra-lemma-chinese-remainder`), and Mathlib's `Field.exists_primitive_element` at PrimitiveElement.lean:209 and `Ideal.quotientInfRingEquivPiQuotient` at Operations.lean:248. When l=kappa the generator is chosen to be 1: this repairs the possible zero generator without an extra hypothesis.

For step 2 I opened the integral-closure definition and the integral-maximal-contraction node. The latter says exactly that a maximal ideal contracts to a maximal ideal for an integral ring map, which applies because every element of C is integral over A. The elementary unit calculation identifies the unique maximal ideal of A as the strict unit ball, so every branch contains t. I also read the corresponding Mathlib theorem in Ideal/GoingUp.lean:211 and Stacks' integral-under-field discussion, Tag 00GR. This avoids silently assuming that an arbitrary extension of valuation subrings is already a local map.

For step 3 the primitive-element leaf applies to E/F by the original finite/separable hypotheses. I opened the separable-algebraic-extension definition: it explicitly says that every element is algebraic and describes its monic minimal polynomial. The integral-closure definition explicitly identifies roots of monic A-polynomials with elements of C. Multiplying the equation by t^(Nd) gives the displayed coefficients; their real absolute values are bounded by the written logarithmic choice of N. This is a direct substitution and a finite maximum, not an unproved general clearing-denominators theorem. Multiplying a generator by a nonzero base-field scalar preserves its generated field by division by that scalar.

For step 4 I opened the full statement of `lem-zl-finite-intermediate-fields`, read Stacks 030N's equivalence and Mathlib's finiteness theorem at PrimitiveElement.lean:305. The statement supplies precisely finiteness for this E/F; the step then proves the affine-line exclusion itself by subtracting two potential elements of the same proper intermediate field. It does not cite the proof of that node or infer the finite-exception assertion from its title.

For step 5 I checked that all correction terms lie in C and in every maximal ideal, that choosing among the distinct positive powers avoids the finite forbidden set, and that the final generated intermediate field cannot be proper. The residue remains exactly b, not merely some nonzero residue. For r=1 the tuple has a single coordinate and there are no other ideals; for E=F there are no proper intermediate fields and no nonzero-generator requirement on w; for l=kappa the chosen b=1 works also in the smallest residue field F_2. Thus no cardinality assumption on the residue field is hidden. A trivially valued base is excluded by the original hypothesis, as it must be for the powers argument.

I checked delivery-errors B through E: no new nodes or duplicated clauses, all sources and notions named, the statement unchanged, all non-elementary inputs cited by their statements, the elementary polynomial/linear arguments written explicitly, and no dependency can point back through this item (all theorem inputs are existing Mathlib leaves). Every step is under 2000 characters. All item Mathlib queries were run through msearch.py and recorded in searches.jsonl; both semantic phrasings were read and gave component facts only. Earlier item searches were retained, not invented or replaced. Citation quotes were copied verbatim from the opened node statements.
