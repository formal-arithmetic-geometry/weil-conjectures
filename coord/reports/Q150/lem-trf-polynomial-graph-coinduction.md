# Q150: lem-trf-polynomial-graph-coinduction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-polynomial-graph-coinduction.json: statement, split; six complete proof steps; no Mathlib match.
- citations.json: thirteen step/node entries, each quoting the complete verbatim current statement.
- report.md: this report. searches.jsonl is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. No unit/chapter file, Lean file, repository file or launcher script was written.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, graph/coinduction terminology, and Koszul/coinduction separately. The hits were ordinary module coinduction or representation-theoretic coinduction; none proves the graph Koszul resolution and D(A)-valued natural shift comparison. Project sorries were not counted as finished proofs.

## WANTED

None. The argument's literature is present in the read clone.

## Problems and changes

The live item was statement-only, with no proof, and the sandbox had no node or report. I copied the live node and retained its exact statement, statement dependencies, source, creation record, blueprint ancestry and old searches. No statement dispute was found. Added six proof steps, their exact dependency union, agent proof origin, search results and split_report. No clause was moved into a new node: existing generic algebraic tools give the needed inputs.

The inherited blueprint ancestry points to the old semistable/nearby-cycle relative-duality auxiliary of lem-trf-local-term-locality. I read the latest blueprint statement and proof, which now emphasize contracting correspondences. This delivery only proves the already-imported polynomial graph auxiliary; it neither claims that the latest locality proof explicitly states this auxiliary nor changes the chapter or unit route. The ancestry is retained as provenance, and split_report names the precise algebraic input supplied.

## Not duplicates

No new nodes, so no new/existing pairs require a same-tag distinction. Whole-DAG searches for Koszul, coinduction, 0BZE and 0BQZ found the generic inputs that this delivery reuses. Blueprint searches for Koszul, coinduction, polynomial variables and polynomial graph found no blueprint theorem stating the item. In particular lem-trf-perfect-algebra-coinduction-tensor is reused, not recreated; lem-trf-flat-epimorphism-polynomial-dual contains a related first isomorphism under additional polynomial-presentation/perfectness hypotheses, but its statement does not give this item's general evaluation resolution and natural unbounded-T comparison. I do not cite that sibling's proof as a theorem.

## Mathlib searches

Read the six inherited 2026-10-22 search results before running five new searches through the prescribed msearch.py command. The new exact tool/query pairs and results are retained in searches.jsonl and appended verbatim as JSON result records in mathlib_searches. LeanSearch returned polynomial evaluations and coefficient-ideal quotients, not the derived graph theorem. Loogle with MvPolynomial.eval₂Hom, DerivedCategory returned no hits. LeanFinder's first phrasing returned shifts and group-cohomology infrastructure; the second returned ordinary weak regular sequence induction and quotient criteria. Grep returned representation coinduction, unrelated coinductive tactics, and mentions of Koszul homology. I read Mathlib/RingTheory/Regular/RegularSequence.lean (its Koszul regularity is explicitly TODO), Algebra/Homology/LocalCohomology.lean (Koszul computation is future work), and the project's ordinary change-of-rings coinduction declarations. None specializes in one line to the item. All five new services succeeded; the historical unavailable LeanSearch record remains historical and unchanged.

## Review by Q150

I read delivery-errors B through E in full, both copies, against the node and the sources. The unchanged statement introduces all objects and has its defining notions in stmt_deps. No new statements or objects with postponed data were introduced. TeX uses single mathematical escapes; tags and labels were verified against literature/stacks-project/tags/tags. I caught and corrected draft references 06YI/06YU, which are not the resolution and scalar-extension lemmas: Step 6 now cites 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), and 06Y6 (lemma-derived-base-change). Every non-elementary fact has a node citation. Every cited statement was opened in full; citations.json preserves those exact statements, including their hypotheses.

The main source is dualizing.tex Tag 0BZE (lemma-RHom-is-tensor-special), read with its proof, and duality.tex Tag 0BQZ (lemma-regular-immersion-ext), read through the local signed Koszul computation. The source's sheaf statement is not silently treated as an algebra-valued isomorphism: the complementary-equivalence node supplies the actual module calculation, and coinduction action plus single-degree reconstruction separately give the D(A) statement. The polynomial specialization and cancellation are explicit agent arguments, so proof_origin.by is agent. Other sources read were more-algebra.tex 062F and 0A66, dualizing.tex 0A70/0A71, derived.tex 08J5, sites-cohomology.tex 06YS/0G7E and more-algebra.tex 06Y6. There is no SGA citation or purity detour.

Step 1 uses only def-weil-pbc-mv-polynomial-ring, whose actual statement supplies the polynomial universal property. The quotient inverse is given on generators, and injectivity is proved by coefficients, not quoted as a hidden regular-sequence lemma. For each j the remaining-variable ring may have zero divisors: the leading coefficient of (x-a)p is still exactly the leading coefficient of p. This elementary argument also works in the zero ring. Evaluation followed by the coefficient inclusion gives ei=1 explicitly.

Step 2 uses lem-weil-pbc-regular-sequence-koszul-regular in its stated successive-injectivity form, which does not require the generated ideal to be proper. Its hypotheses were verified in Step 1 with M=S. It supplies precisely the positive-degree homology vanishing. def-weil-pbc-koszul-complex supplies the finite-subset basis, boundedness, and differential d1 with image the graph ideal; the quotient computation gives H0=A. Thus the proof establishes the resolution rather than citing a newly invented restatement of it.

Step 3 uses def-sc-koszul-dual-complex for the signed Hom differential and lem-sc-koszul-complementary-equivalences for its actual differential-compatible complementary degree equivalences. This node assumes no regularity, so it applies over our arbitrary S. Combined with Step 2, its equivalences imply lower dual cohomology vanishing. The ordered top functional and its boundary ideal are written out from def-weil-pbc-koszul-complex, fixing orientation without assuming an unspecified determinant comparison. The complementary equivalences are used only for cohomology vanishing, not to assert an unrecorded chain isomorphism with a chosen shift sign.

Step 4 uses lem-trf-derived-coinduction-adjunction for the underlying S-derived Hom and its K-injective precomposition model, lem-pod-projective-hom-evaluation-model for the bounded projective resolution comparison and naturality under postcomposition, and lem-sf-derived-concentrated-single for reconstruction in D(A). All terms of the resolution are finite free, hence projective; the model theorem does not require boundedness of the target. Scalar postcomposition makes the computed cohomology comparison S-linear. The displayed identity (b h)(c)=h(cb)=h(i(b)c)=i(b)h(c) proves that the precomposition action is the original A-action after ei=1; an isomorphism after restriction is never assumed to lift. Reconstruction is applied in the abelian category of A-modules only after this action check. The oriented Hn identification determines the requested normalization.

Step 5 applies the statement of lem-trf-perfect-algebra-coinduction-tensor with R=S, B=A, and K=N=S tensor_A^L T. The perfectness hypothesis is provided by the bounded finite-free resolution of Step 2. The cited theorem explicitly gives an isomorphism in D(A), natural for every unbounded input, retaining the B-action. It is not an ordinary Hom-tensor comparison missing its coinduction enrichment. This is the only substantial tensor/coinduction comparison needed.

Step 6 uses lem-pc-kflat-resolution on the one-object identity-cover site, lem-pur-kflat-change-of-rings for S tensor_A P with its flat terms, and lem-pc-derived-tensor-second-factor-functor for computing and descending both tensors and the naturality comparisons. Their statements give the required unbounded representatives and change-of-rings stability. Tensor balancing explicitly uses e(i(a))=a. I checked both inverse composites on pure tensors and the differential sign: moving A[-n] from the second tensor factor into a cohomological shift introduces (-1)^(np) on a degree-p element, and the target differential is (-1)^n d_P. The sign change at p+1 is exactly (-1)^n. All formulas are A-linear, commute with coefficient chain maps, and descend by the canonical K-flat comparisons stated in the tensor theorem. No unproved associativity or shift compatibility is hidden behind the word cancellation.

Small cases checked: n=0 gives the single-term Koszul complex, identity coinduction and the usual identity tensor maps; n=1 gives Hom([S --(x-a)--> S],S) with H1=A and negative shift A[-1]; A=0 gives only zero complexes, with injectivity on the zero module valid; A=Z/4 and a=2 confirms that no nonzerodivisor assumption on a is needed; arbitrary unbounded T uses a K-flat representative and finite Koszul length, with no convergence argument or Tor bound. I checked the dependency closure of every theorem used and found no path back to the item. proof_deps is exactly the union of step uses. The only elementary step is the explicit polynomial calculation. All six proof steps are under 1200 characters, so no step exceeds the 2000-character long-step threshold.

Generic off-unit tools are declared in split_report.tool_uses: regular-to-Koszul exactness, complementary duality, projective Hom model, and the three K-flat/tensor inputs. Each supplies a generic algebraic fact absent from the trace unit; none replaces a unit step. Definition nodes and the existing Mathlib single-degree reconstruction are used according to their actual statements.

## Unfinished work and validation

No mathematical clause remains unfinished. The server review_split check passed with zero new nodes; its only informational note is the pre-existing unrealized sk-i-curve-zero unit. Required full delivery dry run and push are run after this report; their authoritative final outputs are reported to the lead.
