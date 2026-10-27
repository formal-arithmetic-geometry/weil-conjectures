# Q40 stage-1 delivery: lem-sfb-stack-unramified-locus-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-unramified-locus-base-change.json`: statement, split; six proof steps; no Mathlib match for the stack statement. Reuses existing DAG results, with no new nodes and no new Mathlib leaves.
- `citations.json`: all 26 step/node citations, with verbatim excerpts of their statements.
- `searches.jsonl`: five searches actually run with the required msearch command; retained alongside this report in the sandbox.
- `report.md`: this report and the signed review below.

## Attachments

None. Searched the live project `lean/WeilConjectures/` for the blueprint id, unramified-locus names and words, and algebraic stacks. The project hits are ring/scheme results (notably FormallyUnramifiedStalkNeighbourhood and Curve/FiniteMapToLine), not declarations giving this stack statement. No source declaration is offered as finished evidence.

## WANTED

None. All sources used are available as local Stacks TeX. No SGA source is used.

## Corrections and observations

The mathematical statement is unchanged. I corrected its doubled backslashes to single TeX backslashes (delivery-errors B4). There is no statement dispute. The imported item contained no proof. Its source is the appropriate specialization of Stacks 06M3 by 06M5(3); 05W2 supplies the algebraic-space locus, and 03ZK supplies the source-chart test. The proof now fills out the omitted comparison in the last paragraph of 06M3.

The ancestor command reports that the existing item's blueprint ancestor is null. I preserved this maintainer-owned imported chain and its detailed `from.place`, searched the whole imported blueprint (`blueprint_refs.py search 'unramified locus'` and `search unramified`) and the current latest blueprint by tags and words, and found no equivalent blueprint statement. The existing `same_as: []` is retained. I read the current latest sk-thm-sf-ctf-stability and the chapter/unit records: this is a local geometric input on the already recorded chain through the Deligne--Mumford/etale-atlas argument, not a replacement for the unit route.

## Not duplicates

No nodes are created. In particular, the algebraic-space part is cited as `lem-sfb-space-unramified-locus-base-change`; no second 05W2 node was made. Invariant-open descent, representable unramified descent, representable pullback over a space, and the compatible-etale-chart criterion are all reused. The scheme-only `lem-trf-unramified-locus-base-change` was read and is not substituted for the stronger space statement.

The only off-unit result is `lem-a1-space-etale-open-image`. It is declared as a generic tool in `split_report.tool_uses`: step 6 needs the actual open image and the surjective etale factorization of an etale chart. Same-unit locality definitions do not supply this factorization.

## Mathlib searches

I read the item's existing search results and retained them. The fresh Q40 queries and their returned hit names/counts are appended to the item, with the exact query texts in searches.jsonl. All five services/queries succeeded: LeanFinder twice with different phrasings, Loogle for AlgebraicGeometry.FormallyUnramified, LeanSearch for the stack locus, and source grep for unramifiedLocus|unramified_locus|AlgebraicStack in AlgebraicGeometry. The grep returned no hits. Semantic results include Algebra.isOpen_unramifiedLocus, Algebra.unramifiedLocus, and AlgebraicGeometry.FormallyUnramified base-change/diagonal results. I read Mathlib/RingTheory/Unramified/Locus.lean and Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean: these concern rings and schemes, so none is an exact match or one-line specialization for the algebraic-stack statement. These are no-match verdicts, not unavailable-service verdicts.

## Review by Q40

I read all of delivery-errors B--E, and checked the resulting files against the specific failure modes there. The source for the item is the local `stacks-properties.tex`, 06M3 (lemma-local-source), the full proof and 06M5(3). I also read `spaces-morphisms.tex`, 05W2 (lemma-where-unramified), its full proof and 03ZK (lemma-unramified-local); and `stacks-properties.tex`, 0507 (lemma-substacks-presentation) and 04XD (lemma-check-property-covering). Online primary Stacks pages https://stacks.math.columbia.edu/tag/06M3 and https://stacks.math.columbia.edu/tag/05W2 confirm these statements. There are no new nodes requiring independent sources or searches.

Step 1 uses the explicit 2-fibre-product definition for associativity, representable-pullback-over-space for the spaces, stack-chartwise-smooth-etale-calculus for smooth/surjective base changes and local finite type, and the space-unramified-locus lemma for both maximality and equality after arbitrary base change. I verified that the target of each application of the space lemma really is an algebraic space (A or B), and that each source morphism is locally of finite type. The two loci on D are attached to the same map D to B; they are not unrelated loci identified by notation.

Step 2 uses the actual invariant-open-substack-descent statement, which requires a smooth surjective SCHEME atlas. The preliminary U is only an algebraic space, so I explicitly refined it to a scheme P before invoking that lemma. Invariance pulls back along P times_X P to U times_X U. The descent output is an open substack of X; its map to X is representable by schemes by the definition of open substack, and representable-pullback-over-space then makes it an algebraic space. Equality on the intermediate etale cover is equality of open subfunctors, checked by the sheaf condition. I corrected an early draft that would have treated the smooth map P to X as etale: the final argument does not make that claim.

Step 3 uses stack-representable-unramified-descent precisely with the smooth atlas A to the target Y. The calculus statement supplies flatness and local finite presentation of this cover. The restriction is representable, and its pullback is the already unramified O to A. Maximality uses the largest-open clause of the space locus lemma and the factorization clause explicitly present in invariant-open descent. Thus neither a definition of unramifiedness nor a bare atlas-existence statement is being cited for a descent theorem.

Step 4 proves the stronger space-chart identity by writing the comparison C=A times_Y T and E=X times_Y C. The two applications of the space locus lemma have algebraic-space targets and locally finite type source maps. C to T is smooth surjective, whereas T to Y is arbitrary; in particular I did not assume that the requested base change was flat. A scheme refinement H of E makes H to X_T a smooth surjective scheme atlas. The inclusion-preserving bijection from invariant-open descent detects equality there. This is the comparison omitted at the end of the source proof, written explicitly rather than hidden in a new restatement node.

Step 5 verifies that X' really is an algebraic space by applying representable pullback to g and X. It checks the hypotheses needed to repeat the already proved construction for f', and compares the two opens on a smooth atlas of Y'. Detection of equality again uses the scheme refinement and the invariant-open bijection. Thus the argument is independent of the choice of atlas and supplies equality as open subspaces, not only a statement about selected field-valued points.

Step 6 reads the precise statements of space-unramified-permanence (etale implies unramified and composition), space-etale-open-image (image I is open with a surjective etale factorization), and unramified-etale-compatible-charts (one compatible source-surjective scheme chart suffices). These are exactly the clauses used in the two inclusions. For the reverse inclusion the source chart is J to I and the target chart is the identity of T, so source surjectivity really holds even when the original c is not surjective. Maximality of the space locus gives I contained in L. The final pointwise assertion is membership in an explicitly described union of open neighbourhoods.

For small cases I checked empty source and empty atlases (all loci and comparison opens are empty); an already unramified f (the locus is the whole source); a scheme target and the identity chart (the statement reduces to the existing space/scheme locus); and a non-surjective etale chart (the image factorization, not surjectivity of c, is used). I also checked the ramified map t maps to t squared over a field of characteristic different from two: the origin is excluded and remains excluded after extension of the base field. No flatness, separation, quasi-compactness or local finite presentation has been added to f or g.

Every non-elementary result used is a cited existing node, with its statement read in full and its relevant clause copied to citations.json. All six steps are marked non-elementary; each is under 2000 characters, and none hides a separate comparison lemma or relocates an item clause into a new node. `proof_deps` is exactly the union of their uses. The statement's existing definition dependencies were retained. No source, chapter, unit, review, Lean, import or provenance fields were changed, no compiler was run, and only sandbox files were written.

## Validation and unfinished work

The preliminary server review_split passed with zero new nodes and the declared open-image tool use. It notes the pre-existing absence of a unit realization, which this supporting item is not authorized to fill. The full delivery dry run and push follow this report; their actual tool results determine delivery. No mathematical obligation of this one-level split is left unfinished; its existing unsplit dependency nodes remain their own queue items.
