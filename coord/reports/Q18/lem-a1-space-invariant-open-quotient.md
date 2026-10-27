# Stage-1 delivery: lem-a1-space-invariant-open-quotient

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-invariant-open-quotient.json: statement, split; no Mathlib match. Six proof steps, all using existing nodes.
- citations.json: 13 verbatim statement quotations, one for every step/node citation.
- searches.jsonl: five actual Q18 searches, retained without edits.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compilers, builds, repository writes, or git commands were used.

## Attachments

None. The exact blueprint-tag search and concept searches in lean/WeilConjectures found no declaration of the invariant-open quotient or of algebraic spaces. Scheme restrictions and invariant-open descent for schemes do not state this algebraic-space result. There was no earlier sandbox node or report to resume, and no repair note for this item.

## WANTED

None. All sources used are present under literature/stacks-project/.

## Corrections and observations

The original statement is retained verbatim, as are its source, statement dependencies, created record and blueprint ancestry. There is no statement dispute. The original node was statement-only; it now has a proof, proof dependencies, proof origin and split report. The five historical N7 search records are retained, and five real Q18 searches are appended. Neither phrasing in LeanFinder, the LeanSearch query, Loogle nor the whole-Mathlib grep supplied an algebraic-space quotient theorem. The hits concern scheme gluing, scheme restrictions, etale loci, or topological quotients. None has the same kind of objects as this item.

The source's sentence that the inverse images are equal has been expanded into equality of point preimages followed by equality of their open-subscheme structures. The quotient is the sheaf quotient, not the quotient of scheme points or a scheme assumed to exist. The point-image conclusion uses surjectivity on field-valued point classes, not surjectivity on sections over an arbitrary scheme.

## Not duplicates

No new nodes are proposed. Whole-DAG searches for 03BZ, 0262, 02WU, 02WW and invariant-open/equivalence-relation wording found the existing tools now cited. Whole-blueprint searches for invariant open, equivalence relation and open subspace found no statement of this item. The broader quotient search produced unrelated blueprint statements (linear and categorical quotients, coefficient constructions, and Picard definitions), not a second algebraic-space invariant-open construction. The existing lem-trf-etale-open-chart-morphism-descent covers an open descent criterion, not the specified quotient, relation identity, atlas and point image together; no redundant node has been introduced for any of these clauses.

## Review by Q18

I read Stacks spaces-properties.tex Tag 03BZ (lemma-open-subspaces), including the construction from an open point subset and the proof following it. This is precisely the construction required here. I read spaces.tex Tag 0262 (lemma-space-presentation), Tag 02WT (restriction of an etale relation), Tag 02WW (theorem-presentation), and the hypotheses and local-open descent construction of Tag 02WU (lemma-finding-opens). I also read groupoids.tex lemma-restrict-relation and Tag 045Z (lemma-quotient-pre-equivalence-relation-restrict), morphisms.tex Tag 02GP (lemma-open-immersion-etale), and spaces-properties.tex Tags 03H5 and 03BX, with the presentation point argument between them. The tag/label pairs were checked in tags/tags. There are no new nodes whose sources require a separate review. No SGA route is used.

For step 1 I opened lem-a1-etale-atlas-presentation and checked all three assertions used: the actual kernel relation on scheme-valued sections, surjective etale projections, and the canonical isomorphism from the specified fppf sheaf quotient to X. The given representable surjective etale atlas has exactly its hypotheses. def-a1-space-point-topology supplies openness of the inverse image under this representable etale scheme-source map; def-weil-open-immersion gives its open-subscheme structure.

For step 2 I opened lem-weil-pbc-open-preimage-fibre-product: it gives the scheme pullbacks as inverse-image open subschemes, rather than merely a statement about their point sets. The equality p s = p t is the kernel-pair identity from step 1. Its point maps give equal inverse-image subsets. The restricted structure sheaf on an open subset, as in def-weil-open-immersion, makes the two open subschemes equal under their canonical identifications. The double pullback is their intersection, hence the same open subscheme. This is the elementary argument of the source, now written out; there is no extra invariance lemma to create.

For step 3 I opened the Mathlib leaf lem-weil-pbc-open-immersion-etale and lem-trf-etale-relation-restriction-quotient. The first supplies etaleness of V into U, and the second states both the restricted etale equivalence relation and injection of its quotient into U/R. No surjectivity of V into U is assumed or used; only its etaleness is needed. In particular the optional isomorphism clause for a surjective restriction is not applied.

For step 4 I opened lem-trf-etale-relation-quotient. Its hypotheses are an actual monic scheme relation inducing an equivalence relation on every test scheme, with etale projections, not a relation only on topological points. Those hold by steps 1 and 3. Its conclusion states algebraicity and a surjective etale quotient atlas. I checked def-trf-algebraic-space: for these sheaf morphisms etale and surjective are scheme-test properties, so the atlas is indeed representable, not merely locally liftable on sections. The induced map to X and the triangle equation use the canonical quotient morphism already supplied in step 3 and the presentation isomorphism of step 1.

For step 5 I opened lem-trf-etale-relation-finding-opens and checked its statement, not just its proof. It requires s and t to be surjective, flat and locally of finite presentation, and g to be flat and locally of finite presentation. Surjectivity of s and t is supplied by the atlas-presentation node. Their etaleness and etaleness of i give the other hypotheses exactly by def-weil-etale-morphism. There is no quasi-compactness, separatedness or Noetherian hypothesis. Its restricted relation and specified sheaf quotients are precisely the ones constructed here, and its conclusion explicitly gives every scheme-test pullback as an open subscheme. Transport along U/R isomorphic to X therefore proves the representable-open assertion, without a separate implicit descent theorem.

For step 6 I opened lem-a1-space-point-open-calculus and used only its explicit equivalence between representable scheme-test surjectivity and point surjectivity. This gives point surjectivity for q and p; it does not assume the existence of an open subspace for O, so no circular use of the item occurs. The two image equalities are ordinary set calculations using the triangle and |V| equal to the inverse image of O. Finally I opened def-a1-space-open-subspace: the sectionwise injection from step 3 identifies J with an image subfunctor and step 5 gives exactly the scheme-test criterion in that definition. Each cited statement's used part is quoted literally in citations.json.

I checked the small cases O empty and O equal to |X|, and an empty base/atlas. For O empty the restricted schemes and quotient atlas are empty and the resulting point image is empty. For O all of |X| the construction is the original presentation U/R isomorphic to X. These cases do not require a nonempty atlas or surjectivity of V into U. For a disconnected atlas, every equivalence-related pair has the same X-point image, so the invariant-open equality remains valid across distinct components. Arbitrary, possibly non-quasi-compact opens are allowed by all hypotheses checked above.

Against delivery-errors B to E: the item remains self-contained, every notion keeps its definition dependencies, TeX is written once, tags and labels are correct, and no new unsplit node hides a proof. Each non-elementary input is an existing statement, not an appeal to a source or to a cited node's proof. No clause has been renamed as a new lemma. Scheme fibre products and sheaf quotients remain distinct throughout. The proof has no step longer than 2000 characters. The three off-unit statements in split_report.tool_uses are generic relation/quotient tools called for by the Stacks 03BZ route; no unit route is replaced and no top-level tool_uses approval is written by me.

## Unfinished work

None in the stage-1 split. Existing dependencies remain independently eligible for their own stage-1 work; their proofs are not part of this delivery.
