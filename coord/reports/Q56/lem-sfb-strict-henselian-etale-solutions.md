## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-strict-henselian-etale-solutions.json`: statement split, unchanged statement; no exact Mathlib match. The inherited seven search records are retained and five newly executed, logged searches are appended.
- `citations.json`: seven verbatim statement quotations, covering every use in all five proof steps.
- No new DAG nodes and no new Mathlib leaves. The preparation script and search log are sandbox research artifacts.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag, Tag 04GX, polynomial solutions and the strictly henselian notion found no declaration giving the entire item. The section-existence theorem in `AlgebraicGeometry/Sites/StrictlyHenselianLift.lean:138` supplies existence of sections through closed-fibre points, not this bijection or its uniqueness, and is not an attachment.

## WANTED

None. All proof sources used are present in `literature/`.

## Corrections and findings

The statement agrees with Stacks Tag 04GX (`algebra.tex`, label `lemma-strictly-henselian-solutions`, lines 42635 onward); no statement dispute or correction is needed. Its proof was empty. I retained the source, statement dependencies, provenance and inherited Mathlib searches, and wrote the proof from the Stacks argument. No previous sandbox split or report existed.

The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof were read for context. The item's inherited ancestry is a long prerequisite chain ending in the affine solution comparison and its use of 04GX. `tools/blueprint_refs.py ancestor` returns null for that existing chain; I retained its existing null ancestor and fully specified place. The chapter and unit are unchanged. Whole-blueprint searches for henselian, solutions and etale algebra over a field found no blueprint statement of this exact comparison. No new blueprint node or route is introduced.

The only non-Mathlib off-unit statement used is `lem-weil-pbc-henselian-local-target-etale-maps`. It is a generic commutative-algebra tool, not a replacement of a geometric route. Its specialization with target equal to the base gives precisely the residue-reduction bijection used twice in 04GX. This tool use is declared in `split_report.tool_uses` for the maintainer to assess. The other non-elementary input, `lem-weil-pbc-etale-algebra-over-field-product`, and the etale base-change input are existing Mathlib leaves; no duplicate should be created for either.

The new searches actually ran through msearch.py, and I read their results. The two LeanFinder phrasings return standard-etale presentations, root parametrizations and local-property facts, rather than invariance under a local map. Loogle `HenselianLocalRing, RingHom.Etale` returns no hits. LeanSearch returns henselian root lifting, the etale definition and the local-map criterion. The logged grep supplies the standard-etale homEquiv and lift_bijective candidates. I read homEquiv at Mathlib/RingTheory/Etale/StandardEtale.lean:143 and the presentation structure at :262–267: homEquiv only parametrizes roots in one algebra, and lift_bijective is part of a chosen presentation. HenselianLocalRing.TFAE in Mathlib/RingTheory/Henselian.lean:119 describes root lifting and factorization criteria, not the item. None of these is an exact or one-line generalization of the whole statement.

## Not duplicates

No new node was created. The split reuses the existing henselian-map, etale-base-change, etale-over-field and separably-closed nodes. Tag 04GX occurs in the parent affine comparison and ringed-etale reconstruction as an invoked prerequisite, not as another node stating this entire lemma.

## Review by Q56

I read the complete statement and proof of Stacks 04GX, the etale base-change clause in 00U2 (`lemma-etale`), the statement and proof of 00U3 (`lemma-etale-over-field`), and the henselian characterization 04GG (`lemma-characterize-henselian`), including condition (8) and its unique-retraction argument. There are no new nodes with separate sources to review. I opened every cited DAG node and read its statement; the citations file copies the actual parts used, rather than descriptions of their proofs.

For step 1, `def-weil-pbc-mv-polynomial-ring` explicitly gives the polynomial universal property and uniqueness on variables. Killing the listed equations is exactly the criterion to factor evaluation through their ideal. Locality sends exactly the nonunits into the maximal ideal, so the residue-field map is well defined and injective; the equality of the two residue composites follows by the formula on a representative. No smoothness, finite-module hypothesis on D, or additional solution assumption is used.

For step 2, the base-change node explicitly states etaleness of Spec(S tensor_R D) over Spec S and likewise of C over k. The henselian-local-target node explicitly allows the source etale algebra to be nonfinite. Its extra hypotheses concern the TARGET: both applications take that target to be its base itself. It is generated by 1 as a module, and uniqueness of maps out of the base proves formal unramifiedness directly. Both bases are henselian by the terminology node's statement, since the item assumes strict henselianity. The theorem's tensor-reduction map is the residue map used here: evaluate at 1 tensor d. I wrote both scalar-extension formulas and their inverses to check the identifications, instead of claiming an unspecified transport. In particular I never apply the local-target theorem with R as base and S as target, since S need not be module-finite over R.

For step 3, the etale-over-field node explicitly gives finite separable extensions and allows zero factors; no finiteness assumption on D as an R-module is needed. The terminology node supplies separable closedness of k, and `def-kun-separably-closed` explicitly states the equivalent absence of nontrivial finite separable extensions. Thus the structural embeddings into the factors are isomorphisms, not merely unspecified abstract field isomorphisms. This is exactly the residue-algebra splitting in 04GX.

Step 4 is elementary from the product obtained in step 3. I wrote the orthogonal-idempotent argument: a map to a field chooses exactly one factor, and its value on an arbitrary tuple follows from the finite sum of scalar multiples of idempotents. The coordinate label survives postcomposition by the residue-field embedding. The empty-index case has no unital maps from the zero ring into either nonzero field. The tensor formula for K-valued maps is written explicitly and depends only on the already specified field embedding.

Step 5 uses the preceding bijections, not a further lemma. I checked the commuting square on each d, using q_S theta = bar(theta) q_R, and then on each variable class. This proves the actual coordinate map in the item, including its injectivity and surjectivity; it is not just an existence of some equivalence of solution sets.

I tested the small cases n=0 (one empty tuple on each side), D=0 (both solution sets empty), C=0 (the residue Hom sets are empty, hence the full solution sets are empty by step 2), a split algebra with multiple factors (each map chooses its factor), and theta the identity. Local rings are nonzero under the henselian convention, so the residue fields and the use of 0 not equal to 1 are legitimate. No algebraic-closedness or perfectness hypothesis is substituted for separable closedness, and no injectivity of theta itself is assumed. Only its induced field map is injective. In particular the argument also permits a noninjective local map such as the residue map from a strictly henselian ring.

I checked delivery-errors B–E against the finished files: no new-node shape or duplicate issue occurs; every non-elementary step has exactly the relevant statement citations; all uses have verbatim quotes; the proof actually performs the reduction and coordinate calculation instead of moving the conclusion into a new node; hypotheses and objects match throughout. The polynomial, tensor and product computations marked elementary are explicit. Step lengths are 627, 1073, 472, 823 and 646 characters; no step exceeds 2000 characters or hides a longer subsidiary comparison. There is no SGA citation, no Lean edit, no compilation and no repository write.

## Unfinished work

None in the mathematical split. The required remote dry run and direct delivery are the remaining validation and transport steps.
