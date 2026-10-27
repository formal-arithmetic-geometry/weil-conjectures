# Stage 1 worker report

Item: lem-sfb-space-proper-support-below-coherent-image. Group: Q45. Date: 2026-10-24.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-below-coherent-image.json`: statement, split; not a Mathlib leaf. The statement and its statement dependencies are unchanged. Added five proof steps, their exact dependency union, document proof origin, searches, and split report with generic tool declarations.
- `citations.json`: nine verbatim statement excerpts, one for each step/node citation.
- `report.md` and the search command's `searches.jsonl`.

New nodes: 0. Mathlib leaves: 0. No unit file was changed; this item is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, the item id, proper support, coherent image, and the Stacks label. There is no declaration stating this algebraic-space proper-support theorem. The nearby `CoherentSupportProperHigherDirectImage`, `DirectImageBoundedCoherent`, `NoetherianProperBoundedCoherentImage`, and `ProperSupportHigherDirectImageBound` concern schemes or bounded inputs, so they do not give an attachment for the item. Existing abstract truncation declarations are used through their DAG nodes, without claiming a completed proof of the geometric item.

## WANTED

None: all sources needed are available locally.

## Changes and findings

The imported statement is correct. Stacks `spaces-perfect.tex`, Tag 0D0R (`lemma-direct-image-coherent-bdd-below`), allows an auxiliary scheme S; the item is precisely its specialization S=Y. Consequently the support condition is properness over the target, while the ambient map need not be proper, separated or quasi-compact. No upper bound is added to G.

The source offers a bounded-truncation proof from Tag 08GK (`lemma-direct-image-coherent`). That theorem is already the reviewed node `lem-sfb-space-proper-support-bounded-coherent-image`, with the required nonproper ambient morphism and proper cohomology supports. The abstract comparison is already `lem-weil-pbc-derived-functor-truncation-iso`, and the lower bound is already `lem-weil-pbc-derived-functor-negative-vanishing`. No new lemma is justified. The elementary verification of additivity and left exactness stays in the item's proof, rather than becoming a node.

I read the chapter and stored unit records, the three blueprint levels in SETUP.md, GOAL.md, and the latest blueprint unit and direct-images proof under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The direct-images paragraph (3) is the inherited route. This is its existing coherent structure-sheaf supporting input, not a substitution of a different coefficient category. `blueprint_refs.py ancestor` returns None, as in the original node; the inherited null `from.node` and full `via` history are retained. Searches for proper support, direct image, coherent direct image, 08GK, 0D0R and truncation found no equivalent blueprint node. The bounded theorem differs by requiring an upper bound; the proper-space and proper-scheme nodes assume properness of the ambient morphism and cannot replace the item.

The item's original Q48 search records were retained. I ran the required msearch leanfinder, loogle, grep and leansearch calls in this item's sandbox, including a second semantic phrasing, and read their hits. All services answered. The first semantic search gives abstract standard-t-structure bounds; the second gives scheme local Noetherianity and ordinary pushforward. LeanSearch likewise gives ordinary pushforward and its adjunction, while Loogle returns zero hits. The grep hits at Mathlib/AlgebraicGeometry/Modules/Tilde.lean:567,587 concern underived affine quasi-coherent pushforward. I read that source, Modules/Sheaf.lean, and DerivedCategory/TStructure.lean:180: none states coherent algebraic-space higher direct image with proper supports. The new mathlib_searches entries contain exactly the queries and summaries logged by msearch, with their actual results.

## Not duplicates

No new nodes. The split reuses the existing bounded proper-support theorem and the two existing abstract derived-functor lemmas.

## Review by Q45

I read the statement and both proposed proofs of Stacks 0D0R, the statement and spectral-sequence proof of 08GK immediately above it, and `derived.tex` Tag 05TC (`lemma-negative-vanishing`), both assertions and their proof. The latter proves the fixed lower bound and the comparison with an upper truncation. I also read the first paragraph of `sites-cohomology.tex` Section 07A5 (`section-unbounded`), which says that module sheaves on a ringed site form a Grothendieck abelian category. This is the actual source of the generic module-category theorem. There are no new nodes needing additional sources.

Step 1 cites the exact small-site convention and the statement of `lem-pur-ringed-site-grothendieck-abelian`. The former explicitly supplies a small skeleton in the enlarged universe, and the latter requires a small site and a commutative ring sheaf and gives the Grothendieck property. Structure sheaves satisfy commutativity. In particular this does not apply a scheme-only or constant-coefficient module theorem to an algebraic-space structure sheaf, and does not assume that an infinite space is quasi-compact.

Step 2 reads the actual chart-limit formula in `def-trf-space-etale-module-functors`, not an unmentioned property from its proof. Its compatible families have componentwise addition. The exact kernel formula in `def-weil-sheaf-of-modules-category` identifies a family in the direct-image kernel with a family in the source kernel, which proves preservation of kernels and zero. This is a short elementary argument for additivity and left exactness. The statement of `def-sfb-right-derived-functor` explicitly gives evaluation on a K-injective resolution. The bounded-below and total derived functors therefore agree on the inputs used here by using the same resolution, without a Zariski/etale comparison or a quasi-coherent-category derived functor.

Step 3 uses precisely the implication in `lem-weil-pbc-derived-functor-negative-vanishing`: H^i(L)=0 for i<b implies H^j(RvL)=0 for j<b. Its Grothendieck, additive and left-exact hypotheses have been verified in steps 1 and 2. The bound is the original b for G, not an upper bound extracted from truncations.

Step 4 uses the actual explicit truncation complex in `def-sbc-standard-tstructure-derived-category`, shifted to n. That complex has the original cohomology up to n and zero thereafter. For n at least b it is bounded in [b,n]. Its retained coherent cohomology has exactly the assumed proper support. The extra zero cohomology has empty support, and the empty map is proper directly from the separated, finite-type and universally-closed conditions. The statement of `lem-sfb-space-proper-support-bounded-coherent-image` gives coherent derived image for exactly these objects, assumes only local finite type of f and Noetherianity of Y, and explicitly dispenses with properness or quasi-compactness of f. Thus all of its hypotheses really hold here.

Step 5 cites the final canonical-truncation clause in `lem-weil-pbc-derived-functor-truncation-iso`. I additionally checked the general-map hypotheses: the truncation map is an isomorphism on H^i for i at most n, and is the monomorphism from zero on H^(n+1). Both source objects are bounded below. The conclusion is the actual degree-n cohomology isomorphism required to transfer coherence, not just full faithfulness of some unrelated embedding. Isomorphic finite-module sheaves have the same finiteness property on each affine chart, so this last transfer is elementary. Degrees below b were already handled in step 3. There is no infinite filtration or unjustified convergence argument.

I checked delivery-errors B through E against the files: every cited node exists and its statement supplies the quoted input, no proof-only construction is taken from a cited node, and the dependency union matches all uses. The three off-unit statements are generic module-category and derived-functor tools, explicitly explained in split_report.tool_uses; the geometric bounded theorem is in the same unit. There are no new statement-only nodes, no moved clause of the item, no hidden geometric properness hypothesis and no SGA route. Each step is under 1000 characters, so none reaches the long-step threshold. During this reading I corrected my draft source label for Section 07A5 from section-cohomology-modules to the actual section-unbounded before delivery.

Small cases checked: G=0 and empty X give zero derived image; a shifted coherent sheaf uses the same arbitrary integer b, including negative b; n=b gives a single cohomological degree and the needed monomorphism in degree b+1; a complex with infinitely many positive cohomology sheaves is handled independently in each finite truncation and requires no common proper carrier; empty supports cause no exceptional case. For f=id the comparison recovers the original cohomology. A non-quasi-compact disjoint union mapping to Y is not excluded: the argument only invokes properness of the individual supports, exactly as 08GK states.

## Unfinished work

No unresolved stage-1 mathematical issue. The existing dependency nodes remain separate project items as appropriate; this delivery writes no Lean and makes no compiler or axiom-check claim.
