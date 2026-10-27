## Worker report

Item: lem-per-reflexive-saturated-free-embedding. Stage 1 only, Q43, 2026-10-24. The sandbox initially contained only dispatcher brief markers, with no node, report or search log. I copied the current item and preserved its statement, blueprint lineage and inherited Q31 Mathlib search records. I added the existing finite-generation definition to statement dependencies; this is a notion already in the statement, not a new hypothesis. The mathematical statement is unchanged.

Files written under dag/nodes/sec-deligne-laumon-a1/:

- lem-per-reflexive-saturated-free-embedding.json: split into five proof steps, retaining Tag 0AV2's presentation-and-dualization proof and expanding its converse diagram chase.
- lem-per-torsion-free-bidual-injective.json: new statement-only lemma, Stacks 0AV0(3); no Mathlib match.
- lem-per-finite-injection-bidual-injective.json: new statement-only lemma, the injectivity claim proved within Stacks 0EB8; no Mathlib match.

The auxiliary files are citations.json, searches.jsonl and this report. write_split.py is a sandbox-only authoring script, not a project or delivery tool.

Attachments: none. I searched lean/WeilConjectures for the literal blueprint id and for reflexive, Reflexive, saturated embeddings, biduals and double duals. The finite-projective, finite-product and DVR-quotient duality declarations are different statements, so none supplies every clause under this item's hypotheses. No Lean was written and no compiler or build tool was run.

WANTED: none. All mathematical sources used are present in literature/stacks-project/.

There is no statement dispute or source error. The original imported item was statement-only; its proof is supplied here. In particular, the source does not require normality. I did not infer exactness of the top row in the bidual diagram: Stacks explicitly says this is not known, and the delivery instead uses injectivity of the first map and an explicit evaluation calculation. The inherited geometric provenance is historical: the latest ancestor's proof Step 3 concerns duality symmetry, and does not explicitly mention this commutative-algebra lemma. This item is a refinement of the flat-reflexivity input in the already recorded strict-local divisor route, not a proposed new chapter or unit route.

## New nodes

lem-per-torsion-free-bidual-injective states the evaluation-injectivity characterization for any finite module over a domain. It does not assert reflexivity, a free embedding, or existence of a torsion-free quotient. Its Noetherian-free formulation is exactly 0AV0(3).

lem-per-finite-injection-bidual-injective states preservation of injections by double duals for arbitrary finite modules over a Noetherian domain. It does not assume reflexivity or a saturated embedding, and does not assert that a module is reflexive. Its source is the claim inside 0EB8, not the whole kernel-reflexivity lemma. That claim is proved by localizing the cokernel of the single dual map to the fraction field, where linear functionals extend; the cokernel is therefore torsion, its dual vanishes, and the double dual map is injective. These non-elementary facts are left for that node's later split, rather than hidden in the item's assembly proof.

For each new node I ran LeanFinder with two phrasings, Loogle, LeanSearch and a source grep through the prescribed msearch.py command, then read the hits. searches.jsonl records the actual results; mathlib_searches contains those same tool/query texts and their logged result summaries. All services answered. For the item I also reran all four kinds of search, with two semantic phrasings, retaining the inherited Q31 records separately. Module.eval_apply_injective assumes projectivity; Module.Basis.eval_injective assumes a basis; the field dual-map theorems assume a field; Module.dualMap_dualMap_eq_iff_of_injective compares maps under reflexivity hypotheses. None proves either new statement by one-line specialization. CharacterModule duality has a different target. I checked these hypotheses in Dual/Defs.lean, Dual/Lemmas.lean and Dual/Basis.lean, rather than relying on search-result descriptions that omit ambient assumptions.

## Not duplicates

No existing node has source tag 0AV0 or 0EB8 as its statement's source. The existing flat-reflexivity parent mentions these results in its review history, without stating either new lemma. Searches covered all dag/nodes, source tags and labels, and blueprint_refs.py searches for reflexive, sequence-reflexive, double dual, bidual, torsion free, 0AV0 and 0EB8. No imported blueprint statement matches either lemma; same_as is empty.

lem-per-torsion-free-bidual-injective vs lem-per-reflexive-saturated-free-embedding: injectivity of evaluation is weaker than evaluation being an isomorphism, and no finite free ambient module or quotient is asserted.

lem-per-torsion-free-bidual-injective vs lem-per-reflexive-height-one-intersection-criterion: the latter concerns a normal Noetherian domain and height-one intersections; the new lemma works over every domain and asserts only injectivity of evaluation.

lem-per-torsion-free-bidual-injective vs lem-sfb-semihereditary-torsionless-flat: that node assumes torsionlessness and semiheredity and concludes flatness; it does not prove torsion freeness implies injective bidual evaluation over an arbitrary domain.

lem-per-finite-injection-bidual-injective vs lem-per-flat-base-change-reflexive-modules: double dualization of an injection over one ring is different from scalar extension of a reflexive module along a flat map.

lem-per-finite-injection-bidual-injective vs new-affine-double-dual-stalk: the latter compares geometric stalks with affine double duals, and does not state injectivity of the double dual of a module injection.

The Noetherian submodule-finiteness and contravariant Hom-left-exactness facts already have nodes and are reused. There is no new finite-presentation, finite-dual, finite-free-reflexivity or torsion-free-image node: their short constructions occur in the proof itself. Both new nodes have complete object introductions, inline formulas for their duals and maps, definition dependencies for finiteness (and Noetherianity where used), no proof steps or proof dependencies, and exact source labels/tags. Neither node is a relabelled clause of the embedding criterion.

## Review by Q43

I read more-algebra.tex, Tag 0AV2 / lemma-characterize-reflexive, lines 5308-5330, including both implications and its reference to lemma-sequence-reflexive. I read Tag 0EB8 / lemma-sequence-reflexive, lines 5255-5306, especially the claim at 5286-5305, and Tag 0AV0 / lemma-reflexive-torsion-free, including its statement at 5165-5175 and its proof. I verified the tags against stacks-project/tags/tags. I also read the current chapter and unit records and latest blueprint ancestor's proof, whose Step 3 gives the inherited duality provenance. No SGA source is used.

Step 1 cites lem-weil-pbc-noetherian-submodule-finite. I opened its statement: every submodule of a finitely generated module over a Noetherian ring is finitely generated. This applies to the coordinate image of the dual inside R^s and then to the kernel inside R^n. Finiteness of the dual is not assumed: the evaluation-on-generators injection is explicitly proved, and generators transfer back from its image. Choosing generators of the kernel explicitly gives the presentation. This avoids introducing a redundant finite-dual or finite-presentation node.

Step 2 cites lem-weil-pbc-module-hom-left-exact. I opened its statement: clause (1) requires a surjective last map and equality of image and kernel, both constructed in Step 1; it gives injectivity and the correct middle exactness after applying Hom(-,R). Clause (2) supplies exactly the finite-coordinate identifications used here. The target R in this application is an R-module; no flatness or projectivity of M is needed. This node and the submodule node are existing Mathlib leaves, so their use outside this unit needs no new route declaration.

Step 3 is elementary from Step 2: restricting d's codomain makes q surjective, its kernel is unchanged, and a submodule of R^m is torsion free by coordinatewise cancellation in the domain. Composing the injection with the assumed evaluation isomorphism gives exactly the asserted image and kernel. Nothing requires the quotient to be free. These calculations work with empty coordinates as well.

Step 4 cites the entire statement of lem-per-torsion-free-bidual-injective, which explicitly supplies the implication from torsion freeness to injectivity of evaluation. I checked its finiteness hypothesis rather than taking it from the original item: q(e_k) generate N, since q is surjective. The same step proves finite-free reflexivity with an explicit inverse and proves injectivity of eta_M directly from the coordinate functionals and i. Those calculations do not appeal to the proof of another node or import an unrecorded reflexivity theorem.

Step 5 cites lem-per-finite-injection-bidual-injective. Its statement gives precisely the injectivity of i** used in the final equality. Its hypotheses hold because R is the given Noetherian domain, M is finite by assumption and F=R^r is finite; i is injective in the supplied sequence. The element v is defined using the actual eta_F isomorphism from Step 4. Evaluation against each psi in N* proves eta_N(qv)=0 without assuming exactness after double dualization. Injectivity of eta_N, bottom-row exactness, and injectivity of i** then produce eta_M(m)=x. I wrote these equations rather than saying merely 'diagram chase'. Bijective linear maps are linear isomorphisms because their inverses preserve addition and scalars by applying the original injective linear map.

I tested the new statements and the argument on zero modules, rank zero, fields, Z with a nonzero torsion module, multiplication by 2 on Z, and the ideal (x,y) in k[x,y]. In rank zero, exactness forces M=N=0, and every coordinate sum is empty. For Z/a the evaluation is zero, consistent with the first lemma's converse. For multiplication by 2 the single dual map is not surjective, while the double dual remains injective, so the second lemma does not wrongly require integral extension of all functionals. For (x,y), evaluation is injective although the ideal is not reflexive; its natural inclusion in R has torsion quotient, so this example distinguishes both new lemmas from the item's reflexivity conclusion. Finite free modules over the nonnormal domain k[t^2,t^3] also satisfy the construction, checking that normality was not silently added.

I checked delivery-errors B through E against the files: the two nodes remain statement-only; finite generation and every map are introduced; source tags and labels are right; recorded searches actually ran; all substantive facts of each proof step are stated in its cited nodes. citations.json quotes the full verbatim statement for each of the four step/node pairs. The only elementary step is the explicit image/cancellation assembly in Step 3. All five steps are shorter than 700 characters, with no long-step hidden-lemma issue. I corrected no mathematical statement, but supplied the omitted finite-generation check for N and explicitly avoided the invalid assumption that the top bidual row is exact. There is no cycle through the flat-base-change parent: it is provenance only and is not a proof or statement dependency of either new lemma.

Validation: server review_split passed (exit 0), and the required deliver.py --no-push completed successfully at 23db1878c0b with all server preflight checks passing. A final dry run rechecks this validation note before pushing. There is no unfinished mathematical work at this split level; the two new lemmas intentionally remain unsplit for later items.
