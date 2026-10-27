# Q159: lem-sfb-space-surjective-affine-limit-criterion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-surjective-affine-limit-criterion.json`: item, now split in five steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-surjective-affine-limit-criterion.json`: new statement-only input, Stacks 0CM0, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/dependency pair (eight entries).
- `searches.jsonl`: actual msearch output records. Existing searches in the live item were retained, and fresh logged searches were added. No earlier sandbox split or report existed.

## Attachments

None. Searched all of `lean/WeilConjectures/` for the item tag, AlgebraicSpace, and surjection/finite-presentation and affine-limit terminology. No project declaration states the item. Scheme flat-descent results and forward finite-presentation results do not attach either node.

## WANTED

None. Both mathematical sources are present locally in the Stacks source.

## Issues found and changes

The live item was statement-only. The scheme criterion already in the DAG, `lem-sfb-scheme-affine-limit-lfp-criterion`, assumes bijectivity in its converse; it cannot conclude local finite presentation merely from the surjectivity obtained here. Added precisely that missing scheme input, rather than pretending the existing statement supplies it.

The Stacks 0CM6 proof calls the relative algebraic-space criterion for the étale chart map. I verified the same lifting step directly on its scheme base change: once the pair at stage j exists, E = T_j ×_Z U is an étale scheme over T_j, so the forward direction of the existing scheme criterion descends the section. This expands the scheme test of that representable étale map and does not change the source's atlas route. It also avoids using the algebraic-space criterion recursively.

No statement dispute, added hypothesis, weakened conclusion, or unit/chapter change. The ancestor command returns `blueprint.from.node = None` for this existing created chain. I retained that value and its inherited place, and set the new node's via list to the item followed by the existing via list. The current latest blueprint contains the inherited direct-images passage at `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); its old `of` identifier remains det-thm-sf-ctf-stability-direct-images. No blueprint statement states either limit criterion.

## Not duplicates

lem-sfb-scheme-surjective-affine-limit-criterion vs lem-sfb-representable-lfp-object-limit-test: the existing node concerns object descent for representable morphisms of fibred groupoids; the 0CM0 occurrence is a source citation, not its statement. The new node concerns only schemes and surjectivity of their absolute functor-of-points comparison over a fixed scheme base.

lem-sfb-scheme-surjective-affine-limit-criterion vs lem-sfb-scheme-affine-limit-lfp-criterion: the existing converse requires a bijective comparison; the new result assumes only a surjective comparison. The latter does not specialize from the former in one line because the missing uniqueness is not an assumption.

lem-sfb-scheme-surjective-affine-limit-criterion vs lem-sfb-space-surjective-affine-limit-criterion: the new node is the scheme input in the Stacks proof, with no algebraic-space chart reduction. The item's steps perform that reduction and the nontrivial compatible chart lift; they do not merely apply the new node to X -> Y.

lem-sfb-space-surjective-affine-limit-criterion vs lem-sfb-space-relative-affine-limit-criterion: the existing algebraic-space criterion requires bijectivity in its converse, while this item assumes only surjectivity. It is not an attachment or a one-line specialization of that node.

The whole DAG was searched for 0CM0, 0CM6, the source label, and affine-limit/surjectivity words; whole-blueprint searches used `surjection-is-enough`, `0CM0`, `affine limit`, `surjectivity`, and `finite presentation`. No existing statement supplies the new input. Mathlib searches used two natural-language phrasings, Loogle, grep, and LeanSearch through the mandated command. I read the candidate finite-presentation definitions at Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:40-105. They concern affine-open ring presentations, forward consequences, and permanence, not this limit converse. The Loogle surjectivity hits concern flat descent/effective epimorphisms with finite presentation already assumed.

## Review by Q159

I read spaces-limits.tex, Tag 0CM6 (lemma-surjection-is-enough), in full, and limits.tex, Tag 0CM0 (lemma-surjection-is-enough), including its proof. The item matches 0CM6, and the new node matches 0CM0 with the project's small nonempty directed-system universe convention made explicit. The new node is only a statement: its eventual proof needs the algebraic finite-presentation characterization and the eventual containment in an open used by the source; those are not silently treated as elementary here. It is a genuine input below the space theorem. It is not a restated clause about chart lifting.

For step 1 I opened `lem-trf-space-fibre-products-etale-covers`: its statement explicitly says the sheaf fibre product of algebraic spaces is an algebraic space. This is exactly the only theorem taken there. Charts are fixed arbitrarily from the conclusion; their existence is not a hidden additional theorem. The map a is required to be a V-map throughout.

For step 2 I opened `lem-weil-pbc-filtered-colimit-sets-elementwise`: clause (1) supplies representatives, and clause (2) supplies a common stage for equality of base representatives. The assumed surjection gives equality of classes, not necessarily equality at the initial index. I wrote the increase to j before defining the pair (c_j,b_j), so the map into the fibre product is valid. Equality after restriction follows by comparing both projections of the sheaf fibre product.

For step 3 I opened `lem-trf-space-representable-etale-scheme-tests`: scheme-source maps are representable, fibre products of two scheme-source maps are schemes, and representable étale morphisms remain étale after base change. These clauses apply to h and z_j without any separation condition on Z. Its scheme test makes E -> T_j étale. I opened `def-weil-etale-morphism`, whose first sentence explicitly includes local finite presentation. It is used only for this definitional consequence, not for a hidden flatness or descent theorem. The map s is a genuine morphism supplied by the fibre-product universal property, not an inference from containment of point sets.

For step 4 I opened `lem-weil-pbc-limit-affine-transition`: the open-subscheme clause with the open all of T_j identifies the tail limit with T. The tail remains small, nonempty and directed; all its schemes are affine. I opened `lem-sfb-scheme-affine-limit-lfp-criterion`: its forward implication applies to the scheme E over the scheme T_j because step 3 has proved local finite presentation. It assumes no compactness or separation of E. The elementwise colimit node gives the stage representative. The equation r a_k = b_k is written out from the pullback square, which is the needed base compatibility.

For step 5 the newly written 0CM0 node says precisely that surjectivity for every affine V-system proves that the scheme map U -> V is locally of finite presentation. Steps 1-4 prove that hypothesis. The charts were arbitrary, so no unproved independence-of-chart assertion is needed. Every step's used statement was opened and is quoted verbatim in citations.json; proof_deps is exactly their union. The two off-unit space lemmas are declared as generic tool uses in split_report, with reasons; their statements give the fibre-product and representability facts rather than a replacement for the unit's argument.

I tested the statement on the empty source and identity morphisms: the empty source satisfies the comparison condition and is locally of finite presentation; identity gives a tautological relative comparison. For the new scheme input, a non-finitely-presented infinite polynomial algebra over a field fails the hypothesis by the identity map into its directed union of finitely generated polynomial subalgebras, as expected. Non-quasi-separated charts and non-quasi-compact E are allowed by the precise cited scheme criterion, so no intersections of affine opens were assumed affine. Empty limits do not require choosing a point: the descent argument applies to the morphism s and the nonempty tail, and works for empty test schemes too. No injectivity for f is used, and no finite-presentation assumption on a test scheme over S is introduced.

I checked delivery-errors B-E against the actual files: self-contained statements, definition citations, single TeX escaping, correct source tags/labels, no unrun search records added, no duplicate or clause-only new node, and every non-elementary input named. All five steps are under 600 characters; none approaches the long-step threshold or hides an independent comparison lemma.

## Unfinished work

No unfinished part of this one-level split. The new scheme node remains unsplit for the next stage-1 item, as required. No Lean was written and no compiler, Lake, or build command was run.
