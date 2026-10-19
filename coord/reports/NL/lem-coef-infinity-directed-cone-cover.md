# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-directed-cone-cover.json`: item, statement unchanged, split into eight steps.
- `dag/nodes/sec-six-functors/lem-coef-decomposition-local-colimit-cocones.json`: new statement-only lemma; no Mathlib match. The last assertion of HTT Proposition 4.2.3.4, expressed on coherent cocone spaces, for arbitrary small ordinary families over a simplicial set and a specified extension whose local cones are colimits.
- `dag/nodes/sec-six-functors/lem-coef-directed-decomposition-right-anodyne.json`: new statement-only lemma; no Mathlib match. HTT Proposition 4.2.3.8 and Remark 4.2.3.9 for a directed cover. No quasicategory or cone assumption on the covering subsets.
- `citations.json`: one verbatim statement extract for each use in each item step.

The sandbox also contains the actual search log `searches.jsonl` and the item-specific preparation script `write_split.py`. Neither is a project node or a delivered library file. No unit record is changed: this item is a foundational descendant, not its unit's key statement.

## Attachments

None. I searched all project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, its blueprint docstring tag, and directed-cone/cofinal-vertex terminology. I also searched the CategoryTheory subtree for decomposition, cocone restriction, and right-anodyne terminology. There is no declaration stating this item, or either new lemma. No sorry declaration of the read-only upstream master is used as a completed proof.

## Sources wanted

WANTED: Jacob Lurie, *Higher Topos Theory*, Notation 4.2.3.1, Proposition 4.2.3.4, Proposition 4.2.3.8, Remark 4.2.3.9, Corollary 4.2.3.10, and Proposition 5.3.1.16 (printed pp. 248–253 and 383–384), for the item and both new nodes. Read online at https://www.math.ias.edu/~lurie/papers/highertopoi.pdf; not downloaded or archived. The item proof is therefore marked `proof_origin.by = agent`.

WANTED: Kerodon Example 4.6.4.9, https://kerodon.net/tag/05YH, for the coherent-transformation formulation of `lem-coef-decomposition-local-colimit-cocones`. I read this online: the blunt-join functor category is the oriented fiber product, and comparison from the sharp join is an equivalence. The needed fixed-boundary/fixed-apex comparison is already explicitly part of `lem-coef-infinity-join-cone-calculus` (dually for right cones). No Stacks tag supplies these coherent results. Kerodon 05YH is not a Stacks citation.

## Findings and corrections

The item statement is sound as written. It explicitly permits non-quasicategorical covering subsets and targets with no other colimits. Those hypotheses must be retained. The original node had no proof; the split supplies the retraction and the universal colimit test. I did not infer final objects of the subsets from a mapping-space criterion, which would require them to be quasicategories. Instead their literal right-cone structures give augmented extra degeneracies, and the existing cone-monomorphism lemma gives right anodyneness of the cone-point inclusions.

The general assembly node already in the DAG assumes that the target has **all** small colimits and produces **some** coherent assembly. It does not assert a restriction equivalence for this specific extension `Hr` into an arbitrary target. Consequently it cannot by itself justify this item's universal assertion. The two new nodes isolate the actual general ingredients of HTT 4.2.3.4 and 4.2.3.8; the item retains the entire cone-specific construction and cofinality argument. Neither new node states the existence of `j` or a clause asserting its cofinality.

The fixed chapter and unit were read. I also read the current main-20261015 `prop-coef-integral-exceptional-adjoint.proof.md`, especially its second paragraph's derived-Hom computation. This remains the inherited ancestry of this foundational chain. No route change, unit repair, statement dispute, or use of SGA is involved. The off-unit mapping-space criterion `lem-cbc-enhanced-functor-cone-calculus` is declared in `split_report.tool_uses`, as a generic tool rather than a replacement for any unit step.

## Unfinished work

No part of this one-level split is postponed. Both new lemmas intentionally have statements only and status `unsplit`; splitting them further is a later item. No Lean was written and no compiler, Lake command or library build was run. This worker will not push the delivery; a fresh reader is to inspect and deliver the dry-run-accepted sandbox.

## Not duplicates

lem-coef-decomposition-local-colimit-cocones vs lem-coef-directed-cover-colimit-assembly: the existing node assumes all small colimits and assembles chosen local colimits over a directed cover; the new lemma concerns the actual restriction map for any specified extension over an arbitrary ordinary family, with no cover, directedness or ambient-colimit-existence hypothesis.

lem-coef-directed-decomposition-right-anodyne vs lem-coef-directed-cover-colimit-assembly: the new lemma is solely a combinatorial right-anodyne inclusion for the decomposition simplicial set. It has no target category, diagram, chosen colimits, or colimit-assembly conclusion.

lem-coef-decomposition-local-colimit-cocones vs lem-coef-colimit-subdiagram-approximation: the existing node is a small-subdiagram assembly theorem in a cocomplete target; the new node is a local restriction theorem for an arbitrary family, without any cardinal or cocompleteness hypothesis.

lem-coef-directed-decomposition-right-anodyne vs lem-coef-colimit-subdiagram-approximation: the existing node concerns colimits of chosen apices, while the new one asserts a right-anodyne map of indexing simplicial sets without cardinal bounds or a target category.

lem-coef-decomposition-local-colimit-cocones vs lem-coef-infinity-directed-cone-cover: the item constructs a specific coherent cofinal diagram with prescribed vertices from literal right-cone structures; the new lemma assumes a local-colimit extension already given and compares its cocone spaces, with no cone structures or prescribed cofinal functor.

lem-coef-directed-decomposition-right-anodyne vs lem-coef-infinity-directed-cone-cover: the item needs prescribed cone vertices and a retraction into a quasicategory; the new lemma needs none of those and only proves the indexing nerve's inclusion into a separate decomposition simplicial set is right anodyne.

lem-coef-decomposition-local-colimit-cocones vs lem-coef-infinity-cofinal-kappa-poset: the existing parent constructs a filtered-poset reindexing of a filtered quasicategory; the new lemma is a local comparison for an arbitrary ordinary family and does not construct such a reindexing.

lem-coef-directed-decomposition-right-anodyne vs lem-coef-infinity-cofinal-kappa-poset: the existing parent has a filtered quasicategory and a prescribed regular cardinal; the new lemma starts with a directed cover of an arbitrary simplicial set and asserts no reindexing functor into that set.

lem-coef-decomposition-local-colimit-cocones vs lem-coef-infinity-blunt-sharp-join-equivalence: both mention Kerodon 05YH, but the existing node is a join-model comparison for arbitrary two simplicial sets; it does not assert the HTT decomposition restriction theorem under local-colimit hypotheses.

lem-coef-decomposition-local-colimit-cocones vs lem-coef-infinity-join-cone-calculus: both mention Kerodon 05YH, but the existing node compares models of a single cone and describes its morphism spaces. It does not remove the family of local colimit cones from a decomposition diagram.

lem-coef-directed-decomposition-right-anodyne vs lem-coef-infinity-cone-mono-right-anodyne: the existing node cones one monomorphism with a single point, whereas the new one involves an arbitrary directed nerve, all cover members and their intersections. The new lemma cannot be obtained by one application of that cone-monomorphism statement.

I also opened the other nodes found by searching HTT 4.2.3.4/4.2.3.8: `lem-coef-small-saturated-arrow-accessibility`, `lem-coef-presentable-cardinal-enlargement`, and `lem-coef-space-presheaf-presentability`. Their statements concern accessible classes of arrows, cardinal enlargement, and presentability of space presheaves, respectively; none states either new fact. Whole-blueprint searches for directed covers, cone vertices, decomposition, local colimits, simplicial subsets, and right anodyne maps found no blueprint node stating a new lemma. Both `same_as` lists are empty.

## Review by NL

I read HTT's entire construction of `K_F` (4.2.3.1–2), the statement and proof of 4.2.3.4, the statement and proof of 4.2.3.8 and its directed-cover remark, the comparison in 4.2.3.10, and the retraction paragraph in 5.3.1.16. For the new local-comparison node, I checked that 4.2.3.4's last assertion applies to **any** extension with the prescribed local colimit restrictions, not merely an extension chosen by its existence argument. For the right-anodyne node, I checked the subset case of Remark 4.2.3.9: the lifting-index poset is the nonempty directed set of indices containing a given simplex, and the degenerate-lift subcategory equals it for a degenerate simplex. The hypotheses require no quasicategory structure on the cover. Kerodon 05YH and the already existing join-cone node distinguish the sharp join models in HTT from the coherent-transformation convention of this DAG; the new local-comparison statement spells out the ordered map used to turn a join cocone into a transformation.

Steps 1 and 3 are direct calculations, not appeals to a hidden final-object theorem. In step 1, appending the cone vertex increases only the final constant block, so deleting the appended vertex is the identity and appending it twice is the final degeneracy. In step 3, each subsequent cone operation is applied after inclusion into the next subset. Deleting an upper index cancels exactly that operation; deleting a lower vertex commutes through all operations; repeating an index invokes the double-append identity. These checks include disappearing blocks, pure nerve simplices and pure K-simplices. They do not assume that the cone structures on different subsets are compatible. This is why they are elementary construction steps, rather than new nodes. `def-cbc-enhanced-diagrams-cones` provides the underlying simplicial, nerve and coherent-functor conventions.

For step 2, I compared the **statements** of the two new nodes: the degreewise subset construction is precisely the general compatible-lift construction specialized to inclusions. There is no inference from either new node's future proof. Smallness follows from small unions of products of the supplied sets, not from a colimit-existence theorem.

For step 4, I read the complete statements of `lem-coef-infinity-cone-mono-right-anodyne`, `lem-coef-infinity-anodyne-cocones`, and `lem-cbc-enhanced-functor-cone-calculus`. The first really applies to any monomorphism of simplicial sets, so applying it to the empty subset of `L_a` gives the point inclusion even for non-quasicategorical `K_a`. The second really gives the whole coherent cocone **space** equivalence for arbitrary indexing simplicial sets, not merely a bijection of homotopy classes or a colimit statement in a cocomplete target. The criterion node explicitly states the dual cocone criterion used here. The normalized identity component makes evaluation composed with postcomposition the identity; two-out-of-three proves the needed universal equivalence. The new local-comparison node is cited here only for its explicit join-to-transformation convention.

For step 5, the new local-comparison statement has exactly the inputs supplied: `A` small ordinary, the subset functor over `K`, `q = Hr`, equality `q|K = H`, and the local colimit cocones just proved. For step 6, the directed-cover node has exactly the hypotheses in the item, and the anodyne-cocones node explicitly accepts the resulting arbitrary shape `K_F`; I never treat `K_F` as a quasicategory. For step 7, the two restriction maps have the same source; precomposition with the retraction supplies an inverse to the first, and their composite is actual restriction along `j`. For step 8, I checked the commuting triangle with the same apex and the criterion node's dual formula. This proves both directions for each **given** cocone and retains naturality through the actual precomposition maps. No existence of all small colimits is inserted at any step.

Small cases were checked before finalizing the new statements. For the local-comparison node, empty `I` makes `K_F = K` and the comparison the identity. If `K` is empty, all `K_a` are empty and the local hypotheses say each specified apex is initial, as required. For the right-anodyne node, empty `K` makes its inclusion the identity of `N(I)`; a one-element `I` gives the familiar final-vertex inclusion into a right cone, for an arbitrary simplicial base. For the item, a one-element cover reduces to its normalized final-vertex cocone. The nested finite simplices in `N(N)` give `j(a) = a` and the expected inclusion on chains. I also checked a two-stage cover `(boundary Delta^2)^right-cone` inside `Delta^3`, with the same last vertex: the first subset is not a quasicategory, but the construction and right-anodyne argument remain valid. Repeated indices give degenerate simplices, as the explicit formula requires. Empty `K` is excluded in the item by its nonempty index set and nonempty cone members, but remains correctly allowed in both new lemmas.

I compared every citation with the cited node's statement, checked statement dependencies and proof-dependency unions, retained all inherited fields, and copied actual extracts into `citations.json`. The Mathlib records are the exact searches and result summaries logged by `msearch.py`, with a second semantic phrasing for each new lemma. All services answered; there are no fabricated searches or unavailable-service conclusions. The semantic hits are ordinary category theory, ordinary colimits of simplicial sets, or Quillen-model horn generators, and cannot supply either coherent statement in one line.

The preliminary server `review_split` check passed. Its printed count of zero new nodes is not the worker count: that script excludes nodes already present at its temporary committed HEAD. This sandbox has exactly two new node files, whose full statements, source references and search logs were checked above. The required full delivery dry run is the final acceptance check.

## Second reading by NL

- Item statement: checked against HTT Proposition 5.3.1.16 (PDF pp. 400–401; the project source citation's printed pagination is retained); all hypotheses, prescribed cone vertices, non-quasicategorical subsets, and universal cocone conclusion agree.
- New node `lem-coef-decomposition-local-colimit-cocones`: checked against HTT Notation 4.2.3.1 and Proposition 4.2.3.4 (PDF pp. 265–268); the arbitrary ordinary indexing category, maps over `K`, specified extension, local colimit hypotheses, and restriction mapping-space equivalence are all present.
- New node `lem-coef-directed-decomposition-right-anodyne`: checked against HTT Proposition 4.2.3.8 and Remark 4.2.3.9 (PDF pp. 269–270); directedness, increasing simplicial-subset cover, degreewise decomposition, and absence of quasicategory/cone assumptions are correct.
- Step 1: checked the augmented right-cone identities directly from the join definition in `def-cbc-enhanced-diagrams-cones`; elementary and covers empty, pure-cone, and repeated-vertex cases.
- Step 2: checked the two cited decomposition statements and the definitions; the inclusion-specialized compatible-lift construction is exactly the displayed `K_F`, with no hidden proof use.
- Step 3: checked each face and degeneracy against the stated cone identities and inclusions; the retraction and its restrictions are explicit, including pure blocks and disappearing blocks.
- Step 4: checked the statements of the cone right-anodyne, anodyne-cocone, cone-calculus, and local-comparison nodes; each cited node supplies the claimed mapping-space fact under the hypotheses, with no final-object assumption on `K_a`.
- Step 5: checked the local-comparison node against `q = Hr`, the subset functor, and the local cocones; its hypotheses match exactly and no ambient cocompleteness is added.
- Step 6: checked the directed-cover node and anodyne-cocone node; `K_F` is used only as a simplicial set, so no quasicategory assumption is introduced.
- Step 7: checked the retraction restriction maps and `r|_K = id`; the inverse and composite are actual precomposition maps and naturality is stated.
- Step 8: checked the dual mapping-space criterion and the commuting triangle for a fixed apex and legs; it proves both directions of the colimiting equivalence.
- Small cases: tested empty and singleton indexing/category cases, a one-element cover, repeated indices, empty `K` where allowed, and a non-quasicategorical cone subset.
- New-node form and searches: verified statement-only form, self-contained definitions and TeX, source places, blueprint ancestry, no duplicate nodes, and recorded LeanSearch/Loogle/LeanFinder/grep results.
- Changes made: none; the worker split and citations were accurate after this second reading. Delivery dry-run and final delivery are the remaining checks.
