# Stage-1 delivery: lem-per-small-singular-locus-resolution

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-small-singular-locus-resolution.json`: item, statement retained, five proof steps, status split.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-small-divisor-formal-completion.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-rig-regular-formal-resolution.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-supported-formal-blowup-algebraization.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-morphism-formal-completion.json`: statement, unsplit; no Mathlib match.
- `citations.json`: eleven verbatim quotation records for all step/dependency pairs.

The sandbox also retains `searches.jsonl`, the actual search responses in `*.research.json`, and the research/writing scripts for reproducibility. These are sandbox resources, not proposed library or launcher changes. No unit or chapter record changes.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` for the exact blueprint tag, desingularization, small singular loci, rig-regularity, formal varieties, and formal algebraization. The matches concern Popescu ring desingularization, completion of modules, and other algebraizations; none states the item or a proposed formal-geometric node. No compiler or Lake command was run.

## Wanted literature

WANTED: Michael Temkin, *Functorial desingularization over Q: the non-embedded case*, arXiv:0904.1592v2, Theorems 2.3.5, 3.1.5, 3.4.1, Lemma 2.4.3 and Corollary 2.4.5, for the item and all four new nodes. The paper is not in the local literature archive. I read the author's PDF online at https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf (2026-10-24); the item already identifies this version. No archival download was made. In accordance with the missing-archive rule, `proof_origin.by` is `agent`, with the online document and exact places recorded.

No SGA source is used. No Stacks tag states the formal-resolution theorem or these combined formal-completion inputs; their sources identify Temkin's actual results rather than inventing tags. Existing ordinary blowup tools use verified Stacks Tags 0805 (`divisors-lemma-flat-base-change-blowing-up`) and 0807 (`divisors-lemma-blow-up-effective-Cartier-divisor`).

## Problems in the supplied material

The supplied item is statement-only and had no argument or proof dependencies. During self-review I made the formal-scheme convention explicitly quasi-compact (a finite affine cover), specified reducedness by affine chart rings, and clarified that a formal blowup completes the ordinary blowup along the original ideal of definition, not along its center ideal. Its statement agrees with the restriction of Temkin's Theorem 3.4.1 to reduced inputs. I preserved it, including the dependence on the auxiliary divisor and deletion of exactly empty centers. Temkin's larger generically reduced category is not silently substituted for the assigned category. No STATEMENT-DISPUTED correction is necessary.

The current blueprint ancestor is `lem-per-artin-gabber-affine-curve`, whose Step 3 concerns the regular local model and purity. The existing dependency chain reaches characteristic-zero ordinary resolution and then this small-singular-locus input. This split supplies the supporting formal-completion argument; it does not replace the perverse unit's route or edit its binding fields. The source's substantive Theorem 3.1.5 remains a separate unsplit node, rather than hiding its independence-of-algebraization argument in the item's proof.

## Not duplicates

Searched the whole current DAG by source URL, theorem numbers, formal varieties, rig-regularity, Elkik, supported blowups and completion of regular morphisms; read the statements of the closest candidates. Ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for desingularization, formal variety, algebraization, completion, regular morphism, supported blow and rig-regular. The general completion search has coefficient-category results, not these formal-scheme results. Project Lean searches likewise provide no attachment.

lem-per-small-divisor-formal-completion vs lem-per-small-singular-locus-resolution: the new node proves geometric properties of a specified formal completion, without constructing any resolution or rule on pairs.

lem-per-rig-regular-formal-resolution vs lem-per-small-singular-locus-resolution: the new node concerns the entire category of rig-regular locally principal formal varieties with distinguished invertible ideals of definition; it provides no ordinary tower on a scheme. Passage to schemes requires both the completion and algebraization inputs and the functoriality argument.

lem-per-supported-formal-blowup-algebraization vs lem-per-small-singular-locus-resolution: the new node is a conditional correspondence of arbitrary supported centered towers, including empty stages, and asserts no existence of a formal resolution rule.

lem-per-regular-morphism-formal-completion vs lem-per-small-singular-locus-resolution: the new node is regularity of an induced morphism on completions, with two possibly different coherent ideals; it asserts no desingularization.

lem-per-small-divisor-formal-completion vs lem-per-qe-ordinary-regular-resolution: the existing statement constructs ordinary towers on all reduced quasi-excellent rational schemes and depends on this item; it states no completion geometry and cannot be used here without a cycle.

lem-per-rig-regular-formal-resolution vs lem-per-qe-ordinary-regular-resolution: the existing theorem concerns ordinary schemes and reaches this item; the new formal-variety theorem is Temkin's earlier independent input (Theorems 2.3.5 and 3.1.5), not an appeal to the later general-scheme theorem.

lem-per-supported-formal-blowup-algebraization vs lem-per-normalized-blowup-completion-descent: the existing statement concerns normalized closed-point towers over a local domain with normal maximal-adic completion; the new statement concerns ordinary supported formal blowup towers on arbitrary Noetherian quasi-excellent rational schemes with any coherent support ideal, with ordered center ideals and uniqueness.

lem-per-supported-formal-blowup-algebraization vs lem-weil-pbc-closed-supported-formal-algebraization: the existing statement algebraizes a coherent module under an assumed category equivalence; it states no correspondence of formal and ordinary blowup towers or detection of regularity of their last levels.

lem-per-regular-morphism-formal-completion vs lem-per-rational-toric-completion-regular-map: the existing statement asserts regularity for particular monoid-polynomial completions and carries fs log geometry; the new statement applies to every regular morphism of the indicated schemes after compatible completion of both source and target.

lem-per-rig-regular-formal-resolution vs lem-trf-descended-resolution-smooth-comparisons: the existing statement assembles smooth comparisons for a specified ordinary finite-type rational rule from affine data; it supplies neither formal resolution nor compatibility with arbitrary regular morphisms across coefficient fields.

## Review by Q21

I read the statement and proof of Temkin's Theorem 3.4.1 on printed p.26, its precise pair category in §3.4.2 on pp.25–26, and Remark 3.4.2. The remark is why the auxiliary ideal remains part of the formal input and why this proof asserts no independence from D. I also read §§2.2.1–2.2.5 and 2.3.1–2.3.4: blowups retain their centers, and a nonempty Cartier center is not an empty stage even when its blowup map is an isomorphism.

For `lem-per-small-divisor-formal-completion`, I read §§2.4.1, 2.4.3, 2.4.9, 2.4.11, 3.1.1–3.1.4, the cited first sentence of the proof of 3.4.1, and the characteristic-zero completion theorem 2.1.6. The statement specifies what formal schemes, rig-regularity, the ideal of definition and the formal singular locus mean. The source's formal closed fibre is reduced: the statement uses D_red as the closed fibre, not an unjustified claim that D is reduced. An effective Cartier ideal stays invertible in this completion; singular support becomes open. Different field components remain finite disjoint formal varieties. These are the input hypotheses to the formal theorem, not a resolution of the original pair in disguise.

For `lem-per-rig-regular-formal-resolution`, I read Theorem 3.1.5 on p.18 and its proof in §3.4.1 on p.25, as well as Theorem 2.3.5 on p.14. Together they give the asserted existence of one strong formal rule. The definition of morphisms in §3.1.4 requires the distinguished ideals to pull back exactly; I retained this requirement. Regular morphisms need not be of finite type and need not preserve a chosen field. The item does not claim to prove this new node: its future split must expose the algebraization, finite-thickening invariance and gluing used by that theorem.

For `lem-per-supported-formal-blowup-algebraization`, I read both clauses and the proof of Lemma 2.4.3 on pp.15–16 and the preceding definitions. Open ideals are defined on some finite thickening, so the centers are the same schemes before and after completion, not merely sets with the same support. The lemma supplies uniqueness with each ideal and its order retained. Clause (ii), with X_sing inside Z, supplies regularity of the ordinary last level and singular support. I made explicit the reduced-input nowhere-density consequence: reduced Noetherian schemes have regular generic points; ordinary blowup charts of a reduced scheme are subrings of its localizations, and their complement of the center is dense. Centers over the original singular set therefore miss the dense open at every stage. This is a consequence attached to the centered correspondence, not a new resolution existence assertion.

For `lem-per-regular-morphism-formal-completion`, I read Lemma 2.4.4, Corollary 2.4.5 and Lemma 2.4.6 on pp.16–17. The hypotheses include quasi-excellence and Noetherianity on both schemes and containment I O_Y ⊆ J; the item's application has equality. The resulting regularity is regularity of the completed affine ring homomorphisms, not just infinitesimal formal smoothness. The most relevant Mathlib hit, `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, was inspected in `Mathlib/RingTheory/Smooth/AdicCompletion.lean:94`: it lifts a map to a complete ring and does not assert regularity of a map between completions.

Step 1 cites the complete geometric conclusion of the first new node and the existence and support/regularity conclusions of the formal-rule node. I checked reducedness, Noetherianity, quasi-excellence, characteristic zero, the Cartier condition, and finiteness of the disjoint union. These are exactly the formal rule's input assumptions. Step 2 uses the supported-tower correspondence, its center identifications and its regular-terminal/singular-support clauses; it also uses the empty-input clause of the same chosen formal rule. No choice of an algebraization is made separately for each morphism: uniqueness is what defines the ordinary rule.

Step 3 uses the simultaneous-completion regularity statement and the formal rule's compatibility statement. The identity E = Y ×_X D gives the required equality of distinguished ideals. Step 4 uses the actual statement of `lem-weil-pbc-flat-morphism-base-change` to keep the projections flat at each level, and the isomorphism asserted by `thm-nagata-blowup-flat-base-change`, whose statement dependency `def-nagata-blowup-flat-base-change-map` I also opened to check which ideals and comparison it names. The supported correspondence identifies each completed level and center. The equality of extended quotient ideals modulo I^N explicitly justifies the comparison with formal pullback; it is not an unspecified transport of centers.

Step 5 uses that the correspondence preserves the centers as schemes, so it detects emptiness in both directions, and its uniqueness over Y to compare the contracted ordinary tower with H(Y,E). `cor-nagata-blowup-cartier-iso` says that blowing up an invertible ideal is an isomorphism; the unit ideal is invertible, so its statement really permits removal of the empty stages. I checked that the proof retains nonempty Cartier stages. The three existing statement tools lie in other units; `split_report.tool_uses` explains each generic use. No definition node is being cited as an unprovided comparison theorem.

Small cases checked: X empty and D empty give length zero; a nonempty regular X with empty D also has empty completion and length-zero resolution. For a smooth X and a nonreduced Cartier divisor such as x² = 0 on A¹, the formal closed fibre is still its reduced point, and the completion is regular. For the reduced node xy = 0, the parameter x+y is a non-zero-divisor and defines a nonreduced finite divisor containing the singular point, so the completion input deliberately does not assume D reduced. A disjoint union with two distinct coefficient fields is still one formal input, preserving synchronization. Pullback to the empty scheme removes all centers. The algebraization lemma allows length zero, empty centers, and nonempty Cartier centers; none of these forces deletion of a nonempty center.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the actual node statements and source. All four new nodes are statement-only, with notions defined inline or via existing definition nodes. None restates a clause of the item on the same category: the proof genuinely passes through formal geometry and a centered-tower correspondence. There is no dependence on the descendant general-scheme resolution theorem. Every non-elementary step has cited statements for its non-elementary inputs; the quotient-ideal observation in Step 4 is an elementary equality explained there. Every citation has a verbatim statement quotation. All five proof steps are below 2000 characters (822, 759, 608, 769, 749 at initial write), so none hides a long inline lemma. No unproved statement has been labeled a Mathlib leaf. The search queries in each new node are copied exactly from actual msearch runs with two semantic phrasings; every service answered and every result was read.

## Unfinished work

The four new theorem nodes are intentionally unsplit frontier items, as required for a one-level stage-1 split. No unresolved mathematical defect in the assembly proof was found. The archival source request remains for the maintainer. Delivery validation and push follow this signed review.
