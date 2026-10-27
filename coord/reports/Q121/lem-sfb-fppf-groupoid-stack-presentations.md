# Stage-1 delivery: lem-sfb-fppf-groupoid-stack-presentations

Group Q121; direct delivery; 2026-10-23.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-groupoid-stack-presentations.json`: statement, now split in seven steps; no Mathlib match for the item.
- `citations.json`: 20 citations, each quoting verbatim the statement actually used.
- `report.md`: this report.
- `searches.jsonl`: five fresh searches run through the required msearch.py command; prior searches in the item are retained.

New nodes: 0. New Mathlib leaves: 0. The apparent missing ingredients all have existing DAG nodes. In particular, `lem-sfb-flat-groupoid-algebraic-quotient` is a stronger existing theorem for clause (1); it is cited, not duplicated. `lem-sfb-self-relation-quotient-embedding` supplies the fully faithful comparison in clause (2), but does not supply its local essential surjectivity, which is proved here.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, quotient-stack, fppf/groupoid and associated terms. No declaration states the three clauses, and no partial or sorried result is represented as a finished proof. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None. Every source used is present under `literature/stacks-project/`.

## Corrections and scope

The item was statement-only, and the sandbox initially contained only dispatcher brief markers. There was no earlier split or report to replace and no stage-1 repair note. The statement's doubled TeX backslashes were normalized. Its inherited universe convention is now explicit, and the algebraic-stack convention now says etale stack with smooth atlas and cites the existing theorem that implies fppf descent. This is the same notion, not an additional hypothesis. The original repeated surjectivity sentences are retained.

The original source description limited clause (1) to diagonal/presentation properties and pointed to the smooth-groupoid proof. The existing DAG already has the general flat-groupoid theorem. I read criteria.tex 06FH and 06FI: 06FH states the flat lfp presentation, and 06FI proves algebraicity. Using the already existing stronger theorem introduces no smoothness hypothesis on s or t. Clause (3) needs no flatness assumption on either groupoid's source or target: only q is an fppf scheme covering. Nothing of that kind has been added.

The item is not the unit's key statement, so no unit realization file is changed. I read the recorded chapter and unit, SETUP's three levels, GOAL, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. The blueprint ancestor command still returns None; I retain the inherited null ancestor, full via chain and exact place instead of inventing a blueprint node. The split_report explains the inherited stable-curve/field-cover prerequisite. Searches of all blueprint nodes for quotient/stack, fppf/descent and fully faithful/stack yield no blueprint statement of this item. Generic trace-formula-filed nodes used here supply only fibre products and fppf-cover base change, not a trace-formula or duality proof route; these uses are declared in split_report.tool_uses.

## Mathlib searches

I ran five searches through msearch.py for this item: two LeanFinder phrasings (quotient/presentation/restriction, and self-relation presentation), Loogle `"Groupoid", "Scheme"`, LeanSearch on quotient stacks and fppf restriction, and grep `quotientStack|QuotientStack|GroupoidScheme`. Both semantic searches and the second phrasing were read. LeanFinder returned scheme flat descent, site covers and abstract stack conditions; LeanSearch returned `Pseudofunctor.IsStackFor` descent-data equivalences and unrelated module quotients; Loogle and grep returned no hits. The abstract descent-data statements neither construct algebraic-space quotient stacks nor imply the geometric properties of the item by one-line specialization. The item retains its inherited search records and appends the exact five new tool/query pairs with their actual result summaries. No search was invented and no unavailable service was described as an absence result.

## Not duplicates

No new node is created. Existing broader or partial statements are reused explicitly. In particular, the flat-groupoid quotient node already gives all of clause (1), and the self-relation quotient node gives only the fully faithful comparison used in clause (2). Neither restates clause (3).

## Review by Q121

I read sections B through E of delivery-errors.md in full and checked the seven steps against the node statements and source proofs, not merely their titles. The item's sources read were algebraic.tex 04T4 (self-relation construction, canonical map and full faithfulness), 04T5 and 04WY (local lifting and essential surjectivity), criteria.tex 06FH and 06FI (the general flat groupoid result), spaces-groupoids.tex 044V, 04M9, 046S and 046T (Isom formula, self fibre product and restriction), and stacks.tex 046N. I also read criteria.tex 076V to check the etale/fppf convention and topologies.tex lemma-fppf for coverings. There is no new node whose source needs a separate review, and no SGA source is used.

1. Step 1 cites `lem-sfb-flat-groupoid-algebraic-quotient`. I opened its statement: it allows algebraic spaces U and R, assumes exactly flat lfp source/target, and asserts the diagonal, object-map properties, and arrow-map equivalence with the projections. These are exactly the parts used. This is reuse of an existing theorem, not moving a clause into a newly invented node.
2. Step 2 cites `lem-sfb-etale-smooth-atlas-fppf-descent`, `lem-sfb-self-relation-quotient-embedding` and `def-trf-scheme-algebraic-space`. The first really provides fppf descent under the smooth-atlas hypotheses already included in the meaning of algebraic stack. The second explicitly constructs R and all groupoid operations and the fibrewise fully faithful i with specified i pi isomorphic to a. The last allows the scheme U to be used as that node's algebraic-space source. The projections R to U are scheme base changes of the given a, so their flatness and lfp are precisely the hypothesis's test; no claim of scheme representability of R is made.
3. Step 3 cites `def-trf-algebraic-space`, `lem-sfb-space-local-properties-chart-test` and `def-pc-fppf-site`. The first supplies the surjective etale scheme chart W to the representable pullback F. The second explicitly includes both flat and lfp, applies with target chart T itself, and thus gives those properties for W to T. Surjectivity is proved here from two successive field extensions, using the point of F as an object together with its isomorphism. Therefore W to T is an actual fppf covering by the third citation. This avoids incorrectly treating the algebraic space F as a scheme and avoids an unstated existence of local scheme lifts.
4. Step 4 cites `lem-sfb-groupoid-stackification-local-description`, `lem-sfb-stack-fully-faithful-local-equivalence` and `def-pc-fppf-site`. The source is an fppf stack by stackification; the target's fppf descent was established in step 2; full faithfulness is supplied by the self-relation node, and local essential surjectivity is exactly step 3. All hypotheses of 046N therefore hold. The specified isomorphism from step 2 proves compatibility with a, rather than merely an abstract equivalence of fibres.
5. Step 5 uses the extension and Isom-sheaf clauses of `lem-sfb-groupoid-stackification-local-description`, actual space fibre products from `lem-trf-space-fibre-products-etale-covers`, the fppf-sheaf condition in `def-trf-algebraic-space`, and the universal property of `def-weil-pbc-sheafification`. The restriction hypothesis identifies the two arrow presheaves by an actual pullback formula, including the arrow map. The two sheafification units are isomorphisms since both presheaves are already sheaves. This provides exactly the comparison map on Isom sheaves; an unrelated Yoneda or fully faithful result is not substituted for it.
6. Step 6 uses the local-object property of the stackification node and the fppf site. The conjugation reduces arbitrary object pairs to the pairs in step 5. The local-isomorphism test for sheaves is written out by restriction, uniqueness, and gluing, so no hidden non-elementary comparison theorem is invoked. This is the routine sheaf argument in the proof of 046S, not a new lemma requiring a node. It uses no atlas theorem or flatness of the groupoids.
7. Step 7 cites the stackification node, `lem-trf-fppf-covering-base-change`, the fppf site and the local-equivalence criterion. The covering-base-change node explicitly applies to the scheme map q, so W_i to T_i is an fppf scheme covering. Its tautological u maps to v under q, and the specified isomorphism of step 5 gives the desired lift. Successive localizations are allowed by the site axioms. The full-faithfulness hypothesis was proved in step 6 and both quotients are fppf stacks regardless of their source/target properties. Thus 046N applies and yields an equivalence over the site with the required compatible atlas square.

Every cited statement was opened and all 20 quotes are literal substrings of the current node statements. For multiple-property uses the quote retains the full statement rather than a short fragment hiding hypotheses. I checked that no dependency closure reaches this item, so none of the reused results introduces a cycle. Every non-elementary input is a cited existing node; the direct point-lifting and sheaf-gluing arguments are written out. All steps are below 2000 characters. I checked B's statement-only/self-contained/definition/TeX/source/search/Mathlib/blueprint rules, C's source-statement adequacy and dependency rules, D's no-relabelling/no-whole-proof-transfer/no-circularity rules, and E's hypotheses and object identifications. There are no newly created statements to test. For the item I tested the identity groupoid, a nontrivial stabilizer group over a field (the self relation keeps the stabilizer, not the set of orbit classes), identity q, and the empty scheme: an fppf surjection from the empty scheme forces an empty target, and the empty covering/descent convention causes no exception. In particular clause (3) is valid even for groupoids whose arrows are not flat, because its proof never uses that property.

## Unfinished work

None in this stage-1 split. Proofs of existing dependency nodes remain their own items. No new Mathlib leaf is claimed. The required dry run and final push are performed after this report is written; their terminal results determine the final delivery answer.
