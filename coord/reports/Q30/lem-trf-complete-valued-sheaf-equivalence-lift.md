# Stage-1 delivery: lem-trf-complete-valued-sheaf-equivalence-lift

## Files written

- dag/nodes/sec-trace-formula/lem-trf-complete-valued-sheaf-equivalence-lift.json: existing statement, now split into six steps; original statement, source, provenance and historical searches retained.
- dag/nodes/sec-trace-formula/lem-trf-small-pointwise-right-kan-adjunction.json: statement, Mathlib leaf; ranAdjunction with its pointwise-limit formula and normalized unit/counit.
- dag/nodes/sec-trace-formula/lem-trf-hom-right-kan-comparison.json: statement, Mathlib leaf; ranCompIsoOfPreserves specialized to covariant representable Hom, with the counit equation.
- citations.json: a verbatim statement quotation for every node cited at every numbered step.
- searches.jsonl: actual msearch.py output log, retained in full.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and by complete/category-valued sheaves, equivalence and right Kan terminology. No declaration proves the item with all its hypotheses and conclusion. The nearby EtaleSetPullbackSheafEquivalence and topological-invariance files do not state this general theorem. New-node exact ids, right-Kan and comparison declaration-name searches found no project attachment either.

## Wanted sources

None. The item explicitly records an agent generalization rather than a theorem of Stacks 00VR. I read sites.tex, definition-sheaf and its preceding Hom-test discussion (00VR), and categories.tex, lemma-yoneda and the definition and Hom formula for a limit. For the two generic categorical leaves I read the actual Mathlib sources and lines listed below. The full assembly is marked proof_origin.by=agent; it is not attributed to 00VR.

## Audit of the original item and blueprint

The item was unsplit with no sandbox attempt or report to recover. No repair note exists. It already had semantic, pattern and grep searches from its creator: these were preserved; this worker also ran fresh searches of the item under two semantic phrasings, Loogle and grep and inspected the hits. sheafCongr assumes an equivalence of the underlying site categories; DenseSubsite.sheafEquiv assumes dense-subsite data. Neither is the assertion here by a one-line specialization. The item is not a Mathlib leaf.

The original statement is true and is unchanged. No hypothesis or conclusion was weakened. Finite limits and preservation of coverings guarantee the intended restriction, but the proof in fact only needs the explicitly assumed restriction equivalence, subcanonicity, and completeness for the small comma diagrams. The source's mention of a category-of-elements limit is realized concretely as (u downarrow d)^op, not as a limit indexed by the large category of all sheaves. No presentability, cocompleteness, smallness of the collection of objects of A, or sheafification with A coefficients is inserted.

I read dag/chapters/sec-trace-formula.json, dag/units/sk-i-topology.json and the latest blueprint sk-i-topology/_section.md and i-topology.proof.md. This serves the first paragraph's equivalence on sheaves, before the derived step, and does not change that route. The source's SGA references play no role and no SGA source is cited. The ancestor command returns None through the maintainer audit-created parent (created.item=null). I retained the existing null from.node, filled specific places for both new nodes, and used the prescribed via list. The intended mathematical ancestor is i-topology, as its parent's review already notes. No unit realization fields are due: the item is not the unit's key node.

## Not duplicates

No new node carries a Stacks tag: their source statements are the actual Mathlib declarations, not the sheaf definition. The entire DAG was searched by right Kan, pointwise extension, Hom preservation, Yoneda, declaration names, and categories-of-elements terminology; blueprint_refs searches for Kan, right Kan, right Kan extension, sheaf equivalence, Yoneda and representable functor found no duplicate. The two new ids were absent before creation.

lem-trf-small-pointwise-right-kan-adjunction vs lem-sfb-right-kan-extension-unique-iso: the latter assumes two already existing Kan extensions and proves unique compatibility; the new leaf supplies existence, the comma limit formula and the adjunction for every small diagram. No duplication.

lem-trf-small-pointwise-right-kan-adjunction vs lem-sfb-pointwise-kan-colimit: that node treats a particular left Kan extension of abelian presheaves from the profinite-point site, with colimits; this leaf is the general right Kan/limit/precomposition adjunction for arbitrary complete coefficient categories.

lem-trf-small-pointwise-right-kan-adjunction vs lem-cbc-local-dense-ordinary-sheaves: that node proves sheaf comparison under local-fullness, local-faithfulness and covering hypotheses. This new leaf is exclusively about ordinary functor categories and has no sheaf or density assertion.

lem-trf-hom-right-kan-comparison vs lem-sfb-right-kan-extension-unique-iso: this leaf gives preservation by Hom and an equation for its comparison and counits; uniqueness of preexisting right Kan extensions does not state preservation.

lem-trf-hom-right-kan-comparison vs lem-coef-joyal-homset-iso-detection: the latter detects invertibility from Hom bijections, not preservation of Kan extension. Both are used for separate purposes.

The infinity-category Kan nodes use spaces/quasicategories and mapping-space universal properties, not ordinary arbitrary complete coefficient categories. Their statements are not the two new leaves. Neither new leaf mentions sites, set-sheaf equivalences, or the conclusion of the item. These are genuine general tools rather than clauses of the item.

## Review by Q30

I checked delivery-errors B through E against the actual JSON, the current sources and every cited statement. The new leaves contain statements only: no proof steps, hidden proof sketches, or proof dependencies. Each introduces C,D,L,A, the universe, limits, transformations and relevant maps; the second cites the first for its Kan data. Their only definition dependencies are the existing size and category definitions, which I opened. Their formulas use single TeX escapes after JSON decoding.

For the first new leaf I read Pointwise.lean:56-61 (pointwise existence is existence of the comma limits), 713 onward (the pointwise construction), 733 onward (counit projection), 750-767 (universal property and existence); Adjunction.lean:295-305,318-335,343-370 (ran, projections, adjunction and normalized transformations). The finite source and target universes are not confused with the possibly larger object universe of A. The assumed V-small limits give every comma limit, so the Mathlib prerequisites are inferred directly, not by a missing theorem. The multiple declarations listed in mathlib_match give one clause each, as permitted for leaves.

For the second leaf I read Limits/Yoneda.lean:140-151,180-182 (Hom(a,-) preserves limits) and KanExtension/Preserves.lean:405-430,452-467,534-549. I checked the direction of the comparison and copied the actual counit equation: chi followed by the set-valued counit equals Hom applied to the A-valued counit. Preservation instances are consequences of the listed Mathlib instances for the very same comma limits. No claim about commuting arbitrary Hom with colimits is made. The search records come only from the real msearch invocations, and retain exact query text, hit names, and subdirectories. Both leaves have all required search kinds, and their source lines were opened.

Step 1 cites the first leaf for existence, functoriality and the adjunction. That statement gives each of them. I checked that StructuredArrow(d,u.op) has objects u(c)->d in D, so its indexing category is (u downarrow d)^op, with the opposite in the right place. Objects and arrows of that category are sets in V; there is no larger hidden index.

Step 2 cites the full general lem-galois-yoneda-hom-bijection, not merely full faithfulness of the Yoneda embedding, and the first leaf's limit formula. I opened its statement and checked that it provides both evaluation and naturality in the representing object and in the presheaf. Subcanonicity makes h_d an actual sheaf, so full faithfulness of the assumed restriction equivalence applies to h_d and EF. I wrote out the transformation as the family x_(c,alpha) and its exact compatibility equation, rather than hiding a density theorem. That family is the definition of a limit in sets, so this is a direct elementary calculation from the cited formulas, not an unlisted comparison lemma. Reindexing d and acting on F are specified, proving naturality needed for sheafness. This argument is under 1000 characters and has no deferred sublemma.

Step 3 uses exactly the second leaf's natural Hom/Kan comparison and the first leaf's adjunction. It tests every a of A, as required by the original statement and Stacks 00VR, and proves both functors preserve the full sheaf subcategories before restricting the adjunction. Thus no assertion that a presheaf Kan extension automatically is a sheaf is assumed.

Step 4 uses lem-coef-adjunction-equivalence-counit-iso, whose statement has the left adjoint an equivalence: here the left adjoint really is R_set. I checked this direction carefully, since using an inverse-image adjunction instead would be wrong. It only claims counit invertibility; the proof does not take unit invertibility from it. The second leaf supplies the precise counit equation, so the Hom maps of the A-counit are bijections. The existing lem-coef-joyal-homset-iso-detection states the required postcomposition criterion for every test object, and applies in A at each c. Component inverses give the natural inverse by the naturality square. These citations say exactly what the step uses.

Step 5 cites the same Hom-detection statement, now at each d. The only equivalence fact used is reflection of invertibility by full faithfulness, and its proof (lift the inverse and check its identities by faithfulness) is written out. Therefore this elementary step does not need a new categorical lemma. It does not assume A has a small set of detectors: all objects a are allowed.

Step 6 cites the first leaf for the triangle identity of the actual adjunction. Steps 4 and 5 make the restricted unit invertible. The two natural isomorphisms are then literally the quasi-inverse data; no unproved criterion identifying an equivalence is imported. The proof explains which composite and which unit/counit are meant. All proof_deps are the union of step uses, and citations.json quotes the actual statements verbatim for every occurrence. All external-unit proof tools here are Mathlib leaves, so no off-route tool declaration is needed.

I tested u=id (the comma formula reduces to the original evaluation and both transformations are identities up to the chosen limit comparison), A=Sets (recovering the given equivalence), A=Ab (the Hom tests are ordinary Hom sets), the terminal category A (all values and comparisons unique), and sites with an empty covering (the sheaf value is forced terminal and Hom-test gives singleton sets). I also checked an empty comma category: its limit is terminal; the family description is the singleton empty family, so the formula and Hom comparison remain valid. Empty categories without finite limits are not smuggled into the item's hypotheses, but both general Kan leaves allow them and use the assumed empty limits. A is necessarily nonempty because it has a terminal object; no arbitrary element of A was chosen.

Corrections during the self-review were to make the opposite-comma convention explicit, retain the set-counit direction rather than silently use both adjunction maps as invertible, and obtain unit invertibility from the triangle identity and reflection. No statement correction was necessary. No step exceeds 2000 characters and no substantial source argument is hidden by a long step.

## Unfinished work

None in stage 1. No Lean was written or compiled; the two new dependencies are Mathlib leaves. Required server dry run and push follow this report.
