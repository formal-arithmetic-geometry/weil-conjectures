# Q26: lem-pe-ringed-site-derived-evaluation-slice

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-ringed-site-derived-evaluation-slice.json`: item, statement, now split into four steps; no Mathlib match.
- `citations.json`: a verbatim statement quote for every node cited by every proof step.
- `report.md`: this report. The search command owns `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, provenance, and earlier Mathlib searches are retained.

## Attachments

None. Searches of the live `lean/WeilConjectures/` by the exact blueprint tag and by derived evaluation, slice/localized cohomology, and module/abelian comparison found no declaration stating the complete item. The module/abelian comparison is implemented in `lean/Sheaf/CategoryTheory/ModuleAbelianEvaluationComparison.lean` (theorem at line 204), while the separate localized abelian comparison is in `lean/Sheaf/CategoryTheory/Sites/CohomologyOverObjectLocalization.lean` (line 27). They are existing tools, not a project declaration of the complete item under WeilConjectures.

## WANTED

None. All sources used are present in the repository.

## Issues in the imported item and blueprint

The item had no proof; its statement is correct and unchanged. Its provenance points to the first paragraph of the current main-20261015 comparison proof, via the existing injective-left-module comparison item. The legacy `dag/units/sk-prop-sf-comparison.json` records the older smooth-purity unit, whereas the current blueprint places the corresponding unit in sec-proetale-coefficients. I read both and used the current `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sf-comparison/sk-prop-sf-comparison.proof.md`, whose first paragraph invokes injective acyclicity and the comparison of derived sections. Neither the chapter nor unit record is modified.

The existing module/abelian comparison already includes arbitrary ring sheaves, the same common-universe/enough-injectives hypotheses, naturality, and degree-zero normalization. It is not restricted to constant or commutative coefficients. The existing cohomology-over-object-localization node supplies the abelian localization theorem and injective-preservation clause. Its statement does not explicitly state degree-zero normalization; I therefore wrote out the identity-of-section-complexes argument using its injective-preservation clause and the existing exact-restriction statement. No new node is needed for this elementary calculation.

## Unfinished work

None in this stage-1 split. This delivery writes no Lean and runs no compiler or build.

## Searches and reuse

I searched the full DAG for Tags 03FD and 03F3, their labels, localization/injective restriction, and module/abelian evaluation. I read the matching statements rather than relying on their titles. Blueprint searches with `tools/blueprint_refs.py` covered `cohomology modules abelian`, `03F3`, `03FD`, `cohomology on its localized site`, and `derived evaluation slice`; none states the complete item. The 03FD hit sk-def-pbc-conventions is a coefficient convention, not this comparison theorem. The ancestor command returned sk-prop-sf-comparison. No nodes were created.

Six fresh Mathlib queries ran through the mandated msearch command and their exact queries/results are recorded alongside the inherited records. The first Loogle query had an unknown identifier and is recorded as invalid, followed by a valid retry. All services answered. I inspected the hits: SheafOfModules.evaluation and its limit-preservation instances are underived; SheafOfModules.over is underived restriction; Sheaf.H and cohomologyPresheaf are Ext-based definitions. Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean lines 32–36 explicitly lists the localized cohomology comparison as TODO. No hit gives the module-to-abelian-slice derived comparison, including after the second semantic phrasing.

## Not duplicates

No new-node/existing-node pairs: this delivery creates no nodes. The item's extra slice identification is obtained by composing the existing module/abelian object-evaluation comparison with abelian localization, rather than by inventing another node for either fact.

## Review by Q26

I read Stacks `sites-cohomology.tex` Tag 03FD, label lemma-cohomology-modules-abelian-agree, both displayed equalities and its proof (around lines 1862–1921). This explicitly compares module and underlying abelian cohomology over every object. The proof uses injective module sheaves only to obtain abelian evaluation acyclicity, not abelian injectivity; this is precisely why no flatness assumption belongs in the item. I checked the existing comparison node's full statement and the RingCat-valued Lean signature at line 207: neither requires commutativity. I also read Tag 03F3, label lemma-cohomology-of-open, parts (1)–(2) and the full proof (around lines 608–642), and `sites-modules.tex` Definition 04IX and Lemmas 03DI–03DJ for localization and exact extension by zero. All statements needed are existing DAG nodes.

Step 1 uses exactly the statement of lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison: instantiate its U by W and retain its canonical additive natural isomorphism and its normalized degree-zero clause. Smallness and the common coefficient universe agree verbatim; the assumed enough injectives is exactly its hypothesis. No assumption on the ring is strengthened.

Step 2 uses def-weil-pbc-sites-and-cohomology for the abelian category with enough injectives and resolution computation, and def-sp-injective-resolutions for what an injective resolution is. The statement of lem-weil-pbc-site-restriction-injectives explicitly says restriction to the slice is exact; the statement of lem-weil-pbc-cohomology-over-object-localization explicitly says it preserves injective abelian sheaves. Applying those two facts termwise proves that the augmented abelian resolution restricts to an injective resolution. No module injective is forgotten in this step. This is elementary once the two substantive theorems are cited.

Step 3 uses def-pur-localized-ringed-site for literal sectionwise restriction of abelian sheaves and morphisms. The structure arrow proves terminality of id_W directly. The statement of def-weil-pbc-sites-and-cohomology explicitly defines cohomology by evaluated resolutions, specifies its canonical independence via resolution comparison maps, and identifies H0 with evaluation. Thus the two evaluated complexes, differentials, augmentations, and evaluated comparison maps are identical. This proves the additive isomorphism, independence and naturality, and shows directly that the degree-zero map is the identity. This is a calculation from cited statements, not an invocation of a cited node's proof. The four proof steps have respectively 516, 659, approximately 950, and 562 characters, all below 2000; none hides a new lemma.

Step 4 composes the two isomorphisms constructed in earlier steps. Pasting their naturality squares gives the claimed naturality in the module. Their normalized degree-zero maps compose to the identity. This uses only earlier steps, so its uses list is empty and it is marked elementary.

I checked delivery-errors B through E against these files. New-node shape/search/duplicate faults are avoided by creating no new node. Every cited theorem was opened and its actual statement provides the fact used (C4); every non-elementary input is named, including exact restriction separately from preservation of injectives (C1). There is no appeal to the proof of a node, no statement-only replacement for the item, no unmentioned change of coefficient category, and no SGA source. The generic off-unit coefficient and restriction lemmas are declared in split_report.tool_uses; they support the existing unit route instead of replacing it. The citations file is checked against the actual statements.

Small cases: M=0 gives zero groups and the unique identity comparison. On the one-object point site all positive derived evaluations vanish and degree zero is ordinary evaluation. With O=F_p and M=F_p on this site, M is injective as an O-module but its underlying group is not injective in Ab; the proof is still valid and does not make that false assertion. With O=M_2(F_p), the same proof uses left modules and never permutes scalars, so commutativity is not implicit. With the zero ring only the zero module occurs. The original site need not have a final object: only the slice does, by the explicit structure-arrow argument. An empty site has no W, so the quantified assertion is vacuous. A slice of the small site remains small in the stated universe, so there is no new size hypothesis.
