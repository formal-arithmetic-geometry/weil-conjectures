## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-standard-fppf-cover-limit-descent.json` (statement, split; Mathlib searches found no exact covering-descent theorem). `citations.json` contains one verbatim statement quotation for every step citation. The original statement, source, metadata and earlier searches were retained. The five current searches and full outputs are recorded separately and appended to the item.

Attachments: none. Searching `lean/WeilConjectures` for the exact blueprint tag, standard fppf, and fppf limit/descent produced no matching declaration. The Hilbert-scheme file mentions fppf descent, but does not state this result.

WANTED: none.

No statement dispute or source error was found. The imported statement's finite presentation condition agrees with Tag 021Q: over affines local finite presentation suffices because an affine morphism is quasi-compact and quasi-separated. Joint surjectivity is a separate condition; flatness alone never supplies it. Tag 049N proves eventual covering via images and descent of opens; the existing general finite-family Tag 07RR lemma supplies exactly that remaining conclusion without reconstructing its proof or creating another node.

Nothing remains mathematically unfinished at this split level. The cited existing unsplit dependencies, if any, remain the maintainer's queue work. No Lean was written or compiled.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing finite-presentation descent, affine descent, flatness descent, joint-surjectivity descent and permanence statements already give every required input. None is a newly named clause of this item.

## Not duplicates

No new node is proposed. Whole-DAG title/statement/source searches for 01ZM, 01ZN, 04AI, 049N and descent/finite presentation/flatness/surjectivity found the nodes cited in the proof. Whole-blueprint searches with `tools/blueprint_refs.py search '049N'`, `'fppf covering'`, and `'flat limit'` found no existing blueprint statement of the item: the fppf hits are definitions, a Picard sheaf and Zariski-to-fppf covering comparison. The existing finite-family joint-surjectivity statement is stronger than the needed covering condition, so it is reused. No duplicate approximation lemma was created.

## Blueprint and route

Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), and the chapter/unit records. This item's long inherited provenance places it in the stack limit-preservation prerequisite of the alteration/moduli input. `blueprint_refs.py ancestor lem-sfb-standard-fppf-cover-limit-descent` reports `None`; the current live `blueprint.from.node` is already null. I retained that metadata and its exact place rather than invent an imported ancestor. `same_as=[]` records the negative search. Generic approximation inputs from other units are declared, with reasons, in `split_report.tool_uses`; no maintainer-owned top-level `tool_uses` was written.

## Review by O1

I read topologies.tex Tag 049N (`lemma-limit-fppf-topology`), including the complete fppf proof, and Tag 021Q (`definition-standard-fppf`). I also read limits.tex Tag 01ZM (`lemma-descend-finite-presentation`), Tag 01ZN (`lemma-descend-affine-finite-presentation`), Tag 04AI (`lemma-descend-flat-finite-presentation`), Situation 081D and Tag 07RR (`lemma-descend-surjective`). The base-change facts used in assembling the family agree with morphisms.tex `lemma-base-change-flat` (01U9) and `lemma-base-change-finite-presentation` (01TS). There are no new-node sources to audit.

Step 1 uses the full statements of `lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-affine-morphism-permanence`, and `lem-weil-pbc-cartesian-square-pasting`. The first gives qcqs affines, the second gives quasi-compactness/quasi-separatedness of affine maps, and the third supplies precisely the iterated base-change comparison. Affine transitions and the original affine covering maps are already explicit in the item's statement. Finite presentation is local finite presentation plus these two finiteness conditions; no Noetherian hypothesis is used.

Step 2 uses `lem-weil-pbc-finite-presentation-family-descent`, whose statement gives simultaneous finite-presentation qcqs models and cartesian squares, including empty families. It is not an etale-only statement. `lem-weil-pbc-qcqs-morphism-permanence` clause (3) gives finite presentation after further base changes, while clause (2) supplies qcqs sources over qcqs bases. The target model in the later covering lemma is the base itself; its identity has a presentation with no variables or relations.

Step 3 reads and applies exactly the statements of `lem-weil-pbc-descend-affine` and `lem-weil-pbc-descend-flat-finite-presentation`. Their stage-zero source is the qcqs model of step 2, the target and base are the affine stage, and the limit arrows are the original affine flat maps. The flatness lemma requires local finite presentation, which the models have. A finite common upper bound exists by directedness; persistence follows from `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-flat-morphism-base-change` and `lem-weil-pbc-qcqs-morphism-permanence`. In particular, affine source at the final stage follows from affine morphism plus affine target, not from a pointwise image condition.

Step 4 uses only the stated conclusion of `lem-weil-pbc-finite-family-joint-surjectivity-stage`: finitely presented sources and target over a fixed stage, locally finitely presented arrows, and joint surjectivity after limit pullback give joint surjectivity at a later stage. All these hypotheses were established in steps 1--3. I checked its finite index set is not required to be nonempty. Its all-later-stages conclusion is stronger than needed. No appeal is made to its proof or to etaleness.

Step 5 again uses the exact affine/flat/qcqs base-change conclusions and cartesian-square pasting. Each original label is retained; there is no refinement or replacement by an unrelated cover. The component isomorphisms are over the limit T and hence over S. This is exactly the family isomorphism demanded by the item.

For the small cases I checked m=0 (the joint-surjectivity lemma forces an empty final base), a singleton identity covering, a constant inverse system, nonempty indexing with empty stages, and an empty covering member among nonempty members. Nothing in the proof assumes positive m, a nonzero coordinate ring, a surjective transition, a Noetherian base, or that S is affine. Arbitrary S causes no problem: all constructions are over T_i, and composing with its structural map to S gives the required S-structure.

Against delivery-errors B--E: all cited nodes were opened and every step's use is in its statement; full verbatim quotations are in citations.json. The only finite common-bound and definition-unpacking arguments are elementary inside explicitly cited theorem applications. There is no new node, no copied clause, no hidden standard comparison, no use of a definition as a theorem, and no new assertion needing missing hypotheses. I checked dependency reachability: none of the proposed proof dependencies reaches this item. All five steps are below 2000 characters; their combined proof text is 2835 characters. The current search results show affine-limit section/open-cover facts, fppf topology definitions, and fpqc descent of properties, all different from this finite-stage covering theorem. I retained the earlier search records instead of replacing their historical results. The main correction during preparation was to use the scheme-level qcqs permanence statement for finite-presentation base change, rather than cite a ring-only tensor-product statement for that scheme assertion.
