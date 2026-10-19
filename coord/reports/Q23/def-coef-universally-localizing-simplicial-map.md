# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-six-functors/def-coef-universally-localizing-simplicial-map.json`: existing definition node, marked split; statement and dependency unchanged; no new nodes.

2. Attachments: none. I searched the read-only `WeilConjectures/` source for the blueprint id and for the notions of universal localization and simplicial maps. No project declaration states this definition, and no declaration is available to attach.

3. WANTED: archival Kerodon Definition 6.3.5.1 (02M0) and Proposition 6.3.1.13 (01MS), read online on 2026-10-17; the node records the source URLs and explains that Kerodon tags are not Stacks tags. No Stacks source is being substituted.

4. What was checked: this is a definition, so its proof and proof-dependency lists are correctly empty. The definition explicitly says that for every base change `T → B` there is a collection of edges in `T ×_B A` whose localization universal property works for every quasicategory target, with the edge collection allowed to depend on the base change. The statement adds no Kan, quasicategory, finiteness, or colimit hypothesis on the simplicial-set inputs. The existing statement dependency `def-cbc-enhanced-diagrams-cones` supplies the meanings of the simplicial and functor-category notions it invokes. I searched the DAG and blueprint for duplicates and found no node stating this definition; the two existing universal-localization helper nodes cite this definition and are distinct consequences, not duplicates. I also checked the source against the no-attachment rule by grepping the project Lean source for the item id and key terms; no exact declaration was found. The existing recorded Mathlib searches were retained and their results are not a match: they concern ordinary category/ring localization or simplicial primitives rather than this universal simplicial localization definition.

5. Nothing remains unfinished at this one-level split. No Lean file, compiler, Lake, build, live-project file, or git command was used.

## Review by Q23

I read the current item node, the chapter `sec-six-functors`, the unit `sk-prop-sf-biduality-general`, and the cited dependency node. I read Kerodon 02M0 and 01MS and compared each clause: the pullback is degreewise over an arbitrary small map, the localizing edge collection may depend on that map, and the universal property quantifies over every quasicategory target and retains the full coherent functor equivalence. The statement's `stmt_deps` names exactly the existing node that supplies its ambient simplicial/functor-category conventions. I checked that no proof step or hidden lemma is present because this node is a definition, and that no new node would be anything other than a restatement of the definition. I checked the read-only Lean source for a sorry-free or otherwise exact project declaration and found none. I retained the existing source, blueprint ancestry, search records, and statement unchanged, changing only the status and split report required for this stage.

## Second reading by Q23

- Item statement: checked every clause against Kerodon Definition 6.3.5.1 (02M0) and Proposition 6.3.1.13(2) (01MS); the arbitrary simplicial base change, per-base-change edge collection, all-quasicategory quantifier, and functor-equivalence conclusion agree.
- Proof: there are no proof steps because this is a definition; the empty and identity simplicial-set cases are well-typed and impose no hidden Kan or finiteness hypothesis.
- New nodes: none are introduced by this split, so B1–B7 and new-node duplicate/Mathlib checks are vacuous; the sole `stmt_deps` node was opened and supplies the stated simplicial, quasicategory, functor, full-subcategory, and equivalence notions.
- Source and ancestry: the Kerodon tags and the blueprint `from`/`same_as` fields were checked; the existing node's historical `created` metadata is preserved because this delivery changes an existing node rather than creating one.
- Changes: none. The status/split report already present in the packet is sufficient, and no statement, dependency, citation, or search record required repair.
