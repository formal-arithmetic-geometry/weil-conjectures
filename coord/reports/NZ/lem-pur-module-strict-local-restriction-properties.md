# Stage-1 report: lem-pur-module-strict-local-restriction-properties

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-module-strict-local-restriction-properties.json — statement, split; all three clauses proved in five steps. The complete item is not a Mathlib leaf. Mathlib does provide the generic point-fibre finite-limit instance, already represented by the existing exact-stalk node.
- citations.json — one entry for every step/node citation, copied verbatim from the current node statement.
- report.md — this report. searches.jsonl is the unedited msearch log. prepare.py is sandbox-only preparation material, not a delivery node.

No new DAG nodes and no new Mathlib leaves. No Lean files written, compiler invoked, repository writes or direct git commands.

## Attachments

None. I searched lean/WeilConjectures for the full blueprint tag, moduleStrictLocalRestriction, moduleStrictLocalSectionRestriction and the strict-local notions. The only recorded exact item declaration is AlgebraicGeometry.Etale.moduleStrictLocalRestriction_properties in lean/Sheaf/AlgebraicGeometry/ModuleStrictLocalRestrictionProperties.lean; its proof is sorry. It is not an attachment. I read that signature and the actual section-restriction definition in ModuleStrictLocalSectionRestriction.lean. They agree with this item's three clauses and small model.

## WANTED

None.

## Repairs and source route

The imported one-step proof silently changed coefficients: its stalk-exactness and strict-local-sections citations state assertions about abelian sheaves, while this item concerns A-module-valued sheaves. It also compressed the representative cocone and naturality into a sentence. I retained the statement, statement dependency, source, blueprint provenance, Lean record, import flags and earlier review metadata. The earlier review belongs to a stage-2 interface delivery, not a completed stage-1 proof. Only the stage-1 proof and its search/provenance/report fields are changed.

The replacement explicitly equips abelian colimits and limits with their scalar actions, applies the existing module-sheaf forgetting-colimits statement before the exact abelian sections theorem, writes the transition cocone equation, and proves naturality by precomposing with all germs. The old independent affine-cofinal citation is redundant: def-weil-pbc-small-strict-local-section-cone already supplies initiality for exactly the chosen small representative functor as well as the geometric section compatibility needed here.

I read the chapter and unit records. This is a tool underneath Step 2 of the latest prop-pur-gm-relative-kummer proof: canonical restriction to the strict localization, compatible with classes. It does not replace the unit's smooth-base-change and Kummer computation route. No unit or chapter was changed. The three off-unit statement tools are explained in split_report.tool_uses: exact abelian stalks, scalar forgetting of sheaf colimits, and exact abelian sections on the actual chosen small scheme. Definition nodes supply notions and explicit cone data.

## Search record and duplicate audit

No earlier sandbox node, report or searches existed. I read and preserved the item's inherited searches and ran new msearch searches for the item itself: two distinct semantic phrasings, Loogle for finite-limit sheaf fibres, LeanSearch for geometric fibres and descent, and grep in CategoryTheory/Sites/Point. All five calls succeeded and their exact queries and results were appended from searches.jsonl. The semantic results were predominantly Zariski module-stalk declarations; these are not this small-etale theorem. Loogle and LeanSearch returned the actual generic Point.Basic sheaf-fibre finite-limit instance; I read Basic.lean:274–291 and ModuleCat/AB.lean:27–35. This proves only the first clause, not the conjunction with strict-local sections and its specified restriction map. I reused the already existing exact-stalk node rather than introduce a leaf for a clause of this item.

I searched the whole DAG by strict-local sections, exactness, colimit/cocone universality, scalar forgetting, and the relevant Stacks tags. I read every cited node statement in full. Blueprint searches for strict local, stalk functor and finite limits found no equivalent whole item, and blueprint_refs ancestor confirmed prop-pur-gm-relative-kummer. No new node is created, so the same-tag new/existing-pair requirement is vacuous.

## Not duplicates

No new nodes.

## Review by NZ

I read the latest blueprint proof, Step 2, and the actual source passages in literature/stacks-project/etale-cohomology.tex: Tag 03Q9, theorem-higher-direct-images (the affine-neighbourhood replacement, strict-local limit and restriction maps), and Tag 03QO, lemma-vanishing-etale-cohomology-strictly-henselian (exact global sections). I checked their labels against tags/tags. I also read sites-modules.tex, Tag 03CO, lemma-limits-colimits-abelian-sheaves, and Tag 03CY, lemma-sheafification-presheaf-modules, together with the subsequent module limit/colimit construction. These explain the scalar-forgetting tool. The scalar universal-property assembly is written by this agent, so proof_origin is agent, not a claim that the blueprint already contains these details.

For step 1, def-weil-pbc-category-colimit supplies precisely the unique factorization against all legs, not an unproved assertion that forgetting creates colimits. I use that factorization to construct each scalar endomorphism and prove its laws by testing all legs. The dual argument makes the limit maps linear. Sectionwise limits remain sheaves because a matching family glues in every coordinate; the relations and scalar laws follow by projections. The other citation, def-weil-pbc-geometric-stalks, explicitly defines the stalk as the neighbourhood colimit. Thus its scalar action and its underlying additive germ maps are those constructed here. This is a universal-property calculation from the cited definitions, not a separate new lemma node.

For step 2, prop-weil-pbc-geometric-stalks-exact explicitly says the abelian stalk is exact. I use only its finite-limit consequence and step 1 to identify the underlying module comparisons. The inverse of a bijective linear map is linear by applying the map to the scalar identity. No Zariski module-stalk theorem is applied to an etale stalk.

For step 3, lem-pbc-u2-module-sheaf-underlying-preserves-colimit states preservation of every small diagram of constant-coefficient module sheaves on the small etale site. A finite diagram satisfies its size hypothesis. lem-weil-pbc-strict-henselization-scheme-sections-exact explicitly concerns Spec(strictHenselizationRing(s)), not a different strict localization. Its algebraically closed point hypothesis is in the item. Applying the two stated preservation results gives the abelian colimit of global sections; the scalar construction in step 1 gives the module universal property. The section-restriction definition is cited for the actual coefficient/global-sections model. No geometric comparison of two different colimit models, no qcqs assumption on B and no exactness inferred merely from a definition of flatness occur.

For step 4, def-weil-pbc-small-strict-local-section-cone explicitly gives the initial small representative functor and compatible sections for the actual small-colimit scheme. I use those assertions, not its abelian descent conclusion, and not an unstated part of its proof. The restriction definition says to take the adjunction unit followed by restriction and the terminal comparison. I checked the direction: for t:V_i -> V_j, F(t):F(V_j)->F(V_i) and (t times S) sigma_i=sigma_j, giving d_i F(t)=d_j. Thus the displayed maps are a genuine module cocone. The colimit definition gives the linear r_F and its component equations. The stalk definition identifies its source. Every dependency's statement is copied in citations.json, so there is no unsupported C4 interpretation.

For step 5, I checked naturality of each of the three factors in the definition against a sheaf morphism alpha. The two composites on stalks have equal restrictions along every representative germ and are equal by the same universal property. Componentwise uniqueness then gives uniqueness as a natural transformation; no new natural-transformation descent theorem is hidden. The scalar calculation, cocone equation and naturality calculation together supply the missing argument rather than relocating the item's clauses into new nodes.

I checked delivery-errors B1–B10: self-contained original statement retained, its definition dependency introduces every object, TeX is singly escaped in new text, sources have actual tags/labels, searches are real and not reported unavailable when successful, no new leaves or duplicate/clause nodes, correct blueprint provenance, no false attachment. C1–C8: every non-elementary imported fact is a cited statement, there is no appeal to a definition for exactness, all citations were opened, and off-unit generic tools are declared. D1–D5: five actual arguments, no new restatement nodes, no circular induction or invocation of the item's conclusion. E1–E7: the only algebraically closed hypothesis is present; no finite type, noetherian, torsion or nonzero-ring assumption is added; both sides of every transition equation have the same scheme and coefficients; compatibility is calculated explicitly rather than called a transport. No source error or statement dispute was found.

Small cases checked: A=0 gives the zero module category; zero sheaf and zero maps give zero restrictions. Empty finite diagrams give the zero module as both terminal and initial object, so the exactness clauses include these. B cannot be empty when the specified geometric point exists, so there is no use of a nonexistent point in that case. For B the spectrum of an algebraically closed field the construction reduces to the ordinary germ/section restriction. Non-noetherian and disconnected B remain allowed because the sections theorem and representative cone are local at the given point. The same scalar-universal-property argument works in the carrier universe u+1 and uses only the specified small representative index in u. Each proof step is under 2000 characters (lengths 1189, 616, 857, 1227, 760); no long step hides an extracted comparison lemma.

The first server-side review_split check passed with 0 new nodes. Required deliver.py dry run and push are recorded by their own tool output.

## Unfinished work

None at stage 1. This delivery supplies a natural-language split; the existing Lean theorem remains sorry as required by the stage-1-only authorization.
