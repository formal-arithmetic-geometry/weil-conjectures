## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-nodal-etale-postcomposition.json` (item, statement, split; no Mathlib match), `citations.json`, and this report. `searches.jsonl` is the unmodified output of the required search command.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The existing DAG supplies the ingredients, including the unramified-over-a-field decomposition, which is more general than the geometric étale decomposition needed here.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact blueprint tag, nodal, ordinary-node and étale/nodal combinations. The only nodal occurrences are explanatory examples or counterexamples, with no declaration of the claimed permanence result. No Lean file was written and no compiler was run.

## Literature wanted

None.

## Corrections and scope

No statement correction. Stacks curves.tex Tag 0CD8 (lemma-nodal-family-postcompose-etale) states the forward implication. Its first paragraph supplies the structural-properties route, and its second paragraph compares singularities over separable extensions. I use its geometric-fibre version: split the étale target over an algebraically closed field, then identify the resulting clopen source fibres. The reverse implication uses the open graph, as the item's source already specifies, and the same fibre argument. I did not create a node for either implication or an elementary clopen-union observation.

The existing blueprint ancestry ends with `from.node = null`; `blueprint_refs.py ancestor` reports exactly that, rather than an imported ancestor id. I preserve that field and its detailed `from.place` and `via` chain. I read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md: direct-image paragraph (3) is the upstream ancestor named by the existing place. The immediate parent's nodal-chart comparison is the purpose of this item; no chapter or unit route was changed. Whole-blueprint searches for nodal, postcomposition, 02G7, flat and finite presentation yielded no duplicate of this item. DAG searches by nodal, graph, flatness, finite presentation and the Stacks places found the reusable facts cited here.

Mathlib searches made through msearch.py are recorded with their exact query text and output summaries. The two LeanFinder phrasings produce étale or smooth permanence results, not ordinary-node families. Loogle has no nodal hit and the Mathlib AlgebraicGeometry source has no nodal declaration. I read Etale.lean:35-157, Flat.lean:38-99 and FinitePresentation.lean:42-106. Generic permanence is present; the entire item is not a one-line specialization of it. The older search records already in the item were preserved.

## Not duplicates

No new nodes, so there are no new/existing node pairs to distinguish. In particular I reused lem-trf-unramified-field-fibre-decomposition (Tag 02G7) rather than creating an algebraically closed special case, lem-weil-pbc-flat-ring-map-comp rather than creating flat scheme composition, and lem-weil-pbc-finite-presentation-base-change-composition rather than creating finite-presentation scheme composition.

## Tool uses

`lem-trf-unramified-field-fibre-decomposition` is a generic field-scheme tool from the trace-formula unit. Its statement gives precisely the arbitrary disjoint union of finite separable spectra used in step 2. This has no dependence on nodality or this item; it replaces no unit step. It is declared in split_report.tool_uses for maintainer review. The remaining off-unit statement tools are existing Mathlib leaves.

## Review by Q87

I read curves.tex's definition-nodal-family (0C5A), lemma-nodal-family, lemma-base-change-nodal-family (0C5B), and the complete statement and proof of lemma-nodal-family-postcompose-etale (0CD8). These impose neither properness nor quasi-compactness, so the statement's absence of those assumptions is correct. I also read morphisms.tex lemma-unramified-over-field (02G7), the composition and base-change finite-presentation lemmas (01TR and 01TS), and composition/base-change flatness (01U7 and 01U9), plus algebra.tex lemma-composition-flat (00HC). No SGA source was used.

For step 1 I opened the statements of def-weil-etale-morphism, def-weil-flat-morphism, def-sbc-locally-finite-presentation, lem-weil-pbc-flat-ring-map-comp and lem-weil-pbc-finite-presentation-base-change-composition. The étale definition supplies flatness and local finite presentation. The flatness lemma is only a ring statement: the proof explicitly applies it to the two local-ring maps at each c. The finite-presentation lemma is also a ring statement: the proof gives the combined presentation, explains the finite lifts of coefficients, and works on successively chosen affine neighbourhoods, with principal shrinking encoded by one inverse variable. It does not misquote either ring lemma as a scheme theorem.

For step 2 I opened def-pc-fibre-product, def-weil-algebraic-closure, def-weil-etale-morphism, lem-weil-pbc-etale-base-change-finite-limits and lem-trf-unramified-field-fibre-decomposition. Clause (1) of the base-change node really gives T_s étale over Spec Omega; the definition makes it unramified. The field lemma is applied over Omega itself, not over kappa(s), so every finite separable extension is Omega. The polynomial argument proving that assertion is written out. The index set may be arbitrary and empty: no finite-cover assumption is inserted.

For step 3 I opened def-pc-fibre-product, def-weil-open-immersion, def-weil-pure-dimension and def-sbc-smooth-morphisms. The inverse images of the target clopen pieces partition C_s, and the universal-property projection formulas identify each with the g-fibre at its geometric lift. These are actual scheme isomorphisms over Omega, not identifications inferred from point sets. The elementary component argument is explicit: an irreducible component cannot cross the disjoint open partition, and being closed in a closed piece agrees with being closed in the full scheme. Local rings and their completions are unchanged on the open piece, and smoothness at a point is checked on an open neighbourhood. Thus neither pure dimension nor closedness of the node gets lost. This step uses previously established decomposition; it is marked elementary only for this assembly.

For step 4 I opened every cited statement: the fibre-product definition, the étale and unramified definitions, flat-morphism base change, qcqs-morphism permanence clause (3), open-immersion base change, étale composition/cancellation clause (1), and both ring-composition lemmas. The qcqs lemma's clause (3) has no qcqs hypotheses; I do not use its earlier qcqs clauses. The unramified definition explicitly says the diagonal is open. I write the map P -> T x_S T and its pullback relation g(c)=t, so the graph follows from a cartesian square and 01JY, without assuming e separated. Étale open immersions are flat and locally finitely presented by the cited definition. Applying the explicit structural composition argument of step 1 then gives both properties of g. No full nodal-base-change theorem or open-restriction theorem is silently used.

For step 5 I reopened its four cited definitions. It uses the earlier established target splitting for the geometric point e(t); the chosen lift t selects exactly one Omega-point piece because its Omega-structure map is the identity. Its inverse image in C_s is exactly C_t, so its fibre condition follows by the clopen argument already proved in step 3. This checks all geometric points of T, with no lifting or surjectivity requirement on e. The algebraic closure Omega here is any algebraically closed field, not a fixed algebraic closure of a residue field.

For B1-B10/C1-C8/D1-D5/E1-E7 I checked self-contained statements, verbatim citations, correct source tags, route, hypotheses and absence of cycles through the generic tools. No new statement-only node contains a hidden proof because none was added. Each proof step is below 2000 characters. The citations file includes every one of the 27 uses, copied verbatim from the actual cited statement. There is no appeal to a cited node's internal proof. The only substantive correction made during preparation was to avoid the tempting global nodal-base-change lemma entirely: it would introduce unnecessary geometric-field-extension invariance. Here all fibre comparisons are over the identical field Omega.

Small cases checked: C empty (all properties vacuous), T empty (forces C empty), e a non-surjective open immersion (fibres outside its image are empty), e a disjoint union of arbitrarily many identity copies (no hidden finite index), a smooth affine line, the split node Spec Omega[u,v]/(uv), and a non-separated étale target (only its open diagonal is needed, not a closed graph). Empty clopen pieces remain allowed and a chosen lift always selects a nonempty target piece. No unfinished mathematical clause remains.

## Validation

Server review_split passed on 2026-10-23: zero new nodes, generic field-scheme tool use declared. The required deliver.py --no-push invocation exited 0 and printed OK (not pushed), preflight passed, at d297e7977cb. It ran the maintainer preflight, including DAG and split checks, on the server. No local check_dag.py, review_split.py or preflight_delivery.py was run. The only notice is that the inherited unit has no realization recorded yet; this item is not its key statement and does not edit the unit.
