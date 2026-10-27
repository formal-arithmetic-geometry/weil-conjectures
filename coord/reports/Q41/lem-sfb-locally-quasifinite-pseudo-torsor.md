# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-locally-quasifinite-pseudo-torsor.json`: statement; split into four steps. The statement and its statement dependencies are unchanged. Mathlib verdict: no match for this algebraic-space pseudo-torsor result.
- `citations.json`: seven entries, one for every step/node citation, checked as verbatim substrings of the live cited statements.
- `searches.jsonl`: five fresh searches through the prescribed msearch.py command, in addition to retaining all imported Mathlib search records in the item.

There are **0 new nodes and 0 Mathlib leaves**.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, pseudo-torsor spellings and torsor/quasi-finite notions found no project declaration with the exact statement. Existing scheme quasi-finiteness and finite constant sheaf torsor results have different domains and do not attach this item.

## WANTED

None. All mathematical inputs are in the local Stacks source and the live DAG.

## Audit of the imported material

The imported statement agrees with Stacks spaces-groupoids.tex, Tag 0DSK (`lemma-pseudo-torsor-implications`), part (2), and its pseudo-torsor convention agrees with Tag 04TW (`definition-pseudo-torsor`). In particular a pseudo-torsor need not be surjective, and no finiteness of its entire fibre set is asserted. There is no statement dispute or correction.

The imported item had no proof. The four steps fill it using the source's field-base-change route, not a flatness or torsor-cover descent argument: a representative of an individual point supplies the field extension and section needed in the source. Pulling back the pseudo-torsor isomorphism along the pair consisting of a variable point and that section proves the trivialization directly. This is an elementary fibre-product calculation, not a new lemma node.

The existing nodes `lem-sfb-space-quasifinite-locus-open` (04NW, scheme target) and `lem-sfb-representable-lqf-calculus-descent` (03XL, base change) already provide the non-elementary quasi-finiteness inputs. I also read `lem-sfb-space-discrete-fibres-locally-quasifinite`, `lem-sfb-space-field-discreteness-criterion`, `lem-sfb-space-field-extension-dimension`, and `lem-sfb-space-finite-fibre-quasifinite-criterion`; their discrete-fibre, separatedness or finite-type formulations are unnecessary here. None was copied into a new node. DAG and whole-blueprint searches for pseudo-torsors, quasi-finiteness and the quasi-finite locus found no blueprint node stating the item. The sibling `lem-sfb-unramified-pseudo-torsor` is part (1) of 0DSK and does not give part (2).

I read the chapter and unit records, then the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially enclosing proof (3). The item's inherited place records the inertia-criterion prerequisite below that route. `tools/blueprint_refs.py ancestor` reports a null ancestor for this already-created item; its inherited from.node and via chain are retained. No chapter or unit route was changed.

## Mathlib search results

The five searches in this sandbox's log are: LeanFinder on the local-quasi-finite pseudo-torsor statement; LeanSearch on a second phrasing; Loogle on `"PseudoTorsor", "LocallyQuasiFinite"`; grep on `pseudo.?torsor|AlgebraicSpace|algebraic space`; and LeanFinder on a simply transitive action phrasing. Every service returned a result successfully. Loogle and grep returned no hits. Semantic hits included scheme `AlgebraicGeometry.LocallyQuasiFinite`, its scheme base-change/composition API and finite-morphism instances, plus abstract group-action and topological quotient results. I read `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`, lines 43–120: its variables are schemes and its class is a scheme morphism property, so it is not the algebraic-space assertion and does not specialize to it in one line. The actual queries, returned declaration names and verdicts are recorded without inventing searches or converting an unavailable service into a negative answer.

## Tool use

Step 2 cites the off-unit foundational `lem-trf-space-fibre-products-etale-covers` only for existence and the categorical universal property of algebraic-space sheaf fibre products. This is declared in split_report.tool_uses. The two quasi-finiteness statements are already in the item's own unit. Definitions are used as definitions.

## Review by Q41

I read the statement and both proof paragraphs of 0DSK, the definition 04TW, the complete statement and proof of spaces-morphisms.tex 0ABM (`lemma-base-change-quasi-finite-locus`), and the statement of 04NW (`lemma-locally-finite-type-quasi-finite-part`). The source explicitly makes the quasi-finite locus commute with arbitrary base change and reduces (2) to a field where a section identifies the pseudo-torsor with its group. Step 2 gives the omitted section-trivialization calculation rather than quoting the omitted proof of 04TX. There are no new-node sources to audit.

For Step 1 I opened `lem-sfb-space-quasifinite-locus-open` and read its statement, not just its title. It requires an algebraic space with a scheme target and local finite type, and gives the base-change equality for every scheme morphism to that target. Taking an arbitrary etale scheme chart V of B gives precisely such a target, and the item's chartwise local finite type assumption gives the local finite type of X times_B V over V. Thus this citation says exactly what Step 1 uses; it is not being applied to the original possibly nonschematic B.

For Step 2 I opened `def-a1-algebraic-space-point-classes` and `lem-trf-space-fibre-products-etale-covers`. The definition gives field-valued representatives for every point class; the theorem constructs the sheaf fibre products as algebraic spaces and gives their categorical universal property. The chosen representative x gives a section of the pullback P, and the point of P represented by that section maps to the original class z. Pulling back the given isomorphism theta preserves its inverse simply by pulling back both inverse identities. Its further pullback along y maps to (y,x_K) has source H because the second coordinate is forced to be x_K. The displayed inverse first projects theta_K inverse(y,x_K); both composites are identities. This is a calculation from the cited fibre-product statement and the item's given isomorphism, marked elementary; it does not assume the existence of a rational point over an unchanged residue field or surjectivity of X over B.

For Step 3 I opened `lem-sfb-representable-lqf-calculus-descent`: its statement explicitly preserves local quasi-finiteness under arbitrary base change. Applied to G over B and Spec K over B this gives H over K. An algebraic-space map is representable in the sense this node uses because its scheme base changes are algebraic spaces. I also opened `def-trf-algebraic-space`: its representable-etale convention is by scheme tests. Consequently composing any etale chart of P with the inverse isomorphism to H gives an etale chart of H with identical composite to Spec K. This proves the chartwise property of P without an uncited descent theorem or an unexplained transport.

For Step 4 I reread the base-change clause of `lem-sfb-space-quasifinite-locus-open` and the statement of `pqf-def-quasifinite`. The target V and Spec K are both schemes, so the former applies even though Spec K need not be etale, flat of finite presentation or surjective over V. The section point z_K belongs to the entire quasi-finite locus of P, so its image z belongs to Q_h by the literal inverse-image equality. Every z having this property says Q_h is all of F; the cited definition makes every source-chart morphism locally quasi-finite. Quantifying over all target charts is exactly the item's conclusion.

I tested the argument on the empty pseudo-torsor (all point assertions are vacuous), on the trivial pseudo-torsor X=G including an infinite disjoint union of locally finite type zero-dimensional pieces (no quasi-compactness or finite total fibre assertion is used), and on a nonreduced finite group in positive characteristic acting on itself (the proof uses quasi-finiteness, never unramifiedness or reducedness). The method allows residue-field extensions and does not assume the torsor has a point over the original field. Local finite type of X is used exactly at the quasi-finite-locus theorem; that of G remains in the unchanged statement, and its local quasi-finiteness supplies the base-change property. No separatedness is used.

I checked the proposed proof dependencies have no path back to this item, so the reuse introduces no cycle. Every citation quote was checked against the current statement. Each step is under 2000 characters (400, 935, 551 and 619 characters), and there is no hidden non-elementary intermediate comparison. Checking B–E required no statement repair and no new nodes: the substantive correction to the empty imported proof is the explicit trivialization and the carefully restricted scheme-target use of the locus theorem. No Lean was written and no compiler or build tool was run.

## Unfinished work

None in this one-level stage-1 split. The reused unsplit inputs remain their own DAG items; this delivery does not claim their Lean proofs are finished.
