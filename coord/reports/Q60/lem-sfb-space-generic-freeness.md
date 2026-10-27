# Stage-1 report: lem-sfb-space-generic-freeness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-generic-freeness.json — item split into four steps, reusing existing DAG nodes; no Mathlib match for the algebraic-space statement.
- citations.json — seven verbatim statement excerpts, one for every step/node citation.
- report.md — this report. Searches are logged in searches.jsonl; write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project under lean/WeilConjectures for the exact blueprint tag and generic freeness/flatness terms. The finished scheme declaration AlgebraicGeometry.Scheme.Modules.exists_generic_free_neighbourhood in AlgebraicGeometry/CoherentIntegralGenericFreeNeighbourhood.lean:49 gives a morphism invertible at the generic stalk, not an isomorphism on an open of an algebraic space. It is not an attachment for this item. Its existing DAG node was read, not duplicated.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## What was wrong or changed

The item was statement-only and had no proof. Its statement is mathematically sound as written. Normalized imported doubled TeX backslashes to single TeX backslashes; no hypothesis or conclusion changed. In particular nonemptiness, reducedness, irreducibility, Noetherianity, full support, and strictly positive finite rank all remain.

The inherited blueprint ancestry chain has from.node null. tools/blueprint_refs.py ancestor lem-sfb-space-generic-freeness itself returns None. I retained this inherited value and the precise existing from.place and via chain; no invented ancestor was substituted. The current latest blueprint unit and direct-images proof were read. This is a prerequisite far below that unit's direct-image step, and the proof continues the stated Tag 07UQ route.

The nearest generic-free-neighbourhood theorem states only stalkwise invertibility. I did not treat it as an open trivialization: instead the existing lem-pc-c3-coherent-generic-local-free-model states exactly the scheme local model needed. Its stronger generality (an integral closed subscheme and a generic annihilation hypothesis) is specialized by the identity closed immersion, after separately verifying that the generic local ring is a field.

## Not duplicates

No new nodes were created. Searched the entire DAG for schematic dense opens, generic free coherent modules, the local-isomorphism result and the change-of-site equivalence, including Tags 06NH, 01YE, 01Y3, 03LZ, 03OF and 03OG. Used blueprint_refs searches for generic freeness, generic, schematic, 06NH and 01YE. These searches gave existing inputs rather than a new lemma. No imported blueprint statement was found that states this algebraic-space conclusion.

## Searches

Read the item's five inherited search results and ran fresh logged leanfinder, loogle, grep and leansearch searches under Q60. A second leanfinder phrasing searched generic trivialization on a dense open. The hits provide scheme integrality, free loci for modules over rings, and abstract sheaf finite-presentation facts; none is an algebraic-space generic trivialization. The item retains the inherited records and appends only the exact new logged queries/results. No unavailable service was recorded as a negative result.

## Review by Q60

I read Stacks spaces-cohomology.tex Tag 07UQ, lemma-prepare-filter-irreducible, especially its second proof paragraph. It first uses a dense open scheme and then shrinks to a free coherent module, citing coherent.tex Tag 01YE. I read the integral-case proof of 01YE through its local free model, spaces-properties.tex Tag 06NH (the dense open proposition), descent.tex Tag 03DX part (2), and morphisms.tex Tag 01RV (the generic stalk field). These are the item's sources; there are no new nodes needing separate sources. I also read the chapter/unit records, the three levels and tool-use rules in SETUP, and the current latest blueprint unit and direct-images proof.

For step 1 I opened lem-sfb-quasiseparated-space-dense-scheme-open: its statement assumes exactly the quasi-compact diagonal on scheme tests that the item's Noetherian convention supplies, and explicitly produces an open scheme with dense image. No finite-type hypothesis on the base is used. The item gives local Noetherianity and reducedness on every etale scheme chart, so it gives them on this open scheme. I use the actual definition in pqf-def-locnoeth to choose a nonempty member of a Noetherian affine cover, rather than silently assuming the dense scheme is quasi-compact. Irreducibility passes to a nonempty open by the two-open intersection argument written in the step. The equivalence in def-pc-integral-scheme then gives integrality. All three cited statements were opened and their relevant wording copied into citations.json.

For step 2 I opened lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. It says that restriction to Zariski opens is the inverse equivalence and states compatibility with scheme pullback. Thus the Zariski module G really represents the given etale module, including subsequent open restrictions. The coherence hypothesis is the item's explicit coherent-pullback condition applied to this etale scheme chart; it is not a purported conclusion extracted from a definition node. This also prevents confusing an arbitrary etale sheaf with a quasi-coherent module.

For step 3 I opened lem-sc-integral-function-field-affine-fraction and used its explicit conclusion that the generic stalk ring is a field. The maximal ideal is zero, hence annihilates any module. I opened lem-pc-c3-coherent-generic-local-free-model and checked every hypothesis: ambient Noetherian scheme V, integral closed subscheme Z=V, identity closed immersion, coherent module G, and the now-verified generic annihilation condition. Its conclusion is an isomorphism on an actual neighbourhood of the generic point, not merely a stalk isomorphism. Identity pushforward adds no content. Both cited statements are quoted verbatim.

For step 4 I use the same equivalence on the open U. The tensor pullback of a finite free module is computed by sending its finitely many basis vectors to the same standard basis; tensoring an inverse map gives the inverse. This is a routine application of the functor already stated in the cited node, not a hidden comparison theorem. Since U contains the generic point it is nonempty, and since it is open in V it is an open subspace of X. A zero-rank free module is zero on every etale object, hence has zero geometric stalk above a point of U; full support excludes this. This last argument requires no comparison of Zariski and geometric supports and no non-elementary faithful-flatness input.

I checked B through E of delivery-errors against these steps. There are no new statement-only records, no unstated hypotheses, no copied clauses posing as new lemmas, and no citations relying on a cited proof rather than its statement. Each non-elementary input is an existing node. The imported statement's TeX normalization is the sole textual statement edit. The elementary final assembly is explicitly written out. Each step has fewer than 600 characters, so there is no long step concealing a lemma. Existing-node proof routes do not use this item, and the server dry run will also check acyclicity. Off-unit inputs are declared individually in split_report.tool_uses as generic tools; they realize the source's scheme shrinking and change of site without replacing the unit's route.

For small cases: on Spec of a field a coherent full-support module is a nonzero finite-dimensional vector space and has positive rank. A torsion coherent module on an integral scheme has rank zero and fails full support, exactly the excluded case. For F=O_X on an integral Noetherian scheme the rank is one. Empty X and F=0 on a nonempty X are excluded by the hypotheses. Nilpotent generic rings are excluded by reducedness; no field argument was applied to them. None of the cited inputs introduces a dimension or separated-over-S assumption. No Lean was written or compiler run.

## Unfinished work

None in this one-level split. Existing unsplit inputs remain their own queue items. No new queue items were needed.

## Validation

The required server dry run exited successfully: OK (not pushed) at 5a5ae21ce5f, preflight passed. The delivery command ran the required server checks. Local tools/check_dag.py, tools/review_split.py and tools/preflight_delivery.py were not run. This report-only validation update is revalidated before the final push.
