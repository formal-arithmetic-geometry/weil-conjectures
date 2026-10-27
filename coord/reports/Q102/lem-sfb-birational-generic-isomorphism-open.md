# Stage-1 delivery: lem-sfb-birational-generic-isomorphism-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-birational-generic-isomorphism-open.json: item, statement unchanged, split into four steps using existing nodes.
- citations.json: nine entries, each quoting verbatim the statement used by its proof step.
- searches.jsonl: five actual msearch results, read and retained; no match.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and birational/Birational. The exact id has no declaration there. The affine fraction-field birational theorem and generic-fibre partial-isomorphism model theorems concern integral schemes and common opens, not this morphism's entire inverse image over an open for arbitrary nonreduced component-birational schemes. No attachment is claimed. Existing Sheaf statements are not evidence of finished project proofs.

## WANTED

None. All proof sources are available locally.

## Issues found and changes

The item was statement-only. Its statement is true as written, including nonreduced schemes and the absence of reducedness of Y. Stacks 0BFP assumes Y reduced for its other clauses; its codimension-zero argument uses 0BAJ, whose locally-finite-presentation alternative requires no reducedness. Thus adding reducedness here would be unnecessary and would change the intended stronger prerequisite.

The existing lem-sfb-birational-isomorphism-dense-open already states the non-elementary theorem needed. Creating another dense-isomorphism theorem would duplicate it. The extra assertion about all component generic points is proved directly; density alone on an arbitrary space is not enough, so the proof explicitly uses finiteness of the components and their maximality to construct an open piece in each component.

Read GOAL.md, the three levels in SETUP.md, the stage-1 brief and stage document, roles/worker.md, tools/README.md, the chapter/unit records, and delivery-errors B--E (both copies). The current latest blueprint's chapter, unit and det-thm-sf-ctf-stability-direct-images proof were read. The item is an inherited algebraic-geometric prerequisite in its alteration branch, not the unit key statement. The inherited blueprint ancestor is null (blueprint_refs ancestor exits without printing a node); it and via are retained. Whole-blueprint birational search finds only normalization properties, which are not equivalent. No route or unit realization was changed.

## Unfinished work

None for this one-level split. Proofs of existing cited unsplit prerequisites remain their own items. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new node was created. Existing DAG nodes lem-sfb-birational-isomorphism-dense-open and lem-sfb-birational-common-dense-opens were read and reused through the former. Searches for 0BAJ, 0BFP, lemma-birational-isomorphism-over-dense-open, Noetherian finite components and finite presentation over a Noetherian base were made across dag/nodes. The item specializes the existing theorem and separately verifies its additional generic-point clause; no redundant helper is introduced.

## Review by Q102

I read morphisms.tex Tag 0BAJ (lemma-birational-isomorphism-over-dense-open), including both alternative hypotheses and its proof, and varieties.tex Tag 0BFP (lemma-modification-normal-iso-over-codimension-1), especially proof (1). I checked the definition of component-birational morphisms in morphisms.tex and its generic-local-ring condition against the item's unchanged statement. I also read morphisms.tex 01W1 and 01TX, properties.tex 0BA8, schemes.tex 01IS, and topology.tex 004W and the finite-component open-piece part of 0052. There are no new-node sources to audit.

Step 1 cites def-weil-proper-morphism for separatedness and finite type, def-weil-finite-type-morphism for the inclusion of local finite type in finite type, and pqf-lem-lft-fp-locnoeth for local finite presentation. Each conclusion is stated by that node; the required locally Noetherian target is the given X. I checked the corresponding Mathlib Noetherian.lean declaration at lines 274--276. No global finite-presentation or reducedness assumption is smuggled in.

Step 2 cites lem-weil-pbc-noetherian-finite-components for the finiteness of the components of X, which is Noetherian exactly in the item's locally-Noetherian and quasi-compact sense. I read its source 0BA8 and Mathlib's matching declaration. The second citation, lem-sc-scheme-sober, states that each component of either scheme has a unique generic point. Closures distinguish these points for distinct components, so the given bijection of generic points transfers finiteness from X to Y. This avoids needing an uncited quasi-compactness composition or a theorem that Y is Noetherian.

Step 3 cites lem-sfb-birational-isomorphism-dense-open. I read its entire statement: it requires separatedness, local finite presentation, finite component sets, the bijection of component generic points, and the isomorphisms of their local rings. Steps 1--2 supply the first three, and the item supplies the last two verbatim. Its conclusion concerns the whole inverse image f^{-1}(V), precisely what is needed, rather than just an arbitrarily chosen source open. Its DAG unit is the same as this item's; no off-unit tool declaration is necessary.

Step 4 is elementary relative to the three statements it cites. def-weil-irreducible-components says components are closed and maximal; def-sc-generic-point supplies C = closure{xi}; lem-sc-irreducible-components-cover says every point lies on a component. The finite union of all other components is closed, excludes xi by maximality, and its complement O is contained in C by the cover statement. Since V is dense, the nonempty open O meets V. The closure definition then forces xi into V. This is the explicit argument, rather than assuming a generic-point clause not present in the step-3 citation. All citation quotes were copied from the nodes' statements, not from their proofs. No step exceeds 2000 characters.

I tested X empty (the empty dense open and vacuous generic clause), a one-component nonreduced X with f its identity (generic stalks need not be fields), a finite disjoint union (all component generic points must survive), and the normalization of a nodal curve (the open can omit the singular point). The proof only uses separatedness from properness and remains valid in each case. A generic-field-only map such as reduction of a nonreduced component would fail the actual local-ring isomorphism hypothesis and is not incorrectly admitted. I checked the potential D1/D2 fault by using the already existing general theorem rather than inventing a new restatement. There are no new unsplit proofs, no false small-case assertions, and no unrecorded searches. I read the five msearch outputs: PartialIso/Birational supplies a different definition, local-isomorphism and stalkwise criteria impose stronger global hypotheses, and the normalization hits require integral/normal hypotheses absent here. The second semantic phrasing likewise gave no one-line specialization.
