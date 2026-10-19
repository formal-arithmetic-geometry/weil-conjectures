# Q46 stage-1 worker report

Item: lem-coef-injective-simplex-cocone-restriction
Date: 2026-10-17

## Files written

- dag/nodes/sec-six-functors/lem-coef-injective-simplex-cocone-restriction.json: statement; split into six steps, reusing existing dependencies; no Mathlib match.
- citations.json: a verbatim statement quotation for every citation of every proof step.
- searches.jsonl: actual msearch.py search results, retained without alteration.
- report.md: this report and substantive self-review.

## New nodes

None. Zero new nodes and zero Mathlib leaves. The elementary operator-category construction and contraction remain in the item's proof, rather than being exported as duplicate lemmas or a restatement of the item.

## Attachments

None. Read-only searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, the ID and the injective-simplex/semisimplicial/cocone-restriction notions found no completed declaration stating this item. The upstream master source was treated only as reference material.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Lemma 6.5.3.7 (printed p. 676), Theorem 4.1.3.1, and Variant 4.2.3.15 step (3), for lem-coef-injective-simplex-cocone-restriction. The primary PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf was read online; it is not archived in the permitted literature directory. No download was made. The proof is marked agent-written because its operator/comma and pullback details are expanded here and the source is online, not an archived literature file. No Stacks tag states this quasicategorical result, and no SGA source is used.

## Findings and corrections

The shared DAG initially lacked the assigned node, and the initial sandbox had only the four brief markers. The DAG refreshed during the first delivery attempt; the item and its parent then appeared. That premature dry run was interrupted while waiting for worktree capacity, before any split was packaged. This report replaces the initial missing-input report because that condition is resolved.

The imported item had no proof or proof dependencies. Its statement is correct and unchanged. The proof now explains the ordinary comma category, the opposite orientation, the full prepended-zero functor and naturality equations, and why the strict pullback models the infinity-categorical comma. This avoids assuming a general base-change preservation theorem without its fibration hypotheses. It is the same HTT cofinality route, proved directly over each simplex using the contraction from Lemma 6.5.3.7; neither the chapter nor the unit is changed.

## Mathlib and blueprint searches

The inherited searches remain. New searches were run only through msearch.py, with the actual results in searches.jsonl and copied into the item. Two LeanFinder phrasings, LeanSearch, Loogle and two Mathlib greps found no matching statement. Hits concern ordinary cocones, face representability, finite presentability, truncation and the definition of a quasicategory. I read Mathlib/CategoryTheory/Limits/Final.lean:275-295: Final.coconesEquiv at lines 283-287 compares ordinary categories of cocones, and does not provide the item's coherent mapping-space theorem. The item therefore remains a split, rather than a Mathlib leaf.

Whole-DAG and blueprint searches used the exact ID, operator/cofinality keywords, HTT theorem numbers, and blueprint_refs searches for injective simplex, semisimplicial and cocone restriction. No imported blueprint node states the item in another form, so same_as is empty. blueprint_refs ancestor confirms prop-coef-integral-exceptional-adjoint. The item's existing exact ancestry place is retained and the split_report identifies the six steps realizing it. I read the sec-six-functors chapter, sk-prop-sf-biduality-general unit, and the parent poset-replacement split: the item supplies its injective-operator inclusion step, and the cited generic lemmas do not replace the unit's route.

## Tool use from another unit

The item's split_report.tool_uses declares lem-cbc-enhanced-functor-cone-calculus, of sk-prop-sf-cbc, as the generic theorem giving the quasicategory/Kan properties in steps 1 and 6. It supplies no cofinality argument; no node in the item's unit states this generic typing theorem. This is a declared tool use, not a change of the unit route.

## Not duplicates

No new nodes. Reused lem-coef-nerve-natural-homotopy-equivalence, lem-coef-infinity-isofibration-pullback-limit, lem-coef-infinity-cofinal-comma-criterion, def-cbc-enhanced-diagrams-cones and lem-cbc-enhanced-functor-cone-calculus. A read-only dependency traversal found no path from any of these theorem dependencies back to this item.

## Review by Q46

I read HTT Lemma 6.5.3.7's complete proof online, particularly its two transformations through the prepended-vertex functor, and compared it with Variant 4.2.3.15's intended cofinality step. There are no new node sources to audit. I checked delivery-errors B through E against the actual JSON and against each dependency's statement, not just its title.

Step 1 uses the actual ordinary nerve and functor constructions in def-cbc-enhanced-diagrams-cones and the explicit Kan assertion in lem-cbc-enhanced-functor-cone-calculus. It checks smallness and the empty case. Inner horn fillers in an ordinary nerve are written as compositions; this is elementary and does not presume that X is a quasicategory.

Step 2 needs no additional theorem: it gives mutually inverse descriptions of comma objects and morphisms. I checked the arrow direction with an operator from [m] to [n]: because the item takes opposite categories, the comma is the OPPOSITE of the injective-arrow category over [n]. Distinct operators stay distinct even if their composites into X agree. No nondegenerate-simplex replacement is made.

Step 3 writes the object and arrow formulas for prepending the value zero. The monotonicity check uses only that theta takes values in [n], so zero is below each value. The shifted arrow is injective even when theta is degenerate. Both naturality equations are written explicitly. This finite-order calculation is a proof step, not a new node.

Step 4 cites lem-coef-nerve-natural-homotopy-equivalence, whose statement explicitly permits zigzags with either orientation and does not require the component arrows to be isomorphisms. I supplied its P,Q data: the unique functor to the terminal category, its section selecting b, the strict identity composite, and the opposite zigzag. Its weak-homotopy-equivalence conclusion proves the nerve contractible. Applying it directly to the opposite category avoids an uncited opposite-realization comparison.

Step 5 cites lem-coef-infinity-isofibration-pullback-limit, whose statement allows any functor into the base but requires the other map to be an isofibration between small quasicategories. I verify that requirement for the undercategory projection: composition fills inner horns, and ordinary isomorphisms lift by composition with their inverses. The strict pullback is the nerve of the ordinary comma by its degreewise data. Thus the cited statement really supplies the infinity-categorical pullback used in the next step, rather than merely an ordinary pullback or a definition of one.

Step 6 cites lem-coef-infinity-cofinal-comma-criterion. Its statement gives precisely restriction on mapping spaces from a diagram to a constant diagram, for every target quasicategory and vertex, with no colimit-existence assumption. Steps 1 and 5 supply all its hypotheses, including smallness and contractibility of the INFINITY-categorical comma. I also cite the functor-cone calculus for the Kan condition. I did not use any conclusion known only from a cited node's proof. Every use has an actual verbatim statement quote in citations.json.

Small-case checks: X empty gives an identity restriction; n=0 still has the prepended-zero functor; X equal to a point keeps every degenerate simplex and every distinct operator, and the same comma contraction works. For a constant operator into any [n], shifting indices still yields injective transformation components. An additional read-only finite calculation checked 1,155 compatible injective arrows with dimensions 0 through 3: the prepended-zero operator remains monotone, shifted operators remain injective, their triangle equations hold, and both naturality component formulas agree. These checks confirm why retaining degenerate objects is essential and that no regularity or monomorphism assumption on X has entered. All statement fields and maintainer metadata are preserved, and proof_deps is exactly the union of uses. Nothing was written to the shared repository, the Lean checkouts or launcher, and no compiler/build tools were run.

## Unfinished work

No mathematical portion is intentionally deferred within this one-level split. Existing cited nodes retain their own proof obligations. The first completed dry run printed OK (not pushed), commit ef75f0e03e. The final dry run is repeated after recording the explicit generic tool use and the finite checks, so its receipt matches the final sandbox. The worker does not push.

## Second reading by Q46

Independent second reading, 2026-10-17. Read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 contract, the item's six steps, and the actual statement of every cited node. Read the primary HTT PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf: Notation 6.5.3.6 and the complete proof of Lemma 6.5.3.7 (printed p. 676), Variant 4.2.3.15(3) (printed p. 255), and the cofinality/comma discussion in §4.1.3. This result has no Stacks tag; none is invented. The source is online and remains WANTED for the archive. No SGA source is used.

- Item statement: checked all hypotheses against HTT's injective-operator inclusion and the existing universal cofinal-comma theorem; PASS. Its arbitrary small X is allowed because the comma over each simplex is computed directly. All simplices, including degenerate ones, must remain objects. The conclusion is the actual restriction on the specified mapping spaces, and there is no colimit hypothesis. Compared the parent poset-replacement step 4: this supplies exactly its inclusion for X=K_1.
- Step 1: checked against def-cbc-enhanced-diagrams-cones (ordinary nerve, functor object and mapping convention) and lem-cbc-enhanced-functor-cone-calculus (Kan assertion); PASS. The nerve horn argument is the elementary composition calculation, smallness follows from the displayed sets, and the empty case is an identity restriction.
- Step 2: checked against HTT 6.5.3.7's operator category and the definition of the comma in the cofinal criterion; PASS. Reversing the simplex-category arrows makes the comma C_n^op. Operators remain part of objects and arrows even when their images in X coincide. Both directions of the identification and composition are written explicitly.
- Step 3: checked every object, arrow and component formula against the two transformations in HTT 6.5.3.7; PASS. Prepending zero is monotone, shifting preserves injectivity, both triangle equations and both naturality equations are literal evaluations. This finite-order construction is elementary and does not warrant a new node.
- Step 4: read lem-coef-nerve-natural-homotopy-equivalence in full, including its zigzag hypotheses and allowance for noninvertible components; PASS. The specified P,Q satisfy both hypotheses, one strictly and one through the displayed opposite zigzag. The conclusion is a weak homotopy equivalence to a point. No opposite-realization comparison is being assumed.
- Step 5: read lem-coef-infinity-isofibration-pullback-limit and the definition of isofibration in lem-coef-infinity-isofibration-exponentiation; PASS after the small clarification below. All three objects are small nerves, the undercategory projection lifts isomorphisms by composition, and the composition filler lies over the prescribed base filler by uniqueness of inner-horn fillers in ordinary nerves. The pullback theorem therefore applies with no hypothesis on u. The degreewise comma identification is the exact strict pullback to which that theorem applies.
- Step 6: read the complete statement of lem-coef-infinity-cofinal-comma-criterion, particularly its infinity-categorical pullback convention and the actual mapping-space restriction conclusion; PASS. Steps 1–5 supply its smallness, quasicategory and comma hypotheses; the target is the arbitrary quasicategory E, not X. Constant diagrams restrict to constant diagrams directly from their definition. The calculus lemma gives the Kan properties used here.
- New nodes: NONE. B1–B7 have no new-node obligations; no elementary, duplicate, restatement or Mathlib result was exported as a node. Read-only searches of the whole DAG/current blueprint and the allowed source checkouts found no alternative statement or completed attachment; the parent uses this item rather than duplicating it. The generic functor-cone calculus is already declared in split_report.tool_uses; its typing assertion is a tool and does not replace the unit route.

Small cases: checked X empty and X a point (retaining all distinct operators); checked n=0, n=1 and constant theta. An independent finite calculation verified 140 compatible injective arrows with n=0,1 and domain dimensions through 3, including their shifted-arrow triangle and both naturality equations. Empty target E causes no extra hypothesis: when X is nonempty no p into empty E exists; when X is empty restriction is the identity. Terminal E gives point mapping spaces. These are the relevant categorical zero/empty tests; fields and schemes are not objects of this statement.

Changes made and reasons:

1. Expanded step 5's inner-fibration verification to say that its composition filler lies over the prescribed base simplex, using uniqueness in an ordinary nerve. This removes an implicit relative lifting check (C2/E1); no new theorem or dependency is needed.
2. Ran four independent msearch.py searches using different phrasings: LeanFinder on category-of-elements monomorphisms, Loogle on SimplexCategory/Final, grep on simplex/simplicial homotopy-final vocabulary, and LeanSearch on opposite face-operator inclusion. Preserved their actual appended searches.jsonl records and recorded them in mathlib_searches. The hits concern cofibrations, Dold–Kan, face/truncation formulas or order/cardinal cofinality, with no matching statement.
3. Appended this independent reading, preserving every first-worker section, including Review by Q46. No statement, source, unit, blueprint ancestry or dependency was changed. All seven citations.json excerpts were checked literally against the cited statement fields and remain true. The proof_deps list equals the union of the six uses lists.

No new nodes or Mathlib leaves; no statement dispute. No mathematical step is deferred beyond existing cited nodes. Only sandbox files were changed; no git command, Lean edit, compiler or build tool was run in either read-only repository. The completed second-reading report precedes the required final server dry run and delivery.
