## Worker report

Q130, stage 1, 2026-10-24. Item: lem-sfb-finite-jet-normalizer-detection.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-jet-normalizer-detection.json: statement node, now split into nine steps; no Mathlib match for the whole assertion.
- citations.json: one verbatim statement quotation for every step/node citation (12 entries).
- report.md: this report. searches.jsonl is the search command's unmodified log. prepare.py is a sandbox-only preparation script, not a project file or part of the delivery.

New nodes: **0**. New Mathlib leaves: **0**. Existing results provide all non-elementary inputs. No Lean was written and no compiler, Lake or build command was run. No repository or launcher file was changed.

### Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, finite-jet normalizer terminology, identity jets, universal jet density, and the relevant smooth-group model found no declaration stating this item. Abstract subgroup normalizers and unrelated infinitesimal-neighborhood results do not supply an attachment. The finite-flat module pushforward theorem read below is already assigned to its own existing node.

### Wanted source

WANTED: Conrad, Reductive group schemes, Proposition 2.1.6 and proof, pp.61--63; Lemma 2.1.3 and proof, pp.58--59; Theorem 2.3.6 proof, pp.73--74, for lem-sfb-finite-jet-normalizer-detection. Expected local filename: literature/conrad-reductive-group-schemes.pdf. I read the Stanford PDF online at the item's source URL; I did not download or write into literature. proof_origin.by remains agent, recording the expanded argument and the missing local document.

### Issues found and corrections

There was no prior sandbox split and no item repair note. The live item was unsplit. Its statement is unchanged, including arbitrary A, arbitrary test schemes, disconnected ambient G, and absence of a self-normalizer assumption. Conrad's Theorem 2.3.6 assumes a connected ambient group and a self-normalizing subgroup for the later quotient theorem; neither assumption is used by its preceding jet-normalizer argument. The proof now isolates that argument without importing the extra assumptions.

The source's descending-chain assertion requires an explanation: stabilizers of larger closed subschemes do not generally stabilize their smaller closed subschemes. Here the lower jets are recovered by intersecting with the ambient jets, which conjugation preserves. Step 2 establishes that special property and step 5 explicitly uses it. Stabilization is proved using ideals, not underlying closed sets. Both directions of containment are imposed to avoid assuming that one-sided preservation of a finite scheme implies equality.

The inherited blueprint.from.node is null; blueprint_refs.py ancestor prints that exact value. I preserved its existing long via/place chain rather than inventing a new ancestor. I read the current literature/blueprint/latest (main-20261024) chapter, unit and direct-image proof, as well as the recorded DAG chapter/unit. The current direct-image proof uses compactification and the proper/open cases; the long inherited alteration chain is historical supporting material. I did not alter a chapter, unit, or another node, or claim that the latest blueprint itself states this finite-jet lemma. Whole-blueprint searches for normalizer and infinitesimal gave no match; the finite-locally-free search found general definition and module results, not this assertion. same_as remains empty.

### Unfinished work

No part of the item's assembly proof is left open. The existing cited nodes retain their own stage-1 work queues; they are not asserted to be Lean-closed or re-proved here.

## Not duplicates

No new nodes were created. Instead I reused lem-sfb-smooth-section-finite-jets, lem-sfb-smooth-section-universal-jet-density, lem-sfb-smooth-connected-subgroup-noetherian-model and lem-sfb-finite-locally-free-source-factorization-locus after reading their statements. The existing relative-smooth-subgroup-normalizer proof was also read, but it is not cited: this item's own argument supplies finite-stage stabilization. The general module interpretation is supplied by lem-pc-finite-flat-pushforward-locally-free, not a new special-case lemma.

## Mathlib searches

The inherited search history is retained. The five fresh queries are copied exactly from searches.jsonl into mathlib_searches: two LeanFinder phrasings, LeanSearch, qualified Loogle, and source grep in AlgebraicGeometry. All services answered. The hits concern abstract group/Lie/topological normalizers, Sylow stabilizers, Galois categories, and profinite invariant ideals. They do not state a scheme-theoretic assertion for all test schemes or finite neighborhoods of a smooth section. The qualified scheme-normalizer Loogle and the scheme-source grep had zero hits. No unavailable service was recorded as a negative result, and no search was invented.

## Review by Q130

I read Conrad's Proposition 2.1.6 and its proof (pp.61--63), including the use of universal weak schematic density, and Theorem 2.3.6 proof (pp.73--74), specifically the normalizer intersection before imposing the self-normalizer hypothesis for the quotient construction. I also read the finite-source coefficient-equation argument in Lemma 2.1.3 and Proposition 2.1.2, and the local Stacks finite-flat lemma in morphisms.tex, Tag 02KB, label lemma-finite-flat. The tag map confirms 02KB, 01QR and 00FM. There are no new-node sources to certify.

For step 1 I opened the finite-jet node: its statement gives finite locally free jets and the quotient-compatible base-change isomorphism, with no connectedness assumption on the smooth affine source. Thus it applies to G as well as H. I opened def-pc-finite-locally-free: it means finite, flat and locally finitely presented, not already locally free coordinate modules. To close that distinction I cite lem-pc-finite-flat-pushforward-locally-free. Its statement gives finite locally free module pushforwards for precisely these morphism hypotheses; the input module is the structure module of rank one. I read the upstream theorem isFiniteLocallyFree_pushforward in lean/WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean at lines 214 onward, and checked its finite, flat, lfp and locally free module binders. This generic off-unit tool is declared under split_report.tool_uses; it does not replace the unit route. Identifications on nonaffine tests are the same quotient-compatible maps on overlaps.

For step 2 I opened def-weil-closed-immersion: its affine characterization supplies the surjective coordinate map. The remaining work is explicitly calculated, rather than hidden in that definition: a lift of an augmentation-zero element has augmentation zero, ideal powers map to ideal powers, and sums of powers identify H_n intersect G_m. A conjugation automorphism fixes the section, so its pullback preserves the augmentation ideal in both directions. The universal point over G verifies action preservation, not only preservation for rational points. These are elementary ideal identities and identities of group-object morphisms.

For step 3 I opened lem-sfb-smooth-connected-subgroup-noetherian-model. Its statement simultaneously preserves the group operations, the finitely presented closed subgroup, smoothness and nonempty geometrically connected fibers, and explicitly gives a Noetherian model. It is not merely a smooth-algebra descent statement. No assertion about representability or finite jets is taken from it.

For step 4 I opened lem-sfb-finite-locally-free-source-factorization-locus. It permits arbitrary parameter P, arbitrary test T and arbitrary base change; it requires only finite locally free source, affine finitely presented target, and finitely presented closed target. H_0,n supplies the source by step 1, G_0 the target and parameter, and H_0 the closed target. Importantly I use H_0 as target, not an unproved finite-presentation assertion for its jet. Both conjugation families are actual morphisms from the group operations. The same affine closed-immersion definition supplies the quotient ideals; lem-weil-pbc-scheme-morphism-gluing, whose statement I opened, glues the unique quotient factorizations on a general test. This gives a represented closed locus without invoking a Hilbert scheme or normalizer theorem.

For step 5 the preceding containment loci become equality stabilizers by the computed H intersect G_n identity and the two inverse conjugations. The lower jet equals H_n intersect G_m, so preservation follows by applying the automorphism to that intersection. Evaluating containment of these functors on the universal quotient point gives inclusion of ideals. This is an elementary calculation from the preceding steps, with no external normalizer or chain theorem hidden in it.

For step 6 I opened lem-weil-pbc-closed-immersion-base-change, which gives that the inverse image in H_0,T is closed. I opened lem-sfb-smooth-section-universal-jet-density: it explicitly allows every base-changed test, with no reducedness/Noetherian condition on T. Its Noetherian hypothesis concerns A_0, which step 3 provides, and its connected geometric fibers concern H_0, not G_0. It concludes equality of closed subschemes, not just equality of points. The omitted zeroth jet is contained in the first. Applying it separately to g and its inverse proves both containments. The converse uses the already proved ambient-jet intersection identity.

For step 7 I opened pqf-lem-affine-open-locnoeth and def-weil-pbc-noetherian-ring. The first gives a Noetherian coordinate ring for affine G_0; the second states finite generation of every ideal. Choosing generators in the sum of an increasing family and taking the largest finitely many indices proves stabilization directly. No additional descending-chain lemma or existence of a normalizer scheme is presumed. Arbitrary-test factorizations are those already verified in step 4.

Step 8 uses the universal all-tests result of step 7 and the group-compatible model/base-change identifications from steps 1 and 3. Each W over A is also over A_0, so no preservation of an infinite intersection under tensor product is assumed. This is why the proof handles nonflat and nonreduced base change.

Step 9 uses the locally free coordinate modules already proved in step 1, simultaneously chooses their local bases, and writes the finite principal-open selection explicitly using an expression for 1. The rank inequalities follow on residue fields from the two quotient maps C_i to D_i and D_i to the base. A quotient remains a quotient under tensoring, so no flatness of the base change is used. All nine steps are shorter than 2000 characters. I checked the elementary steps for hidden general lemmas: each is an ideal calculation, application of an already established universal characterization, finite selection, or finite-dimensional rank inequality.

Small cases: H=G gives equality normalizers G at every order; the trivial smooth subgroup has rank-one jets and is preserved by every conjugation; disconnected G causes no change because only H is used for density. In positive characteristic the first jet need not suffice, so the proof chooses an unspecified N from increasing ideals and does not replace it by the Lie algebra. The construction admits nonreduced/non-Noetherian test rings because the cited density and locus statements explicitly do. For the zero base ring the base scheme is empty and the final cover can be empty. Varying relative dimensions are accommodated by separate constant-rank trivializing opens, not a globally asserted rank. These checks found no statement error to mark STATEMENT-DISPUTED.

This review addresses B1--B10 with no new nodes or attachments, C1--C8 by statement quotations and the declared generic tool, D1--D5 by an explicit assembly argument rather than a renamed conclusion, and E1--E7 by the hypothesis and base-change checks above. No second worker was started, as required by the direct-delivery brief.
