# Stage-1 worker report

Item: lem-coef-ghn-ind-presheaf-cartesian-realization
Group: Q114
Date: 2026-10-17

## Files written

- dag/nodes/sec-six-functors/lem-coef-ghn-ind-presheaf-cartesian-realization.json: item, split into eight proof steps; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-relative-cone-presheaf-fibers.json: new statement-only structural lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-relative-functor-cocartesian-classifier.json: new statement-only relative-functor classification lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-cartesian-maps-presheaf-extension.json: new statement-only generic extension theorem; no Mathlib match.
- citations.json: a verbatim statement quote for every citation of each item step.
- searches.jsonl: actual msearch.py searches for the item and new lemmas. The Mathlib records in new nodes use the exact logged query strings and retain the results, not invented searches.
- report.md: this report. write_split.py is sandbox-only drafting support, not a delivery file.

## Attachments

None. Exact blueprint-tag and conceptual searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no project theorem for this item or its proposed new nodes. The same reference searches in upstream master found no attachment candidate; no sorry declaration was treated as a finished proof.

## WANTED

WANTED: Gepner–Haugseng–Nikolaus, Lax Colimits and Free Fibrations in infinity-Categories, arXiv:1501.02161v3, Definition 7.2, Proposition 7.3, Definition 9.1, Warning 9.2, Lemma 9.4 through Corollary 9.9, Lemma 9.10, Propositions 9.12 and 9.16, Example 9.14 and Corollary 9.17. Read online at https://arxiv.org/html/1501.02161v3; no archived copy is in literature/. Supports the item and all three new nodes.

WANTED: Lurie, Higher Topos Theory, Corollary 3.2.2.13 and Corollary 5.3.5.4, for the relative-exponential edge criterion and the existing Ind-presheaf recognition node. GHN explicitly state and use these facts in the paragraphs read above. I read GHN's explicit unpacking of the former, and the existing Ind criterion's full statement; I do not claim to have reread the entire HTT proof. No document was downloaded or changed. proof_origin.by is agent because the archived literature is absent and the expanded proof was written here.

## Statement typing correction

STATEMENT-DISPUTED (strict simplicial typing, not the mathematical realization): the imported condition (ii) writes a map from the ordinary join E_a^triangleleft into the raw relative-cylinder pushout. GHN Warning 9.2 explicitly notes that this pushout is the alternative/fat cone, not the ordinary join. The imported text supplies neither a comparison inverse nor a categorical replacement.

For the concrete test A=point and E=N([1]), the pushout collapses the bottom of the simplicial square Delta^1 x Delta^1. Its edge from the new apex to the upper vertex 1 coming from the diagonal is distinct from the vertical cone edge at vertex 1. The simplex with vertices apex, upper 0, upper 1 has the former edge; the ordinary-cone face would have to be the latter if it preserved both specified cone arrows. Thus there is no literal cone inclusion with those prescribed restrictions. This is a failure of the displayed strict map, rather than a counterexample to GHN's theorem.

I replaced that expression by its intrinsic coherent augmented-limit formula: the diagram contains the common target X(a) as well as all Psi(q(k)), and its limit is compared with Psi(c). Equivalently it is the limit in S_/X(a). This is exactly the condition in GHN's proof of Proposition 9.16 and agrees with the original display after the fat/ordinary categorical cone comparison. No hypothesis or intended conclusion was weakened. The empty diagram requires Psi(c) -> X(a) to be an equivalence, not that Psi(c) itself be contractible. No target statement, coefficient category or base-change morphism is changed.

## Not duplicates

Before creating anything I searched the entire DAG by relative-cone, presheaf/slice, relative-functor, Cartesian-map, right-fibration and limit-extension terminology and searched the whole imported blueprint with tools/blueprint_refs.py. The blueprint searches for relative cone, relative functor, Cartesian maps, cone presheaf, Cartesian sections, presheaf slice and presheaf fibration gave no matching blueprint assertion. I also read the broader presheaf search results. The nearest blueprint ancestor is prop-coef-integral-exceptional-adjoint; every new node records that ancestor with the whole existing via chain preceded by this item.

lem-coef-relative-cone-presheaf-fibers vs lem-coef-ghn-ind-presheaf-cartesian-realization: the new lemma is the unrestricted slice/category-of-elements description for any functor p; it makes no cocartesian-edge descent test, no Ind claim and no limit-extension claim. Item steps 2-8 prove the substantial missing conclusions.

lem-coef-relative-functor-cocartesian-classifier vs lem-coef-day-relative-exponential-model: the new lemma is the relative functor construction for any Cartesian fibration and any target, including its edge criterion. The existing Day node concerns sections of the universal RFib diagram over a covariant diagram of base categories and monoidal envelopes. Its explicitly cocartesian total category of opposite fibers is not the Cartesian fibration E^op over A^op occurring here; there is no asserted one-line specialization supplying the required relative-exponential theorem.

lem-coef-cartesian-maps-presheaf-extension vs lem-coef-infinity-presheaf-free-cocompletion: the new lemma gives a concrete model by edge-preserving maps over right-fibration elements for arbitrary category-valued functors, and identifies its higher coherences and contravariance. The existing free-cocompletion theorem gives a restriction equivalence for colimit-preserving functors; it does not identify those relative mapping categories.

lem-coef-cartesian-maps-presheaf-extension vs lem-coef-right-fibration-section-limit: the existing node computes a space of sections of a right fibration as a limit of spaces; the new lemma computes an infinity category of Cartesian/cocartesian-preserving maps to a category-valued fibration and its extension on all presheaves.

The existing lem-coef-infinity-presheaf-ind-criterion and lem-coef-ind-right-adjoint-coherent were reused rather than recreated. The new nodes have no Stacks tag because no Stacks theorem states these quasicategorical classification results. No new lemma is elementary or a restatement of an item's clause: they are the independent general GHN 9.6, 7.3 and 9.10 inputs, and the item's proof carries the two condition translations and their compatibility.

## What was wrong or corrected

Besides the typing issue above, the imported item had no proof. The proof now includes the right-adjoint identification instead of silently equating presheaf restriction with the given Ind diagram. It proves transport compatibility and existence of the restricted Cartesian fibration, not merely equivalence of individual fibers. I corrected a draft explanation of the left-fibration edge condition: transport between its fibers need not be an equivalence of spaces; its outer-horn fillers directly make every edge cocartesian. No such incorrect transport claim remains in the node.

The repository initially lacked the assigned item and its ancestry, so the first report recorded that assignment inconsistency and srvcheck failed on missing input. The required dry-run invocation refreshed the shared repository; the node then appeared. Its temporary-worktree checkout was interrupted before preflight, and I resumed from the newly available authoritative JSON. That transient missing-input diagnosis is resolved and is not the result of this split. All inherited item fields and searches were retained. This report supersedes the initial blocker report.

## What could not be finished

No mathematical gap in the item's eight-step proof is deferred except for the explicitly cited statement-only nodes, as required for a one-level split. Three new nodes remain unsplit; zero Mathlib leaves. No Lean was written or compiled. The sandbox is for a fresh second reader; no push or delivery is authorized or attempted.

## Review by Q114

I read the worker contract, stages/1-dag.md, SETUP.md including all three levels, delivery-errors.md B-E in full, GOAL.md and dag-sync.md, and the item's chapter and unit. The unit has no proof steps to rebind; this is a general foundational support lemma within the existing ancestry, not its key node. I read the current ancestor proof, which uses the finite mapping-complex adjunction, and kept the established foundational chain beneath it. No SGA source is used. All cited statement nodes used for this proof lie in the item's unit; definitions from the enhanced-cone framework remain definitions.

For the item I read GHN's definitions, Warning 9.2 and the full proofs of Propositions 9.12 and 9.16, plus Example 9.14 and Corollary 9.17. For the first new node I read Lemma 9.4, Remark 9.5, Proposition 9.6, Proposition 9.7 and Corollary 9.8, and the explicit fiber formula in Proposition 9.12's proof. For the second I read Definition 7.2 and Proposition 7.3 with its proof, Corollary 9.9(2), and the edge criterion explicitly unpacked in Proposition 9.12's proof. For the third I read all four clauses and the proof of Lemma 9.10. Their new statements introduce their own categories and universes and contain no proof steps or sketches hidden in the statement.

1. Step 1 uses the new general relative-cone fiber lemma exactly for its two displayed fiber equivalences, specified cone transformation and natural homotopy-fiber formula. Its hypotheses are met because the given A,E are small and each presheaf has a small right-fibration model. The lemma allows arbitrary p, so no unstated colimit or cocartesian hypothesis is needed here.
2. Step 2 uses the new relative-functor lemma with the Cartesian opposite E^op -> A^op and target S, and the fibration definition for the opposite and its horn convention. Its universal equivalence is explicitly a statement about full quasicategories over the base, not merely spaces or sets of sections. This says exactly what the step takes. The product is the opposite of E x_A Y_X, with all higher simplices retained.
3. Step 3 uses the new fiber lemma at E=A=point to detect equivalences by homotopy fibers, and the relative-functor lemma's mixed-edge criterion. I checked the direction: x belongs to X(b), and the lower-source value is X(alpha)(x) in X(a). Thus it proves the actual displayed square condition, with no unjustified geometric fiber comparison.
4. Step 4 uses that same slice equivalence, the existing pointwise-limit and mapping-space-limit statement of lem-coef-infinity-yoneda-presheaf-limits, and the existing full equivalence of clauses (1),(2) in lem-coef-infinity-presheaf-ind-criterion. I opened all of these statements. The Ind criterion assumes E_a small and admitting lambda-small colimits, both in the input F_0. The augmented limit formula is written out by its testing maps, including K empty; it is not a separate elementary node or a citation to a mere definition.
5. Step 5 uses the existing Ind criterion to show restriction preserves the full Ind subcategories, Ind presentability for a genuinely small filtered presentation, Yoneda evaluation for the actual formula Map(y(c),N)=N(c), and the mapping-space colimit criterion for both ends of the adjunction calculation. It uses the coherent Ind-adjoint node's explicit extension and coherent right-adjoint assertion, not an assertion hidden only in its proof. I checked that the filtered presentation is an allowed shape, L_u preserves it by the stated extension property, and no extra presentability adjoint theorem is being assumed. The displayed equivalences are natural in all variables and identify the given coherent diagram, not just arbitrary fiber adjoints.
6. Step 6 uses only the new natural fiber and relative-functor equivalences to restrict to the two full subcategories identified in steps 3-5. Their statement-level naturality explicitly includes pullback/precomposition along a base presheaf map. Therefore the cited results do supply the comparison on arrows and higher simplices, as well as on objects.
7. Step 7 uses the ambient Cartesian fibration and its pullback transports from the first new lemma, and the actual horn/lift definitions in def-coef-infinity-fibrations. The short proof of restriction to a transport-stable full subcategory is written explicitly. This is the single elementary step; it does not conceal a new classification theorem.
8. Step 8 uses the new general extension theorem for precisely its cocartesian-map model, existence and uniqueness and naturality, and the existing straightening statement for coherent classification, universe enlargement and uniqueness. The functor H has its actual right-adjoint transition maps by step 5. All indexing right fibrations are small in the original universe, while presheaf/Ind categories are formed in containing universes. Thus no large-index colimit was smuggled into a small existence result.

I tested A empty (both presheaf categories are terminal), A a point and F_0(a) terminal (condition (ii) forces Psi(*) -> X(*) an equivalence, yielding the identity fibration over S), X empty (empty element category gives a terminal fiber), and the empty colimit shape (the comparison is to X(a)). I also tested a nonidentity base arrow to verify the variance of precomposition and a two-point or disconnected X to verify the common target in the slice limit. For the new lemmas separately I checked p the identity, E empty, terminal base, product/constant fibrations, and G constant with A a point: here Y_X is itself a space and the extension model gives Fun(Y_X^op,G), whose arrows in the source are necessarily carried to equivalences. For a general base the edge-preservation condition remains essential; no claim of an unrestricted Fun(Y_X^op,G) formula is made. No nonemptiness, connectedness, uncountability or idempotent-completeness hypothesis was added. Every citation is backed by an actual verbatim statement in citations.json, and proof_deps is the union of uses. The DAG/blueprint/source and Mathlib searches were actually made; the ordinary slice-presheaf equivalence at Mathlib/CategoryTheory/Comma/Presheaf/Basic.lean:613 is a genuine hit but has Type-valued ordinary categorical hypotheses, so it is not a leaf for these quasicategories.

## Validation

The server review_split check and the required delivery dry run are run after these files are complete; their final results are recorded below. No local checker, Lean compiler, Lake or build command is run.

The server review_split check exited 0 with PASS. The required deliver.py --no-push exited 0 and printed: OK (not pushed) deliver/Q114/lem-coef-ghn-ind-presheaf-cartesian-realization at 81d9734bfb: preflight passed. A durable handoff receipt was saved. This validates the complete mathematical split, citation quotes, search provenance and new-node records. I then added the actual item-specific fresh search to its retained inherited search records and recorded these results; the final dry run below validates that exact final handoff.

Tool issue for maintenance: review_split prints 0 new nodes even though this delivery contains three. Its head_version function reads the temporary commit HEAD, and its new-node filter excludes every child already present in that same HEAD (tools/review_split.py lines 29-34 and 128-131). This explains the count after srvcheck commits the sandbox. I did not edit or work around the checker. The delivery preflight independently checks new files against the base and passed all three statement-only nodes. The second reader should still read all three listed new nodes.

## Second reading by Q114

I independently opened GHN arXiv:1501.02161v3 in the cited HTML and checked the item against Definition 9.1, Warning 9.2, Propositions 9.6, 9.12 and 9.16, Example 9.14 and Corollary 9.17. The source's alternative-cone warning supports the item's intrinsic augmented-limit formulation; the source's (K^{\triangleleft\triangleright}) limit is equivalent to the displayed cone with apex \(\Psi(c)\). No Stacks source applies, and no SGA source is used.

- Step 1: checked against GHN Proposition 9.6 and the fibre calculation in the proof of Proposition 9.12; the cited relative-cone fibre statement supplies the slice and right-fibration equivalences with the required smallness.
- Step 2: checked against GHN Corollary 9.9(2), Definition 7.2 and Proposition 7.3; the opposite of the cocartesian (p) is Cartesian, transport is precomposition, and the right-fibration opposite has all edges cocartesian by the left-fibration horn definition.
- Step 3: checked against the last paragraphs of the proof of Proposition 9.12; fibrewise equivalences over each (x\in X(b)) are exactly the pullback-square condition, and the relative-functor edge criterion supplies cocartesian preservation.
- Step 4: checked against Proposition 9.16, its proof at lines 866--875, Example 9.14 and the existing Ind criterion; the slice is \(\operatorname{Fun}(B,\mathcal S)\) by fibre evaluation, limits are pointwise, and the empty shape is retained.
- Step 5: checked against Proposition 9.16, Corollary 9.17 and the existing coherent Ind right-adjoint statement; precomposition preserves the bounded-limit subcategories because the cocartesian transport preserves colimits, and the mapping-space pairing identifies the transport with the stated right adjoint.
- Step 6: checked against the naturality clauses of Proposition 9.6, Corollary 9.9 and the relative-functor classifier; the equivalence is on full subcategories and is natural under base-presheaf maps and higher simplices.
- Step 7: checked against Proposition 9.6 and the horn/lift definition in `def-coef-infinity-fibrations`; the full subcategory is stable under Cartesian transports, so the ambient Cartesian fibration restricts.
- Step 8: checked against Lemma 9.10(4), Proposition 9.16 and Corollary 9.17; the cocartesian-map model is the unique limit-preserving Ind extension, with the stated universe enlargement.

- `lem-coef-relative-cone-presheaf-fibers`: its self-contained statement was checked against Definition 9.1, Lemma 9.4, Propositions 9.6--9.7 and Corollary 9.8; it is a general slice/right-fibration lemma, smaller than the item, and has no hidden proof.
- `lem-coef-relative-functor-cocartesian-classifier`: its self-contained statement was checked against Definition 7.2, Proposition 7.3 and the edge criterion used at Proposition 9.12 lines 831--833; it correctly includes naturality and the cocartesian-edge test.
- `lem-coef-cartesian-maps-presheaf-extension`: its self-contained statement was checked against Lemma 9.10(1)--(4), including both Cartesian and cocartesian models, representable extension, naturality and universe conventions; it is not duplicated by the existing free-cocompletion or Day/RFib nodes.

I searched the entire DAG for all three new-node identifiers and for relative-cone, relative-functor, Cartesian-section and presheaf-extension terminology. The nearest existing nodes (`lem-coef-infinity-presheaf-free-cocompletion`, `lem-coef-day-relative-exponential-model`, and `lem-coef-right-fibration-section-limit`) do not state these quasicategorical classification results, so no new node was removed. The recorded grep, LeanSearch, Loogle and LeanFinder searches were inspected and are genuine no-match results for these statements; there are zero Mathlib leaves.

I tested the item and new nodes on the empty base, a point base, terminal and empty presheaves, a nonidentity base arrow, the empty colimit shape, identity and product fibrations, and constant targets. These cases confirm the variance, the requirement \(\Psi(c)\to X(a)\) for the empty shape, and the retained higher/coherent data. I repaired one proof-step imprecision: the slice of spaces over \(B\) is written as \(\operatorname{Fun}(B,\mathcal S)\) by fibre evaluation (the prior \(B^{\mathrm{op}}\) was a variance typo; (B\) is a space, but the covariant form is the source's form). No hypothesis or conclusion was changed. All citation quotes remain verbatim statements of the cited nodes, and `proof_deps` remains the union of step uses.

No Lean, Lake, compiler, build, local preflight, or live-project command was run. The required server delivery dry run is the remaining validation step after this report and statement repair.

Citation repair after server dry run: step 5 now quotes the complete verbatim statement of `lem-coef-ind-right-adjoint-coherent`, including its universe convention and `def-cbc-enhanced-cartesian-fibration` clause. No proof text or node statement changed.
