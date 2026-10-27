# Stage-1 report: lem-sfb-group-scheme-differentials-from-identity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-group-scheme-differentials-from-identity.json: split the unchanged statement into five steps; no Mathlib match.
- citations.json: nine step/node entries, each quoting a verbatim substring of the cited statement.
- searches.jsonl: actual searches produced by the required msearch command; existing item searches retained unchanged.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. No Lean files written and no compiler, Lake or build invoked. All writes are within the item sandbox.

## Attachments

None. Searched the project WeilConjectures tree for the exact blueprint tag and for differentials/cotangent at the identity, then examined the GroupScheme and Modules differential interfaces. Lie/Basic defines the identity cotangent sheaf but does not identify its structure pullback with the whole differential sheaf. Modules/Differentials has relativeDifferentials and affine/open-immersion comparisons, not this group-scheme isomorphism. Ring-level Hopf algebra cotangent dimension theorems impose extra hypotheses and do not give the claimed sheaf isomorphism. Thus no exact project attachment was found.

## Wanted literature

None. Read literature/stacks-project/groupoids.tex, Tag 047I, label lemma-group-scheme-module-differentials, including its full proof; read morphisms.tex, Tag 01V0, label lemma-base-change-differentials, and the preceding functoriality statement. Read the use in moduli-curves.tex, Tag 0E6G, label lemma-in-DM-locus-vector-fields. No SGA source is used.

## Corrections and scope

The statement was correct and remains unchanged. The original node had no proof. The split follows precisely the shearing-map argument of 047I; it omits only the conormal-sheaf and freeness conclusions that the item never states. In particular, it does not assume smoothness, finite type, reducedness, commutativity, or characteristic zero.

The non-elementary input already exists as lem-trf-relative-differential-sheaf-base-change. Its arbitrary cartesian-square clause applies both to the product projection and to the automorphism square. This avoids creating either a duplicate base-change node or a separate elementary shearing lemma. It is declared as a generic off-unit tool in split_report.tool_uses: the source 047I itself uses exactly this input, and the unit route is not replaced.

The item inherited blueprint.from.node = null and a detailed from.place and via chain. The required ancestor command returns None; this existing maintainer-owned lineage is preserved. The report names the inherited ultimate direct-images/alteration place and the actual local Stacks argument. Read the chapter record, unit record and current main-20261015 unit text. The item is not the key statement of its unit, so no unit realization fields are written.

## Searches and duplicate checks

Whole-DAG searches by Tag 047I and lemma-group-scheme-module-differentials found the item and its parent context, not a second statement of the result. Searches for relative differential base change and Tag 01V0 found lem-trf-relative-differential-sheaf-base-change, whose statement was opened and reused. Whole-blueprint searches for differentials, group scheme, invariant differentials and 047I found no exact duplicate of the item. The group-scheme tangent and smooth cotangent statements have additional smoothness hypotheses or different conclusions and cannot replace it.

Ran leanfinder twice with different formulations; the results were ring-level Kahler/cotangent and generic presheaf differential declarations, not a group-scheme sheaf trivialization. Loogle with relativeDifferentials and GrpObj returned no hits. Both required Mathlib/AlgebraicGeometry grep patterns returned no hits. LeanSearch returned a rate-limit error and is recorded as unavailable. Read the generic presheaf differential and formally etale differential source interfaces to check the closest hits do not supply the group-scheme assertion. The exact actual searches and outcomes are in searches.jsonl and appended to the item; no fabricated query or match is recorded.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. The existing scheme-sheaf base-change theorem is reused rather than cloned.

## Review by NF

I checked the five steps against the full argument in Stacks 047I, not just its conclusion. The theorem is stronger over an arbitrary base, but our item needs only a field base. Its proof never uses field-specific linear algebra: that is only for the additional freeness assertion in Stacks, which is outside this item.

Step 1 cites def-sc-group-scheme for the associativity, inverse and unit diagrams, and def-pc-fibre-product for the construction and uniqueness of pair morphisms. I checked these exact statements, including the morphism-valued rather than just field-point-valued meaning of the formulas. The inverse is right multiplication by the inverse of the second coordinate; its order is correct even for a noncommutative group. The calculations (gh)h^{-1}=g and (gh^{-1})h=g prove both composites, and the second projection stays fixed. This is a direct calculation from the cited definitions, not an independent hidden lemma.

Step 2 cites the full arbitrary cartesian base-change clause of lem-trf-relative-differential-sheaf-base-change. I opened its statement and verified that it supplies an isomorphism for arbitrary scheme morphisms, with exactly the ordinary pullback and local differential rule stated in the proof. Its separate finite-type conclusion is conditional and is not used. The square is the base change of f by f, with the SECOND projection as structure map; the pulled-back differential sheaf comes from the FIRST projection. No flatness hypothesis is smuggled into the application.

Step 3 cites that same base-change theorem and the product universal property. I checked the cartesian assertion explicitly: for a compatible pair (a,b), the unique lift is sigma a. In particular the bottom map is the identity on the SECOND G; this is not a mistaken claim that multiplication itself is a base-change projection. Applying the canonical base-change map to this square yields tau*D -> D with its stated derivation rule. Thus no uncited general theorem about invariance of differentials is needed.

Step 4 uses def-pc-module-pullback, whose statement explicitly supplies functoriality and the identity/composition comparisons. These comparisons give tau*p0*Omega = (p0 tau)*Omega = m*Omega. The arrow is c^{-1} composed with c_tau composed with tau*c, so its direction and both endpoints check. Only composition and applying a functor to an isomorphism remain; this is elementary from the cited functor statement.

Step 5 again uses the group unit diagram, product universal property and ordinary pullback comparisons, exactly as quoted in citations.json. I checked f e = id so (ef,id) really defines a map to the fibre product; m s = id and p0 s = ef have the correct order. Pulling back the step-4 map gives Omega -> f*e*Omega, not its accidental reverse or e*f*Omega. All maps are the canonical specified maps; no basis or arbitrary local trivialization is chosen, so the conclusion is canonical.

Small-case checks: G = Spec K gives zero differentials on both sides and the construction is the unique zero-module isomorphism. For the additive group it is the usual invariant dt trivialization. For the multiplicative group it is the invariant logarithmic differential (the construction is a map of sheaves, not evaluation at points). In characteristic p the nonreduced group alpha_p has free differential module on dt despite its failure to be smooth; the shearing inverse and base-change steps still work. A noncommutative matrix group checks the order in step 1; finite etale groups have zero differentials. No part of the proof uses finite-dimensionality of the identity fibre, so arbitrary non-finite-type groups are not excluded.

I checked delivery-errors B--E: no new nodes or unsplit proof sketches, definitions say the notions used, all non-elementary facts have cited node statements, no use of another node's proof, no statement weakening or new hypothesis, and no circular dependence. Every citation quote is an actual substring of its node's statement. The longest step is 810 characters, below the long-step threshold. The server review_split check passed with the declared generic tool use.

## Repair of the returned delivery

The return concerned a side completion that had not been promoted into the live DAG. I compared the retained delivered split with the current shared DAG item: the current item is unsplit, has an empty proof and no split report, while its statement, source, statement dependencies and inherited blueprint metadata agree with the retained version. The retained split and all six newly logged searches are preserved. The required delivery tool constructs the replacement commit on current origin/sheaf-dag and preserves current maintainer-owned fields; no repository git command was run by this worker.

I reread the current statements of all four proof dependencies: def-sc-group-scheme still supplies the group diagrams used in steps 1 and 5; def-pc-fibre-product still supplies the existence and unique pair morphism used in steps 1, 3 and 5; def-pc-module-pullback still supplies the functor and identity/composition comparisons used in steps 4 and 5; lem-trf-relative-differential-sheaf-base-change still has the arbitrary-base-change isomorphism and its differential rule used in steps 2 and 3. In particular, its finite-type addendum is not a hypothesis of that isomorphism. All nine citation quotes remain literal parts of the current cited statements. No dependency needs replacement or extra hypothesis on this base.

I reread Stacks 047I (groupoids.tex, lemma-group-scheme-module-differentials) and 01V0 (morphisms.tex, lemma-base-change-differentials), including their proofs, and repeated the project attachment search. The shearing proof remains valid over the current statements. I clarified step 1 to say explicitly that its two first-coordinate calculations concern the composites sigma tau and tau sigma, rather than the individual maps. This clarification changes neither the route nor the result. The statement is unchanged; no new node, Mathlib leaf, source or search assertion was added. The review above applies to this repaired split, including the non-smooth alpha_p and noncommutative checks. Rebase and renewed server validation address the return; no prior passing review is treated as a live completion.

## Unfinished work

None in this one-level split. The reused base-change node remains its own queued item, as required by stage 1. No new item was introduced.

## Renewed repair against the 08:44 UTC return

The return names branch head 68f8ee4d4ac and asks for rebase, rereading changed citations, adjustment, and renewed delivery. I retained the sandbox proof, report, citations and all six logged searches rather than restarting them. The initial required dry run on this retry exited successfully at 83da951ef59; it builds against current origin/sheaf-dag. Comparing the retained node to the current shared item shows differences only in proof, proof_deps, proof_origin, mathlib_searches, status and split_report: statement, source, statement dependencies and blueprint lineage agree. The live item remains unsplit; this is a delivery for promotion, not a claim that the side completion is already live.

I reopened each of the four current cited statements and both Stacks proofs, and checked every one of the nine literal citation quotes against the current statements. Their used clauses remain as described in the review above, so no citation or hypothesis changes are required. I additionally repaired the explicit cartesian argument in step 3: it now states p1 sigma = p1 and proves uniqueness of the lift u by u = sigma tau u = sigma a. This makes the use of the cited fibre-product universal property fully visible, without a hidden invariance theorem or a new node. The returned proof route and all searches are preserved. The final dry run and push are performed only after this adjustment; the earlier dry run is not treated as validation of edited content.

## Current repair and rebase review

The required initial dry run completed successfully at 526e5febf72 on this retry. It reconstructs the delivery against current origin/sheaf-dag; the shared live item is still unsplit. Comparing the retained delivered node against the current live node finds changes only in proof, proof_deps, proof_origin, mathlib_searches, status and split_report. The statement, its definition dependencies, source, created metadata and blueprint lineage are identical. No released repair-note file exists for this item. The earlier delivered proof and logged search results were retained and read; the search question and statement have not changed, so no search was repeated or invented.

I reread the full current statements of def-sc-group-scheme, def-pc-fibre-product, def-pc-module-pullback and lem-trf-relative-differential-sheaf-base-change. Their clauses used by this proof have not changed from the retained quotes: the group diagrams and product universal property justify steps 1 and 5; arbitrary differential base change justifies steps 2 and 3; the pullback functor and composition comparisons justify steps 4 and 5. All nine citation entries were checked against their current statements and remain literal substrings. In particular, no finite-type condition is needed for either use of differential base change.

Against the full Stacks 047I argument and its 01V0 input, I made step 1 more explicit: multiplication and inversion are morphisms over S, so the two pairs defining the shearing maps have equal composites to S and the product universal property actually applies. Both shearing maps preserve the second projection. This also supplies explicitly the projection identity used to construct the cartesian lift in step 3. The inverse calculations are valid in the stated order for noncommutative groups. Pulling the resulting differential isomorphism back along (e f, id) still gives precisely Omega -> f*e*Omega; the identity and alpha_p edge cases introduce no missing smoothness assumption. This is an adjusted split rather than an unchanged re-push; no statement or proof route is replaced.

I repeated the project attachment search and read the identity cotangent definition in GroupScheme/Lie/Basic.lean and the differential declarations in Modules/Differentials.lean. Neither supplies this sheaf isomorphism. The whole-DAG Tag 047I search still identifies only the item and its parent context; blueprint searches give no duplicate. No new nodes or Mathlib leaves are introduced. The final dry run below validates the edited proof and updated report before delivery.

## Repair review on 2026-10-23

The retained receipt identified the earlier delivered head b6614e4245c. I continued that sandbox rather than discarding its proof, citations, report, or searches. The required initial dry run exited with OK at 6d3967cec70 against the current server base. The current shared item is unsplit: its statement, statement dependencies, source, created metadata, chapter, unit and blueprint lineage agree with the retained item. Its differences are exactly the retained proof, proof dependencies, proof origin, search additions, split status and split report. There is no released repair-note file. The delivery tool rebuilds the commit on current origin/sheaf-dag; this worker runs no git command in the shared repository.

I reread every current cited statement, including the entire arbitrary-base-change clause of lem-trf-relative-differential-sheaf-base-change. The nine citation quotes are still literal substrings. Thus there is no changed dependency clause to replace: steps 1 and 5 use the group diagrams and fibre-product universal property; steps 2 and 3 use arbitrary relative differential base change; steps 4 and 5 use the ordinary pullback functor with its identity and composition comparisons. The field hypothesis agrees with def-sc-group-scheme. Neither application of differential base change uses its finite-type addendum. I reread Stacks 047I and 01V0, and the use in 0E6G, and checked the current chapter and unit records and main-20261015 unit text. No unit route is replaced.

The concrete adjustment in this retry is to step 3: it now names X=P, S=S'=G, f=p1, g=id, p=tau and f'=p1 explicitly. Its preceding existence-and-uniqueness calculation proves this really is a cartesian square; it is not an assertion that multiplication alone is a base-change projection. This clarifies the exact substitution into the cited statement before forming tau*D -> D. All hypotheses, directions and endpoints then check, and pulling along (ef,id) gives precisely Omega -> f*e*Omega. The source construction remains canonical even for noncommutative groups and for alpha_p; the trivial group has zero differentials. There are no non-elementary steps longer than 2000 characters, no hidden new lemma and no new node or Mathlib leaf.

I repeated the project attachment search and read GroupScheme/Lie/Basic.lean and the differential interface in Modules/Differentials.lean; neither states the item. Whole-DAG Tag 047I matches are this item and its two parent contexts, not duplicates. Whole-blueprint searches for group scheme, 047I and invariant differentials yield no duplicate. I read the retained search log results: the statement and search questions have not changed, so the actual queries and unavailable-service record are preserved without repetition. Delivery-errors B--E were checked against the actual statements and sources, especially C1/C4 and the absence of extra smoothness or finiteness assumptions. The final dry run validates this edited split and report before the push; the earlier passing receipt is not used for edited content.
