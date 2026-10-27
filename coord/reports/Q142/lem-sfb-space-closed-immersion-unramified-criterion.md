# Stage-1 report: lem-sfb-space-closed-immersion-unramified-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-immersion-unramified-criterion.json: item, statement unchanged; split into four proof steps following Stacks 05W8.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-radicial-representable.json: one new statement-only node, status unsplit, no Mathlib match. This isolates only representability from 05W6; it has no universal-closedness hypothesis and asserts no closed-immersion conclusion.
- citations.json: 13 step/node citations, each with a verbatim quotation from the cited statement.
- searches.jsonl and search-results/: actual msearch.py records and complete responses. Searches for the item, the new representability node and an initially considered universal-injectivity comparison are retained. The last comparison was NOT made a node: its short field-point argument is step 3.

## Attachments

None. Searched lean/WeilConjectures/ for the item tag, closed-immersion/unramified concepts and algebraic-space declarations. The finite-unramified scheme results found do not state this algebraic-space criterion. No sorry declaration was treated as a finished proof. No Lean was written and no compiler, Lake or build command was run.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Problems found and changes

The item had no proof. Its statement agrees with Stacks spaces-more-morphisms.tex, Tag 05W8, equivalence (1) and (3), with universal closedness already assumed. There is no statement dispute and no hypothesis was added or dropped.

Read the chapter and unit records and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/ unit and direct-image proof. This small supporting criterion continues the existing Tag 05XA route through the node's recorded ancestry. No unit or chapter file is changed. The blueprint ancestor command prints None for this pre-existing chain; I retained its null ancestor and existing via chain, and gave the new node an explicit place in that chain with the item prepended to via. Searches of the whole imported blueprint for closed immersions, unramified/injective maps, unramified monomorphisms, radicial representable maps and Tags 05W6, 03MU and 040X found no blueprint node stating the missing representability input.

The proof does not silently assume that a fibre product over a scheme is a scheme. In the forward direction this follows from the assumed closed immersion's representability. In the reverse direction it follows from the new Tag 05W6 node BEFORE the scheme criterion is applied. Universal closedness survives the tests directly from its quantified definition; this is written out rather than assumed from a definition of properness.

Mathlib searches used leanfinder twice, loogle, grep and leansearch for each candidate. All services answered; none is recorded as unavailable. Read Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean:36-79, ClosedImmersion.lean:43-68 and 370, Finite.lean:124, and FormallyUnramified.lean:45-56. UniversallyInjective, its diagonal characterization, the closed-immersion criteria and the formal-unramified declarations concern schemes or rings. They do not give the algebraic-space representability theorem by a one-line specialization. The exact query texts and full responses are preserved, without inventing any search.

## Unfinished work

No unfinished part of this item's proof. The single new node remains statement-only, as required by the one-level split. Its proof source is 05W6: the diagonal is open and surjective, hence an isomorphism; the resulting locally finite type monomorphism is separated and locally quasi-finite, and the cited separated locally quasi-finite representability theorem applies. This outline is report material, not a proof inserted into the new node.

## Not duplicates

lem-sfb-space-unramified-radicial-representable vs lem-sfb-space-closed-immersion-unramified-criterion: the new input assumes no universal closedness and concludes only scheme representability, not a closed immersion or either direction of the item's equivalence. An open immersion of a proper open subset, such as G_m into A^1, satisfies the new input but is not a closed immersion.

lem-sfb-space-unramified-radicial-representable vs lem-sfb-space-lft-monomorphism-separated-lqf: the existing node has a scheme target, assumes a monomorphism and states separatedness and chartwise local quasi-finiteness, not representability. The new node has an arbitrary algebraic-space target, assumes unramifiedness and universal injectivity and supplies representability.

lem-sfb-space-unramified-radicial-representable vs lem-sfb-universally-closed-unramified-radicial-criterion: the existing node is a criterion entirely for scheme morphisms with universal closedness already assumed; it cannot justify a scheme representation of the fibre product of algebraic spaces.

lem-sfb-space-unramified-radicial-representable vs lem-sfb-space-unramified-permanence: the existing node supplies composition, cancellation, base change and the etale implication, not representability of an unramified universally injective map.

No existing node shares Tag 05W6 in its source. Searched both by that tag and by its hypotheses and conclusion, including the entire DAG and current blueprint, before writing the new node. No second node was created for scheme-test universal injectivity, since the existing field-point equivalence makes the needed argument elementary.

## Review by Q142

I read the full statement and proof of Tag 05W8 (spaces-more-morphisms-lemma-characterize-closed-immersion), Tag 05W6 (spaces-more-morphisms-lemma-universally-injective-unramified), and the scheme criterion Tag 04XV (etale-lemma-characterize-closed-immersion). For the sole new node, 05W6 explicitly says that under its condition (2), unramified and universally injective, the map is representable. I extracted only that assertion. It is a non-elementary input, not a clause restating the item. Its statement introduces the base, the two spaces, their morphism, the chartwise unramified condition, the pointwise universal-injectivity condition and every scheme test for representability. Its definitions are each named in stmt_deps. Its proof, proof_deps and proof_origin are empty/null as required for a new unsplit node.

For step 1 I opened def-sfb-space-morphism-properties: it quantifies universal closedness over EVERY algebraic-space base change. Consequently it includes every further scheme test T' -> T -> Y, which supplies exactly the scheme universal-closedness hypothesis of lem-sfb-universally-closed-unramified-radicial-criterion. I opened that node's statement: it asserts both implications, for arbitrary schemes, and gives precisely unramifiedness and universal injectivity from a closed immersion. The schemes exist here because representability was assumed in the item's definition of a closed immersion. No finite-presentation, noetherian or quasi-compact hypothesis was imported.

For step 2 I checked def-trf-algebraic-space for existence of a representable surjective etale scheme atlas V -> Y. I checked lem-trf-space-fibre-products-etale-covers for stability of a jointly surjective etale family under arbitrary algebraic-space base change, so U = X times_Y V -> X really is such a chart. Scheme representability of U comes from step 1's assumed closed immersion, not from that fibre-product lemma. I read lem-sfb-unramified-etale-compatible-charts: its single-diagram criterion requires a surjective SOURCE chart, which U -> X has, and the unramified scheme top arrow, which step 1 supplies. Thus it yields exactly the chartwise unramifiedness used in the item.

For step 3 I read spaces-morphisms.tex Tag 040X, particularly its common-field argument for (1) implies (2), and opened def-a1-algebraic-space-point-classes and def-weil-radicial-morphism. The former explicitly identifies representatives after a common field extension; the latter explicitly includes the equivalence between scheme universal injectivity and injectivity on K-valued points. After aligning the Z-components over K, both X-components are points of the SAME represented scheme X times_Y Spec K over its identity K-point. Therefore that field-point criterion identifies them. The sheaf fibre product of lem-trf-space-fibre-products-etale-covers then identifies the pairs, not merely their images in X. This is a short application of already stated facts and definitions, so it is marked elementary. There is no unproved claim that injectivity on underlying points alone implies injectivity of arbitrary K-valued maps.

For step 4 I checked the new node's exact hypotheses against the reverse assumption; it supplies representability without requiring universal closedness. I opened lem-sfb-space-unramified-permanence: its base-change clause imposes no flatness, etaleness or finiteness condition on T -> Y. The resulting unramified morphism is between schemes, and identity charts in lem-sfb-unramified-etale-compatible-charts give precisely scheme unramifiedness. The item's universal injectivity and the universally closed definition include every scheme base change, so both hypotheses of the existing scheme criterion hold for each g_T. That criterion yields the closed immersion of every scheme test, exactly the item's stated conclusion. This is the route of 05W8, not a new criterion asserted without proof.

I tested the statements and proof on empty source and empty target (an existing map to an empty target forces empty source), identity maps and arbitrary closed subschemes, including nilpotent and non-finitely-presented closed immersions. A surjective ring map is still finite type as an algebra, so such closed immersions do not invalidate unramifiedness. The map Spec k[epsilon]/(epsilon^2) -> Spec k is universally closed and universally injective but is not unramified, so the proof correctly cannot use it in the reverse direction. Two disjoint k-points over Spec k are unramified and universally closed but not universally injective. G_m -> A^1 is unramified and universally injective and satisfies the new representability assertion, while failure of universal closedness prevents the item's conclusion. Thus the hypotheses are used where needed and no properness or finite-presentation restriction is hidden.

I checked delivery-errors B through E against the node files: no duplicate or elementary new node, no new node that is a clause of the item, no proof inside the new unsplit node, no unsupported non-elementary step, no use of a cited node's private proof, and no new dependency cycle. The four steps have 566, 523, 871 and 943 characters before harmless prime-notation normalization, all below 2000. All 13 citation pairs have meaningful verbatim quotations in citations.json. Only the item and one new node are delivered; unrelated repository and launcher files were never written.
