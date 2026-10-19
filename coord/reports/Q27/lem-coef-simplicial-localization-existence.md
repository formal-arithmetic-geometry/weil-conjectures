# Worker report: lem-coef-simplicial-localization-existence

## Files written

- dag/nodes/sec-six-functors/lem-coef-simplicial-localization-existence.json: statement unchanged; split into eight proof steps.
- dag/nodes/sec-six-functors/lem-coef-simplicial-edge-inversion-pushout.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-filtered-inner-horn-factorization.json: new statement-only lemma, unsplit; no Mathlib match for the filtered-colimit clause.
- citations.json: one verbatim statement quotation for each of the twelve step/node citation pairs.
- searches.jsonl: actual msearch results, reused in the node records with identical tools and queries.

The sandbox also contains the local JSON-writing helper write_split.py. It is not a delivery file. No repository, Lean source, launcher, unit, chapter or live coordination file was changed. No compiler, Lake, local DAG checker or git command was run by the worker.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id and for simplicial localization, inner anodyne/fibration and localization/filtered-colimit terminology. The hits concerning localization of rings and ordinary categories do not construct this simplicial localization. Upstream master sorry declarations are not treated as proofs.

## Wanted sources

WANTED: local archive of Kerodon Proposition 6.3.2.11, tag 05ZP, for lem-coef-simplicial-localization-existence.

WANTED: local archive of Kerodon Corollary 6.3.2.9, tag 05ZL, and Corollaries 6.3.2.7 (05ZJ), 6.3.2.8 (05ZK), for lem-coef-simplicial-edge-inversion-pushout.

WANTED: local archive of Kerodon Proposition 4.1.3.2, tag 01BP, for lem-coef-filtered-inner-horn-factorization.

I read these sources online at https://kerodon.net/tag/05ZP, https://kerodon.net/tag/05ZL, https://kerodon.net/tag/05ZJ, https://kerodon.net/tag/05ZK and https://kerodon.net/tag/01BP. The inherited item already uses online Kerodon with archive WANTED. No download was made. The expanded proof is marked proof_origin.by=agent because there is no local archived source. Kerodon and Stacks use distinct tag namespaces; 01BP here is not the Stacks finite-presentation lemma.

## Findings and corrections

The imported item was a correct, unsplit statement of 05ZP. No statement dispute or change is needed. Its ordinary filtered-colimit assertion is stronger than merely preserving filtered colimits up to categorical equivalence, so a generic functorial fibrant replacement is insufficient. I retain the explicit inverse-gadget construction and the special finite-horn small-object replacement in the source proof. Its strict naturality gives the specified comparison, rather than a new choice of an equivalent object.

The two new nodes do not restate the item or its clauses. The first asserts the universal property of a specified finite-gadget pushout with arbitrary, possibly non-quasicategorical output and does not provide the final functor or any colimit result. The second is a general theorem about arbitrary simplicial arrows and inner lifting properties, with no localization or marking in its statement. Their combination, the Joyal lifting argument, and the two explicit colimit arguments supply the item's actual construction.

No change to the chapter or unit route is made. I read sec-six-functors and sk-prop-sf-biduality-general, and the ancestor record prop-coef-integral-exceptional-adjoint. This is a supporting construction many levels below that ancestor, through the item's existing blueprint.from.via chain. The two created nodes retain that full ancestry and add the item as their first via entry. No replacement route or off-unit proof tool is introduced. The item is not a key unit statement, so its unit record is not written.

## Search and duplicate audit

Before creating either node I searched the whole DAG for its source tags and for inner-anodyne factorization/replacement, inverse gadgets and edge localization, and ran blueprint_refs.py ancestor and search for functorial inner, inner anodyne, horn replacement, localization of simplicial, inverting edges and edge inversion. These yielded no blueprint statement to reuse. The broader localization search also found no matching blueprint statement. same_as is [] for all three nodes.

I opened the relevant existing statements, including presentable-cellular-factorization, enriched-functorial-factorizations, infinity-equivalence-anodyne-factorization, infinity-relative-joyal-factorization, coherent-inner-anodyne-equivalences, joyal-quasicategory-characterizations, quasicategory-invertible-interval, enriched-marked-realization and universal-localization-pushout. The existing functorial factorization nodes do not promise preservation of all filtered colimits. The localization pushout node concerns universally localizing maps of two whole spans, whereas this construction adjoins a fixed inverse gadget to arbitrary selected edges and asserts the edge-inverting full-functor-category property. It is neither a special case with the necessary hypotheses nor a source for the missing marked universal property. The existing localization-filtered-colimit node depends on this item and is not cited, avoiding a cycle.

All Mathlib searches used msearch.py with this group and item. For each new node I ran LeanFinder, Loogle, source grep and LeanSearch and read the hits; a second semantic phrasing and a second grep were tried. The item was also searched twice semantically. All services returned normally. The JSON results retain their actual log records. Ordinary CategoryTheory.Functor.IsLocalization, read in Mathlib/CategoryTheory/Localization/Predicate.lean:45-58, localizes ordinary categories, not arbitrary simplicial sets with all coherent transformations. The gadget searches returned horn pushouts, skeleton/coskeleton, QCat and finite presentability; none has the required localization statement.

The factorization searches found SSet.innerAnodyneExtensions and inner-horn smallness in Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/Basic.lean:35-102, and CategoryTheory.SmallObject.functorialFactorizationData in Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean:460-468. I read these sources. They give inner-horn functorial factorization, but do not assert filtered-colimit preservation of the chosen factorization. Grep of CategoryTheory/SmallObject for filtered-colimit preservation returned no hits. The Kan-Quillen SSet.modelCategoryQuillen.J hits, read in CategoryWithFibrations.lean:35-86, use all horns rather than inner horns. The filtered-colimit theorem hits concern generic colimit functors; using them to establish preservation for the recursively constructed factorization requires a proof, so this is not a one-line Mathlib specialization. No Mathlib leaves are claimed.

## Not duplicates

lem-coef-filtered-inner-horn-factorization vs lem-weil-pbc-finite-presentation-kernel-surjection-finite-type: Kerodon 01BP is a functorial factorization of simplicial arrows; the existing node uses Stacks 01BP for finite generation of a sheaf kernel.

lem-coef-filtered-inner-horn-factorization vs lem-weil-pbc-quasi-coherent-finite-type-affine: the existing node concerns affine sections and finite-type/presentation modules on schemes; its text mentions the unrelated Stacks 01BP.

lem-coef-filtered-inner-horn-factorization vs lem-weil-pbc-finite-presentation-local-comparison: the existing node uses Stacks 01BP to compare local module presentations, not inner-horn factorizations.

lem-coef-filtered-inner-horn-factorization vs lem-weil-pbc-module-finite-presentation-extension: the existing node extends a finite-presentation module and its map across a quasi-compact open in a scheme; its mention of Stacks 01BP has no connection with Kerodon 01BP.

lem-coef-filtered-inner-horn-factorization vs lem-weil-pbc-finite-presentation-kernel-comparison: the existing node produces finite generators of module kernels from comparison maps, not simplicial factorization or filtered-colimit preservation.

No existing source carries Kerodon 05ZL, 05ZJ or 05ZK. The existing item carries 05ZP, which is distinct from both new source results.

## Review by Q27

I read the full statements and proofs of Kerodon 05ZP, 05ZL and 01BP online, and 05ZJ/05ZK to identify the finite gadget without an undefined reference. In 05ZJ the edges 02 and 13 are collapsed separately, leaving two distinct quotient vertices; in 05ZK the selected edge is 12, not 01 or 23. The new gadget node spells out those exact degreewise pushouts. Corollary 05ZL applies to any collection of edges, including degenerate edges, and imposes no quasicategory hypothesis on either the original object or its pushout. Its full functor-category formulation is the localization definition already used by the item. Proposition 01BP is about every simplicial arrow, not only arrows to the point, and explicitly includes functoriality and filtered-colimit preservation. The new factorization statement retains both structural maps, the input universe and arbitrary small filtered ordinary index categories.

For step 1 I checked the new gadget node's full statement: it supplies exactly the displayed D and the restriction equivalence, without assuming D is fibrant. Step 2 uses only the two degreewise pushout universal properties from that statement; its summand-index map w to a(w) is valid even when different markings merge, and uniqueness proves the actual equations. This is an elementary construction, not a new naturality lemma.

For step 3 I checked the new factorization node for the functor T, both natural maps, the inner-fibration target map and the strict functor laws. Applied to X to Delta^0 it gives a quasicategory by the inner-horn definition in def-cbc-enhanced-diagrams-cones. It gives the precise object L and map F required. Step 4 cites the complete statement of joyal-model-structure: inner horns are trivial cofibrations and trivial cofibrations are exactly the maps lifting against Joyal fibrations. Thus those fibrations are inner fibrations, and the inner-anodyne lifting property identifies r as a trivial cofibration. I checked joyal-functor-equivalence-test, which asserts a coherent equivalence for the actual restriction map for arbitrary simplicial source and target. It is not merely a homotopy-category comparison. The implication is a few-line lifting-class argument, so it is marked elementary.

For step 5 the gadget's restriction lands in the full W-inverting subcategory, the functor-equivalence test supplies replacement invariance, and def-coef-universally-localizing-simplicial-map gives exactly the universal property to prove. The quasi-inverses compose, retaining coherent transformations. There is no assertion that a categorical equivalence between ordinary homotopy categories by itself proves this property.

Step 6 writes the finite representative argument identifying colim W_i with the union in C_1. Filteredness is used to identify two representatives at one common stage, not to assume the transition maps are monomorphisms. The subset property W_k subset (C_k)_1 then gives equality in W_k. Step 7 explicitly tests maps from each degreewise pushout into an arbitrary set S. Compatible functions on the colimit degrees and on the marking indices give exactly the same agreeing pushout data. This is the ordinary colimit universal property, so no unproved theorem about infinity-categorical colimits is being used. Step 8 checks nonempty connectedness of the index category before identifying colim Delta^0 with Delta^0, and then uses exactly the filtered-colimit and structural-map clauses of the factorization node. The comparison is the canonical comparison for the strict functor, and the equality involving F follows from the two structural-map identifications. These last steps are elementary applications of the stated universal properties; no separate lemma is hidden in them.

I checked every cited node's statement against each use and recorded verbatim copies in citations.json. Both proof results used from the existing DAG belong to sk-prop-sf-biduality-general. I kept proof_deps equal to the union of the uses lists. All new nodes are statement-only, introduce every object, define their lifting terminology inline or cite the correct existing definitions, and have no proof sketch smuggled into their statements. Neither is an elementary fact or a relocation of the item's conclusion.

Small cases checked: C empty forces W empty, the pushout is empty and the inner replacement remains empty; W empty gives D=C and an inner replacement with the expected empty-marking localization. For C=Delta^1 and W its nondegenerate edge, D is exactly Q with its specified edge and the source's universal property applies. A degenerate selected edge may still attach a redundant Q and need not leave C literally unchanged; no such false equality is claimed. The factorization allows the identity, an arrow to the empty simplicial set (whose domain must be empty) and empty lifting-problem families. A one-object terminal index category gives identity comparisons. For noninjective diagram maps, markings may merge, and step 6 accounts for that explicitly. The filtered comparison never uses an assertion that arbitrary colimits of quasicategories are quasicategories.

I checked delivery-errors B through E against the written JSON and source statements. No SGA source is used. All eight steps are shorter than 2000 characters (the maximum is 726), and none hides a separate comparison theorem: the non-elementary gadget and replacement inputs are precisely the two new nodes. No target statement or coefficient category is changed. Nothing mathematical is left unfinished at this split level; the two new nodes are deliberately unsplit for subsequent workers.

## Validation

The required server checks and dry run are recorded below after they finish. Delivery is left to the independent second reader.

Server check_dag via srvcheck.py: `check_dag OK: no finding introduced by the sandbox or on its nodes` (2026-10-17). This check was run only on the server, not locally.
