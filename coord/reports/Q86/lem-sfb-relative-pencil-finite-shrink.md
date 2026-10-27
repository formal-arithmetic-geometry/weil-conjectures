# Stage-1 delivery: lem-sfb-relative-pencil-finite-shrink

Group Q86, 2026-10-23. Direct delivery; no second worker, no Lean writing or compilation.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-pencil-finite-shrink.json`: existing statement node, now split into eight complete proof steps; statement and stmt_deps preserved verbatim. Mathlib searches find component lemmas, not the complete assertion.
- `citations.json`: one entry for every step/use pair, quoting each cited node's actual statement verbatim.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log. `write_split.py` is sandbox-only preparation.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched all of `lean/WeilConjectures/` for the item id, its blueprint tag, pencil/Pencil, relative_pencil, finite-surjective and finite-shrinking terminology. No project declaration states the item. In particular the searches did not treat imported sorry declarations or a Mathlib theorem about a single finite fibre as a proof of the relative-pencil assertion.

## Wanted literature

WANTED: `literature/de-jong-families-curves-alterations-1997.pdf`, §3.4, printed p.606, for lem-sfb-relative-pencil-finite-shrink. It is absent locally. I read the publisher's PDF at https://www.numdam.org/item/10.5802/aif.1575.pdf, PDF page 8, printed p.606: the paragraph beginning with arbitrary lifts of the two special-fibre sections and asserting that a finite relative pencil exists after shrinking. The proof_origin remains agent: the eight steps give the explicit quotient-free shrinking argument rather than claiming that de Jong wrote those details.

## Findings and scope

The item was unsplit and had no Lean audit record or released repair note. The sandbox initially had no node, report, searches or previous delivery, only dispatcher brief markers. The source's shrinking assertion is correct, and the full item is correct. No STATEMENT-DISPUTED correction is needed. The inherited source place's sentence about finite-separable parameter descent is generic extraction history: this particular node only restricts an already specified generic pencil and introduces no field extension. I preserved the source metadata.

I read AGENTS.md, the stage-1 worker brief and role, GOAL.md, STATE.md, SETUP.md including its three levels, stages/1-dag.md, tools/README.md, and both occurrences of delivery-errors B--E. I read the item's chapter and unit records. This is not a unit key statement, so no unit record is changed. The existing branch realizes the direct-image alteration prerequisite within the stated unit; the generic geometric tools below do not replace that route.

`blueprint_refs.py ancestor` reports None for this inherited created-item chain. I preserved the inherited from.node=null, its detailed from.place and via list. Whole-blueprint searches for pencil, finite fibre and projective space found no statement equivalent to the complete relative-pencil assertion. The finite-near and standard-chart nodes are component tools, not duplicates of the item.

## Mathlib search results

All new searches were run through the required msearch.py command, and the output was read. The exact tool/query strings and result records are appended to the item and present in searches.jsonl. I retained the item's previous search records unchanged.

The first LeanFinder phrasing returned Proj properness, fromOfGlobalSections, affine-space surjectivity and unrelated pointsPi declarations. A second phrasing about deleting closed images returned Proj construction, valuative-criterion and affine-transition-limit declarations. Neither contains the relative-pencil result. LeanSearch returned finite-implies-proper, finite fibres and restrictions of an already finite morphism; these do not shrink the base around the given point. Loogle returned proper/finite equivalences, `exists_isFinite_morphismRestrict_of_finite_preimage_singleton` and the finite-image version. The grep result puts the former at Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:406; I read lines 399--440. It is Stacks 02UP and is a component already carried by lem-trf-proper-finite-fibre-finite-near, not a one-line specialization giving this item. No unavailable service was relabelled a negative result.

## Review by Q86

I read de Jong §3.4 at the publisher PDF location above and checked the proof's supporting Stacks statements in the local source. The relevant readings were modules.tex Tag 01CY (lemma-s-open), constructions.tex Tags 01NE (lemma-projective-space), 01NF (definition-projective-space and its following relative-coordinate paragraph), 01NG (lemma-standard-covering-projective-space), 01NH (lemma-projective-space-separated), morphisms.tex Tags 01W1 (definition-proper), 01W4 (base-change-proper), 01W6 (lemma-image-proper-scheme-closed), 01WI (lemma-finite-local), 01WL (lemma-base-change-finite), 01WN (lemma-finite-proper) and 02NH (lemma-quasi-finite), and more-morphisms.tex Tag 02UP (lemma-proper-finite-fibre-finite-in-neighbourhood). I also read the Noetherian version in coherent.tex (Tag 02OH), and chose the existing general 02UP node so no unnecessary local-Noetherian interface or hidden hypothesis is needed. No new nodes need separate source reviews.

For step 1 I opened lem-weil-pbc-nonvanishing-section-trivializes: its statement actually says that each nonvanishing locus is open and trivializes the line bundle. I opened lem-weil-pbc-invertible-generating-sections-fibre: it actually gives generation iff the nonvanishing loci cover. The module is invertible by the item's hypothesis, so both apply. I read def-pc-base-change and def-pc-scheme-fibre for the pulled-back module and fibre space, including the homeomorphism onto the inverse-image subset. The section values agree after tensoring to the same residue field, so fibre generation removes every point over s, not only closed points. I read def-weil-proper-morphism: universally closed means closed under every base change and in particular on U itself. Hence the image of the closed base locus is closed. A principal neighbourhood of s exists and has a nonzero denominator because A is a domain. This is the first actual argument, not a new node restating a clause.

For step 2 I opened def-weil-pbc-morphism-to-projective-space-by-sections and lem-weil-pbc-projective-space-functor-of-points. The former gives the relative map with the specified base projection; the latter explicitly includes compatibility with pullback, which a mere representability definition would not supply. Together with def-pc-base-change, they identify both fibre maps and every later restriction. The sections generate on the whole retained source by step 1, as their hypotheses require.

For step 3 I opened lem-weil-pbc-proper-fp-permanence, whose part (b) is proper base change; lemma-nagata-projective-space-base-change-proper, whose statement covers every base and the two homogeneous coordinates; def-weil-proper-morphism, which includes separatedness; and lem-weil-pbc-proper-over-separated, which requires a proper source over V, separated target over V and an actual V-map. These hypotheses are exactly p_V, q and h, with q h=p_V from step 2. Thus h is proper. I do not infer it merely from the phrase 'proper family'.

For step 4 I opened lem-weil-pbc-finite-closed-map-finite-fibres, which explicitly gives finite underlying fibre sets. Fibre-product associativity identifies h's fibre over each t of P_s with the fibre of the finite given psi_s; def-pc-scheme-fibre supplies the topological fibre identification. I opened lem-trf-proper-finite-fibre-finite-near: it states 02UP for any scheme and any point with finite inverse-image set, without a closed-point or Noetherian hypothesis. It therefore applies even to the generic point of P_s and to an empty inverse image. I opened lem-weil-pbc-finite-local-on-target: clause (3) is precisely the open-cover criterion used to combine the neighbourhoods O_t into O. The proof does not secretly assume psi_s is surjective or that a finite cover has already been chosen.

For step 5 I again use projective-space properness and the definition of universally closed to remove q(P minus O). The removed closed subset misses s because O contains all of P_s. A principal base neighbourhood is taken inside this complement, rather than treating arbitrary open subsets as affine. I opened lem-weil-pbc-finite-morphism-permanence: its part (a) gives finite base change for the inclusion of P^1_U' into O, and def-pc-base-change identifies the source of that base change with Y_U'. This justifies finiteness of the actual section map and preserves the specified fibres.

For step 6 I opened lem-weil-pbc-projective-space-standard-charts in full: parts (a) and (c) give a cover and the polynomial chart rings for the base-change projective space used by the item, including their base maps. I did not cite a field-only chart theorem or silently identify two different projective-space interfaces. The remainder is elementary: A_b[T] is a domain, its zero prime lies in every nonempty basic open, and that prime contracts to zero in A_b. This proves density for the actual generic-fibre subset via def-pc-scheme-fibre, without introducing an unnecessary projective-density node.

For step 7 the finite-closed-map node explicitly gives that the image is closed, and def-weil-surjective-morphism explicitly means pointwise topological surjectivity. The generic-surjectivity hypothesis and the fibre equality from step 2 put the dense P^1_K inside that image. Therefore the closed image is the entire target. This is where generic surjectivity is used; it was not inferred from finiteness of the special fibre.

For step 8 I checked that the group acts over U, so every base restriction Y_U' is stable. Restricting the assumed equality of morphisms on the generation locus gives the same equality on Y_U'; this is elementary, as is transporting the generic-etale assertion along the equality of generic-fibre morphisms. The assertion is only about the same nonempty generic-fibre open, exactly as stated in the item. No relative-etale spreading theorem or extra flatness assumption is being hidden here.

I tested the small cases. If A is a field, s is generic, and the two shrinkings may keep all of U. If s is not closed, the fibre homeomorphisms and 02UP remain valid. If the inverse image of a t in P_s is empty, it is still finite, so 02UP supplies a neighbourhood; special surjectivity is not assumed. With a nonflat proper family, the proof still only uses properness, finite fibres and closed images. With nilpotents or extra vertical components in Y, the nonvanishing loci and proper closed-image removal still apply. A constant generic pencil cannot satisfy the given generic-surjectivity hypothesis. A purely inseparable generic pencil is allowed for the main conclusion; it simply does not meet the optional generic-etale hypothesis. A nonfaithful or infinite group causes no problem because invariance is only restricted from the stated hypothesis.

I checked B--E against the files: no new statement nodes, no elementary lemma promoted to a node, no duplicate or item clause renamed, no hollow data or Lean changes, no SGA citation, no dependence on a cited proof's private construction, and no false claim of Mathlib absence. Every use is backed by the cited statement, and citations.json quotes those statements exactly. The complete proof has eight steps of lengths 966, 500, 320, 658, 636, 670, 301 and 522 characters, all below 2000; no long step hides a separate lemma. The statement and statement dependencies are unchanged. The generic tools outside the unit are explicitly declared in split_report.tool_uses, especially the 02UP node filed under trace formula, used solely for its scheme-theoretic statement.

## Not duplicates

No new nodes were created. The six non-Mathlib tool citations are reused existing nodes, not new duplicates. In particular the preexisting general 02UP lemma was reused instead of creating a new finite-neighbourhood node.

## Unfinished work

No mathematical obligation of this item remains. Stage 1 leaves the cited existing open lemmas to their own nodes. Server validation and direct push results follow below when the commands complete.

## Validation

The required `deliver.py Q86 lem-sfb-relative-pencil-finite-shrink --no-push` completed with exit 0 and printed `OK (not pushed)` at fd6c14136db: server preflight passed. No local DAG checker, Lean compiler, Lake command or repository git command was run. The dry run had fully exited before the subsequent direct-delivery command.


## Repair of returned head 2984fb5d80c

The 2026-10-23 05:14 UTC return says the reader approved the split but landing refused the side completion that the live queue had not received. I continued the retained sandbox, not a fresh split. The initial repair dry run completed with exit 0, `OK (not pushed)` at d91ae379f37. The delivery command fetches the current server sheaf-dag and builds on that fetched base; no repository git command was run by the worker.

I compared the retained node with the current repository node. The current node is unsplit, with an empty proof. Its statement, statement dependencies, blueprint references, source and all other retained metadata agree with the sandbox; the differing fields are precisely the proof, proof dependencies, proof origin, split report, status and appended search records. There is no statement change to reconcile. I retained the approved eight-step route and all existing search history. The Lean source search again found no declaration for the item or its pencil terminology, so no attachment supersedes the work.

For the dependency recheck I read the entire current statement of every one of the sixteen proof dependencies, not only the quoted fragment. All twenty-six step/use quotes remain verbatim in the current statements. In step 1 the nonvanishing and generation statements still give the open generation locus, and universal closedness still permits removal of its closed complement's image. In step 2 the projective-coordinate definition and pullback-compatible functor-of-points statement still identify the maps on both specified fibres. In step 3 proper base change, projective-space properness and proper-over-separated still prove properness of the actual map over the retained base. In step 4 the current finite-fibre node still covers all points and empty fibres, the current 02UP statement still has no Noetherian or closed-point assumption, and target locality still covers an arbitrary union of the finite neighbourhoods. In step 5 proper closed-image removal and finite base change still give the smaller affine base. In step 6 the current chart statement still supplies both the cover and the polynomial chart rings over the actual affine base. In step 7 the finite closed-image and surjectivity statements still give the asserted conclusion. In step 8 base change still gives the restricted morphism, and equality of the original generic map retains the optional etale assertion.

I re-read the local source statements and proofs for 02UP, 01W6, 01NG and 01CY, checking especially the all-point fibre assertion, separated target hypothesis and projective chart base maps. I made step 4 explicit about the point of P underlying a point of its s-fibre, its unchanged residue field and the resulting fibre-product identification. I made step 5 explicit about factorization through the open subscheme O; this is justified by restriction of the structure sheaf, rather than by mere set-theoretic image containment in a general subscheme. These are actual clarifications of the delivered proof. All uses and citation quotes are unchanged because their current statements already supply the required facts.

The original Review by Q86 and source/search records above are retained. The field-base, nonclosed s, empty fibre and nonflat-source checks remain valid. No new nodes or Mathlib leaves were created, and no step exceeds 2000 characters. The final repaired content is submitted to the required server dry run before the direct push.
