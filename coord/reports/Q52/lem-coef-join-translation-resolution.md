# Worker report — repair of ad7fbeb25b

## Files written

- `dag/nodes/sec-six-functors/lem-coef-join-translation-resolution.json`: statement, split; ten proof steps and sixteen proof dependencies. Step 9 is replaced. The statement, statement dependencies, Steps 1–8 and 10 are unchanged.
- `dag/nodes/sec-six-functors/lem-coef-kan-enriched-hammock-comparison.json`: new statement-only node, unsplit; no Mathlib match. It specifies three canonical simplicial functors and their Dwyer–Kan equivalence property, with a strict vertex-category square.
- `citations.json`: 29 verbatim statement quotations, one for every citation in every proof step.
- `searches.jsonl`: retained earlier actual searches, with six actual repair searches appended by msearch.
- `report.md`: rewritten report. The earlier second-reading endorsement of the faulty Step 9 is superseded; a fresh second reader must review this repair.

New nodes: 1. New Mathlib leaves: 0. Existing Mathlib leaves reused: the simplicial-set definition, the extra-degeneracy contraction, unique nondegenerate decomposition, and the anodyne pushout-product statement.

## Attachments

None. Exact-id and conceptual searches over the supplied slopmaster2 `WeilConjectures/` and the read-only upstream master found no declaration for either the item or the proposed comparison. Searches included `lem-coef-join-translation-resolution`, `lem-coef-kan-enriched-hammock-comparison`, hammock, Dwyer, decalage, and join-translation names. Master sorries are not treated as finished proofs. No Lean was written or compiled.

## WANTED

WANTED: Lurie, Higher Algebra, Notation 1.3.4.11, Lemmas 1.3.4.12–13 and Proposition 1.3.4.14, printed pp.112–113, for lem-coef-join-translation-resolution. Read online at https://www.math.harvard.edu/~lurie/papers/HA.pdf; not archived under literature/.

WANTED: Lurie, Higher Topos Theory, Examples A.2.9.8, A.2.9.21, A.2.9.29–31 and Corollary A.2.9.30, for the item's Reedy coend argument. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; not archived under literature/.

WANTED: Dwyer–Kan, Function complexes in homotopical algebra, Proposition 4.8 and its diagram, pp.432–433, and Section 7.4, p.437, for lem-coef-kan-enriched-hammock-comparison. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-3.pdf; not archived under literature/.

WANTED: Hinich, Dwyer–Kan localization revisited, Proposition 1.3.5, p.7, for the same new node. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hinich.pdf; its cleanly typeset three-arrow diagram confirms the reading of the scanned DK diagram.

The item's `proof_origin.by` remains `agent`: its expanded contraction/coend argument and passage to the coherent colimit go beyond HA's short model-categorical statement. The new node has no proof, proof dependencies or proof origin.

## Corrections and issues found

The maintainer's return is correct (E5, C4, hidden circularity). The old Step 9 computed pairwise mapping spaces using frames and then asserted that currying made them into a coherent equivalence of categories. Neither a comparison functor nor the composition compatibility required to build one was provided. The old report's claims that HA itself already stated the entire coherent colimit and that the old Step 9 had established it were too strong. HA states a model-categorical homotopy colimit. Our unchanged item also asserts a coherent colimit in the category of spaces, and that additional conclusion requires the independent comparison now cited.

The repair follows the first option requested in the return. DK Proposition 4.8 supplies actual simplicial functors through diagonal enriched hammock categories. The new statement records these maps, their Dwyer–Kan property, and the commutative square on the ordinary category of Kan complexes. Step 9 applies functorial locally Kan replacement and the derived coherent nerve to the complete zigzag. It then constructs the equivalence E by composing/inverting those equivalences. The square identifies Eqi on the ordinary Kan category. The natural trivial-cofibration replacement X → TX identifies Eq with the actual functor X ↦ TX on all objects, arrows, diagrams and transformations, using the componentwise equivalence criterion. Coherence is supplied by simplicial functors and their square, not inferred from mapping-space equivalences.

I read the return at `coord/returns/Q52.md` identifying head ad7fbeb25b and compared the retained ten-step sandbox against the current shared item. The shared item is still unsplit with the same statement and statement dependencies; no newer reviewed split supersedes this work. The sandbox retained the returned Step 9 verbatim before this repair. Packaging with deliver.py rebases only the owned split fields onto current main in its own worktree, preserving current maintainer fields; I run no git command in the shared repository.

The parent `lem-coef-enriched-marked-realization` uses the item's space-colimit assertion in its Step 2. That assertion remains unchanged, so no parent adaptation is needed. Its other uses of the translation maps and first-block equivalence also remain valid.

The new node's statement dependencies have closures of 196 nodes (coherent nerve) and 197 nodes (simplicial hammock definition); the existing hammock-localization closure has 260 nodes in the shared snapshot inspected. None contains this item or `lem-coef-simplicial-model-nerve-localization`. The new comparison is sourced to DK's fractional/resolution argument, not to HA 1.3.4.20, the simplicial-interval/enriched-marked-realization chain, or a rename of its conclusion. It is left unsplit with no proof dependency on those results. The former direct use of `lem-coef-cosimplicial-frame-mapping` in Step 9 is removed; its legitimate indirect use by the generic derived-adjunction theorem remains.

Tool-use issue in the return: `split_report.tool_uses` explicitly declares both off-unit proof statements, `lem-cbc-kan-mapping-homotopy-invariance` (generic mapping invariance and Kan mapping objects) and `lem-cbc-enhanced-functor-cone-calculus` (the componentwise transformation criterion and cocone mapping-space criterion). They are tools, not replacement geometric routes. All other direct proof statements belong to this unit or are Mathlib leaves; off-unit definitions introduce notions. No maintainer-owned `tool_uses` field is set.

## Mathlib searches

For the new node I ran msearch leanfinder with the three canonical comparison functors, and again with “The enriched category of Kan simplicial sets is connected by canonical Dwyer Kan equivalences through diagonal hammock categories to the ordinary hammock localization of simplicial sets at weak homotopy equivalences”. I ran LeanSearch with the simplicial-model comparison phrasing, grep `Dwyer|[Hh]ammock|[Dd]iagonal.*[Ll]ocalization` over Mathlib, and Loogle. The first Loogle query `CategoryTheory.SimplicialCategory, CategoryTheory.Localization` was rejected because its second identifier is unknown; this is explicitly recorded as a rejected query, not evidence of absence. The retry `"hammock"` returned zero hits. No service was unavailable.

I read the returned types and Mathlib's `SimplicialCategory/SimplicialObject.lean:12–45`, `ModelCategory/CofibrantObjectHomotopy.lean:12–100`, and `CategoryTheory/Localization/LocalizerMorphism.lean:12–100`. The hits provide simplicial enrichment, ordinary homotopy-category localization, or ordinary localized functors. They provide none of the enriched-hammock functors or the mappingwise and π₀ equivalence assertions of the proposed node. The new node copies the six actual query/result records from searches.jsonl, with individual verdicts. The item's actual earlier translation searches are retained; its mathematical statement is unchanged.

## Not duplicates

Searches covered the whole DAG by hammock, Dwyer, function-complex, diagonal/localization and source-place phrases, and the whole blueprint using `tools/blueprint_refs.py search` for hammock, function complexes, Dwyer, simplicial localization and Kan. No blueprint statement gives this result. The ancestor command returns `prop-coef-integral-exceptional-adjoint`; the new node adds the item to the inherited via list and names paragraph 2's coefficient-adjunction foundation. The unit and chapter are unchanged.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-simplicial-model-nerve-localization: the latter asserts universal infinity localization for general simplicial model categories but does not supply the three specified diagonal-hammock enriched functors or their strict square; it also depends on this item. The new input is the distinct DK Proposition 4.8 enriched comparison explicitly requested by the return, used together with the existing hammock-localization theorem to derive the needed specialization.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-hammock-infinity-localization: the latter identifies the ordinary hammock coherent nerve with universal localization, but gives no comparison to the enriched category of Kan complexes.

lem-coef-kan-enriched-hammock-comparison vs def-coef-simplicial-hammock-pair: the latter defines the diagonal hammock and its operations; it does not assert that these three canonical functors are Dwyer–Kan equivalences. The new node cites this existing definition.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-hammock-pair-homotopy-invariance: the latter assumes a mappingwise equivalence of enriched pairs before taking diagonal hammocks; the ordinary vertex category to the simplicial category of simplicial sets is not a mappingwise equivalence. It cannot supply the new comparison.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-special-hammock-reduction: the latter compares three-arrow category nerves with individual hammock mapping sets. It does not compare enriched compositions or give these functors.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-cosimplicial-frame-mapping: the latter gives mapping-space computations, not the enriched functor comparison; confusing those conclusions was the returned defect.

lem-coef-kan-enriched-hammock-comparison vs lem-coef-dk-cofibrant-localization-comparison: that node compares free-comonad and ordinary hammock presentations for an ordinary relative category, not the standard simplicial enrichment of simplicial sets or its Kan subcategory.

No Stacks tag states this enriched-homotopical result. No new node restates either clause of the translation resolution; the contractions, diagonal argument, Reedy cofibrancy, Quillen adjunction and cocone identification remain in the item's steps.

## Review by Q52

I read the item, all sixteen now-cited statements, the simplicial-hammock definition needed by the new node, the parent split, the six-functors chapter, the biduality unit and the current ancestor proof paragraph 2. I read the HA translation definitions and model homotopy-colimit proof online, the HTT Reedy/coend passages, DK's Proposition 4.8 with its commutative diagram and Section 7.4, and Hinich's Proposition 1.3.5. No SGA source is used. The item remains a below-unit technical descendant, not the unit's key statement.

1. Step 1 uses the simplicial-set definition. The two ordinal-sum restrictions commute, giving both directions and both augmentations; naturality follows from naturality of X on ordinal operators. This is elementary.
2. Step 2 uses the definition and the extra-degeneracy statement. I checked its augmented identity and four shifted face/degeneracy equations, including D₁h₀; the cited statement supplies exactly the section and homotopy obtained.
3. Step 3 uses realization-finite-limits for the product with Δ¹ and the enhanced-diagram definition for weak equivalences. The written homotopy inverse gives component bijection and based homotopy-group isomorphisms with the required basepoint transport. No Kan hypothesis is used.
4. Step 4 uses those same statements and the simplicial definition. Reversing the first simplicial direction changes its faces and degeneracies to the stated degree-dependent operators. I checked h₋₁=s₀, hₙ=sₙ₊₁, the augmented identity, and both ranges of identities. Coordinate reversal respects the realization quotient; it preserves the augmentation to X_m. No naturality of the contraction in the other variable is asserted.
5. Step 5 uses the exchanged-direction clause of bisimplicial-diagonal-equivalence, exactly the direction proved in Step 4. The last-block restriction is its diagonal map. A weak equivalence is not yet called a coherent colimit.
6. Step 6 uses the Kan model statement, Reedy latching statement and unique nondegenerate decomposition. The latter's uniqueness identifies the latching colimit with the subset of degenerate simplices; hence every latching map is a monomorphism. The degree-zero latching object is empty. Δᵒᵖ is small in the fixed universe.
7. Step 7 is an elementary coend-quotient calculation using the internal functor definition. Its two inverse maps, compatibility with simplicial operators and currying adjunction are written explicitly.
8. Step 8 uses the Kan lifting characterizations, the mono/anodyne pushout-product leaf, Reedy relative matching characterization, and the derived-adjunction statement. Horn lifting and boundary lifting verify the two Quillen classes, including empty boundary at outer degree zero. Only then is the derived adjunction invoked; its coherent unit is part of the cited conclusion.
9. Repaired Step 9 uses the new node for the actual functors a,b,j and equality ahi=jbv; the coherent-nerve statement sends their DK equivalences to category equivalences. Kan mapping invariance supplies locally Kan mapping objects. Hammock infinity localization supplies the universal localization with its actual q. The Kan model statement supplies the natural replacement X→TX. The enhanced cone/functor calculus supplies the componentwise equivalence criterion. Every compatibility now follows from the actual square or natural transformation. The old unsupported frame/currying composition claim is gone. None of these inputs uses the downstream simplicial-model localization theorem.
10. Step 10 uses Kan mapping invariance on Δⁿ→Δ⁰, small-diagram rectification for coherent constants and transformations, the derived adjunction with its unit, and the dual cocone criterion of the enhanced functor calculus. The Step 9 functor equivalence identifies these with spaces coherently. The composite (α⋆1)ι_last=ι_last identifies the resulting cocone with the specified augmentation, degree by degree, independently of α; hence its naturality is also retained.

For the new node, B1–B7 hold: it introduces all categories, universes, marks and maps; uses the existing diagonal-hammock definition; has a statement only; uses single TeX escapes; has an exact source place; and makes no false Mathlib-leaf claim. The maps agree with DK's diagram with the marked degree arrows restricted to iterated degeneracies of ordinary weak equivalences, not all parameterized families of equivalences. For sSet every object is cofibrant and bifibrant objects are precisely the Kan complexes. This is the specialization in the node. The source's functorial-factorization case applies, and its proof route does not use join translations.

I tested the item for X empty, X discrete, n=0, m=0, Δ¹ and the non-Kan ∂Δ². The explicit degeneracies exist in every case, with no horn fillers assumed. In the new statement ∅ is a Kan object (there is no dimension-zero horn condition); Fun(∅,B) is a point and Fun(A,∅) is empty for nonempty A, so no forbidden basepoint or nonemptiness hypothesis is hidden. The constant degree-r arrows are injectively represented by ordinary maps because Δʳ is nonempty. For r=0 all the displayed comparisons reduce to ordinary one-arrow hammocks. Identity arrows reduce to the length-zero hammock, so both sides of the vertex square agree even for identities. The square agrees on a composable pair of Kan maps because both functors concatenate/reduce the same constant hammocks. The mappingwise DK assertion, unlike this elementary square check, remains the cited non-elementary DK theorem; it is not inferred from these small cases. The complete Kan category remains present; no claim is made about arbitrarily restricting the hammock categories to a few objects.

C1 and C4 were rechecked for every step using the statements themselves. `citations.json` quotes their actual text; no proof of a cited node is used as an extra public conclusion. The only new non-elementary fact is explicitly a new cited statement. D1–D5 were checked against the new node and the source route: it is neither a relabelled translation clause nor a circular justification. E1–E6 were checked especially at the model/space passage and its naturality. No imported statement is corrected or weakened. The substantive repairs are the replacement of Step 9, its exact functor compatibility, the new independent comparison dependency, regenerated citations, explicit off-unit tool declarations, and removal of the earlier erroneous review claims.

No source file, shared project file or launcher was edited, no compiler or Lake command was run, no agents were started, and no delivery is to be pushed by this worker. The required dry run is the final gate before handoff to the fresh second reader.

## Second reading by Q52

1. Step 1 checked against HA Notation 1.3.4.11 and `def-weil-pbc-simplicial-set`; ordinal-sum functoriality, both block maps, and naturality are explicit and correct. Verdict: accepted, elementary.
2. Step 2 checked against HA Lemma 1.3.4.12 and `lem-coef-extra-degeneracy-contraction`; all augmented extra-degeneracy identities and index ranges are present. Verdict: accepted.
3. Step 3 checked against the realization finite-limits node and the weak-equivalence definition in `def-cbc-enhanced-diagrams-cones`; the realized contraction gives the claimed weak equivalence without Kan hypotheses. Verdict: accepted, elementary from cited statements.
4. Step 4 checked against HA Lemma 1.3.4.13 and the simplicial identities; reversal, augmentation, endpoint and shifted face/degeneracy equations are written, including the realization homeomorphism. Verdict: accepted.
5. Step 5 checked against `lem-coef-bisimplicial-diagonal-equivalence`; the exchanged-direction hypothesis and last-block diagonal map match, with no premature colimit claim. Verdict: accepted.
6. Step 6 checked against the Kan model, Reedy model, and nondegenerate-decomposition statements; latching objects are identified with outer degeneracies, including degree zero. Verdict: accepted.
7. Step 7 checked against HTT A.2.9.29 and `def-cbc-enhanced-diagrams-cones`; the coend quotient maps, inverse, diagonal identification, and currying adjunction are explicit. Verdict: accepted, elementary.
8. Step 8 checked against HTT A.2.9.29–31 and the cited model/Reedy/pushout-product nodes; the relative matching argument handles (n=0), horns, boundaries, and both right lifting classes. Verdict: accepted.
9. Step 9 checked against DK Proposition 4.8 and its square, `lem-coef-coherent-nerve-comparison`, hammock localization, Kan mapping invariance, and cone calculus; the repaired argument constructs an actual coherent functor equivalence and does not infer composition from mapping spaces. Verdict: accepted after repair.
10. Step 10 checked against HTT Corollary A.2.9.30/A.2.9.31 and the derived-adjunction, rectification, mapping-invariance, and cone-calculus nodes; the unit and last-block equality identify the specified natural cocone. Verdict: accepted.

New node `lem-coef-kan-enriched-hammock-comparison` checked against DK Proposition 4.8 (pp. 432–433), Section 7.4 (p. 437), Hinich Proposition 1.3.5, and its three definition dependencies; it is statement-only, self-contained, has no Mathlib match, and records the strict functor square as well as the three DK equivalences. Verdict: accepted.

Changes made in this second reading: corrected the item node's `created.item` and `created.group` metadata to Q52/item; retained the repaired Step 9 and independent hammock-comparison node; and added this review section with the source, dependency, edge-case, and form checks. No statement, hypothesis, source citation, or proof step was weakened.
