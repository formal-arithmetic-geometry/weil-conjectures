# Stage-1 report: lem-sfb-noetherian-affine-atlas-relation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-affine-atlas-relation.json: existing statement split into four steps; no Mathlib match for the complete algebraic-space assertion.
- citations.json: one verbatim statement quotation for each node used in each step.
- searches.jsonl: six actual searches made with the required msearch command, including two different semantic phrasings.
- report.md: this report and the author's source review.

There are zero new nodes and zero new Mathlib leaves. All substantive inputs already have nodes. The statement, its statement dependencies, and the inherited provenance were retained.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag and the notions Noetherian atlas/groupoid found no project declaration proving the item. The relevant Mathlib hits concern schemes, not algebraic-space presentations, and do not attach this item.

## WANTED

None. The necessary Stacks sources are present locally.

## Problems found and changes

The item was statement-only, not a checked split. Its atlas is already chosen, so the existence theorem 03H6 is not needed as a proof dependency. No separatedness of X over S is needed. The crucial compactness input is absolute quasi-separatedness of X, together with the existing qcqs fibre-product node, not an assertion that U times over S U is affine or quasi-compact over an arbitrary S.

The latest blueprint's direct-images proof is a high-level preservation/compactification argument; it does not state this local atlas prerequisite separately. I read the latest unit and direct-images proof and retained the inherited branch provenance. The blueprint ancestor tool returns None for this chain, consistently with the inherited blueprint.from.node = null. I did not invent an ancestor or alter the unit's route.

I did not create nodes for the groupoid laws, local Noetherianity of the charts, or the concluding conjunction: the operations and arguments are explicit proof steps. I reused the existing general fibre-product and permanence nodes rather than creating versions of the item's clauses. No source error or statement dispute was found.

## Mathlib searches

The two LeanFinder queries returned IsNoetherian/IsLocallyNoetherian scheme definitions, affine Noetherianity and quasi-separatedness lemmas, and etale scheme infrastructure. Loogle on IsLocallyNoetherian and Etale returned no hit. The source regex for algebraic spaces and etale/Noetherian combinations returned no hit. LeanSearch returned the affine-open Noetherian criteria and scheme quasi-separatedness. I read the relevant local Mathlib Noetherian and Etale source passages. These do not state the complete assertion for an arbitrary algebraic space X. The exact queries and their actual logged results are in the item's mathlib_searches; no search was invented. The inherited creator's queries were rerun as this item's own searches, and the new results replace the inherited result summaries.

## Not duplicates

No new nodes were created. Existing generic results are cited directly, including both clauses of Tag 073B through their already separate nodes.

## Tool uses

lem-trf-space-chartwise-etale-permanence is a generic off-unit tool for composition of etale maps with scheme source. lem-weil-pbc-affine-scheme-qcqs is the generic scheme fact making U qcqs. Their use is declared in split_report.tool_uses. The other theorem inputs are already in the item's unit. These citations expand a supporting prerequisite; they replace no step of the unit's prescribed route.

## Review by Q20

I read spaces-cohomology.tex Tag 07UV, especially the paragraph choosing affine U and the relation R. I checked its suppressed geometric prerequisites against spaces-properties.tex Tag 03EA and its following distinction between Noetherian schemes and Noetherian spaces, the etale definition/composition passages 03FR and 03FT, the quasi-separated criterion 0AHR, and spaces-morphisms.tex Tag 073B, including its proof. I also read 03H6 to verify that it concerns existence of an atlas, which the item already assumes. For the groupoid I read groupoids.tex definition-groupoid (0231), its axioms and equivalence-groupoid (0233). There are no new-node sources to audit.

In step 1 I checked def-trf-algebraic-space literally says that representable etale maps have scheme pullbacks whose projections are etale. This supplies R as a scheme and both etale projections without a missing base-change lemma. def-weil-etale-morphism includes flatness, so no separate flatness theorem is being smuggled in. The local Noetherian assertions are direct instances of the definition stated in the item's hypothesis. To use it on R, I explicitly cite lem-trf-space-chartwise-etale-permanence: its statement supplies both equivalence with representable etale for scheme sources and composition. Thus R to X is an etale chart. It need not be surjective to apply the stated definition. I verified that this tool's dependencies do not use the item.

In step 2 I opened the statements of def-pc-fibre-product and def-a1-scheme-groupoid-laws. The proof uses precisely their universal property and axioms, with the representable sheaf relation supplied by def-trf-algebraic-space. I wrote the identity, inverse, composition and associativity computation, using t(a,b)=a and s(a,b)=b so that c(a,b)=a composed with b agrees with the cited convention. The operations are morphisms by the universal property, and their equations hold on all tests by their displayed components. This is an elementary calculation, not a cited-but-unproved groupoid theorem.

In step 3 I opened lem-weil-pbc-affine-scheme-qcqs and lem-sfb-qcqs-space-fibre-product. The former says both properties needed for U. The latter requires all three of A, B, C to be qcqs; these are U, U, X, respectively. X satisfies both properties by its Noetherian hypothesis. The statement explicitly permits arbitrary ambient S, so there is no hidden separatedness of S or X over S. Since step 1 proved local Noetherianity for both schemes, their quasi-compactness gives ordinary scheme Noetherianity. I checked the affine qcqs source assertions in Algebra 00E8 and Schemes 01KN as well as the supplied node statement.

In step 4 I opened lem-sfb-space-qcqs-permanence. Its exact hypotheses are quasi-compact source and quasi-separated target, with quasi-separated source for the second conclusion. Step 3 provides all three for each of s and t. Its scheme-test definitions agree with the quasi-compact and quasi-separated morphism definitions in the item, so this proves precisely the missing projection clauses. Every theorem used is named by a cited node, and every citation quote is copied verbatim in citations.json.

For edge cases I checked the empty space and empty affine atlas, disconnected affine U, and nonseparated schemes such as the doubled affine line with the finite disjoint union of its standard charts as U. The groupoid operations and compactness argument cover them without claiming R affine. Dropping X's quasi-separatedness would invalidate the compactness input: the locally Noetherian affine-line translation quotient by Z, discussed immediately after Tag 03EA, explains why this hypothesis must be retained. Surjectivity of the given atlas is allowed throughout but is unnecessary for these geometric properties. No argument uses a Noetherian product over S or finite type of S. All four steps are below 2000 characters; none hides an inline auxiliary theorem.

## Unfinished work

No mathematical part of this one-level split remains. The existing unsplit dependencies remain their own queued items; I have not split or edited them. Delivery validation is recorded below after the required server dry run.

## Delivery validation

The resumed required server dry run exited successfully: `OK (not pushed)` at `343d5d12580`. On resumption I rechecked all nine citation quotations against the current repository statements, read the cited permanence statements and Stacks passages again, and confirmed that the sandbox retains the live statement unchanged. The only report correction was counting the six logged searches accurately. A final dry run is run after this report correction, before the direct push.
