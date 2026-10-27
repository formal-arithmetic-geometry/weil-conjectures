# O4: lem-sfb-kummer-source-coherent-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kummer-source-coherent-descent.json: statement, split; unchanged statement, ten proof steps, 21 reused proof dependencies. No new nodes and no Mathlib leaves.
- citations.json: verbatim statement quotations for every step/node pair.
- searches.jsonl: actual msearch.py results, retained without alteration. write_split.py is sandbox-only preparation, not part of the delivery.

## Attachments

None. Searches for the exact blueprint tag and for Kummer descent/coherent boundary comparisons in lean/WeilConjectures found no declaration proving the item. The KummerCover.lean declarations concern towers of a unit and their site covering, not this all-continuous coefficient boundary theorem. No upstream sorry declaration is treated as finished.

## WANTED

WANTED: an external proof of the all-continuous norm-topological Kummer boundary calculation and its compatible resolution formulation, for lem-sfb-kummer-source-coherent-descent. The current blueprint direct-images paragraph (3) supplies the route, but not this theorem. The proof is therefore marked agent-origin. No SGA source was used.

## What was missing and what changed

The item was statement-only. Its chart existence assertion is already in lem-sfb-tame-root-tower-extension; its one-term boundary computation is already in lem-sfb-root-tower-boundary-acyclicity. Recreating either would be a duplicate. The statement and its statement dependencies are unchanged, including the inherited blueprint.from.node=null and via chain. I filled the proof, proof dependencies, split report and same_as search result.

The imported item explicitly requires coherent resolutions. It would be insufficient to give independently natural isomorphisms in the triangulated category. Steps 6-7 instead retain the actual unit/counit/evaluation cospan: invert the puncture unit after localization, restrict full-source sections to the zero-root fibre, and apply free-generator evaluation. Functorial nonnegative resolutions of this diagram retain its operators. The proof does not use a claimed ability to lift arbitrary commuting triangles in a derived category. The actual augmented Cech resolution is reused, rather than constructing a new descent theorem.

The coefficient change argument uses finite bases and ordinary tensor on finite sums. It does not require flatness of C_E -> C_Omega, a completed coefficient field, replacement by finite-subextension-valued functions, or scalar extension commuting with derived direct image. Both fields use the same geometry.

## Searches and not duplicates

Before writing the split I searched the whole DAG by Kummer, equivariant extension, coherent cosimplicial comparison, Cech descent and derived resolution terms, and ran blueprint_refs.py ancestor and searches for Kummer, root tower, coherent Cech, Kummer source, functorial resolution and derived mate. No blueprint node states this exact coherent source theorem. The ancestor command reports the inherited null ancestor, which I have retained rather than inventing a blueprint id.

The main reusable nodes are tame-root-tower-extension, root-tower-boundary-acyclicity, derived-cech-image-totalization, cech-injective-column-model, condensed-derived-invariant-bar and the generic resolution nodes. tame-stratum-kummer-descent has a related larger ordinary boundary calculation, but its statement does not supply the explicitly coherent augmented first-quadrant comparison required here; its proof was read for comparison, not cited as an unstated stronger theorem. kummer-supported-nerve-descent additionally compares a supported inner unit and would introduce an irrelevant and stronger conclusion. kummer-partial-nerve-naturality additionally asserts unique extension of maps and iterated group comparisons; none of that is needed for the present source construction. No new node was created, so there are no new/existing duplicate pairs.

I ran all item searches through msearch.py, read the logged hits and retained the searches. The two geometric phrasings returned ordinary Rep bars, ContinuousCohomology, scheme module restriction and etale definitions. I read Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean at its inhomogeneous differential: it uses ordinary Rep modules and functions, not internal condensed derived Hom or pro-etale boundary restriction. The later resolution queries returned general localization/right-derivability and adjunction infrastructure; none states the geometric assertion. No matching Mathlib declaration is claimed. Every new entry in mathlib_searches corresponds to an actual log entry; no unavailable search is recorded as absence.

## Review by O4

I read the current main-20261015 direct-images proof paragraph (3), the chapter and unit records, and the exact statements of all 21 cited nodes. For the generic resolution argument I also read Stacks derived.tex, Tag 0141, label lemma-functorial-injective-resolutions: its cokernel/injective-embedding construction applies functorially, with the same lower bound. For evaluation and restriction I read sites-cohomology.tex Tag 08J7, section-internal-hom (including equation-internal-hom and its K-injective model), Tag 08FI, lemma-restrict-K-injective-to-open, and Tag 0D6E, lemma-derived-pushforward-composition. These are supporting sources for the existing nodes, not independent uncited black boxes in the proof. The proof follows the blueprint's open-image route and remains agent-origin. There are no new nodes requiring their own source review.

Step 1 uses exactly the chart, root torsor, equivariant extension and boundary representation clauses of tame-root-tower-extension. Its I=J hypotheses match the item's strict-local Kummer tameness; no general notion of tame ramification is substituted. Step 2 uses the definition of lisse as locally finite free and pulled-back coefficients. An E-basis makes scalar extension and the continuous-function module identities literal finite-coordinate calculations. No direct-image fact is used in this elementary step.

Step 3 iterates the supplied torsor scheme isomorphism. Both directions are written using consecutive vertices and unique ratios. The first vertex deletion changes the coefficient trivialization, interior deletions multiply ratios, and repetitions insert 1. Commutativity of G_J reconciles the order of the products with the usual bar convention. This verifies scheme maps on the full profinite family, not just a bijection of points. It is an elementary use of the cited torsor isomorphism, not a new node.

Step 4 uses coefficient-sections-localization only for the slice and coefficient identifications; ringed-derived-slice-localization supplies the derived direct-image identification and normalization. Derived-cech-image-totalization supplies the actual augmented first-quadrant descent. Its exact inverse-image hypothesis holds for the Cartesian pulled-back coefficients; the root covering is applied on U^circ before restriction to the stratum. This order avoids the invalid empty cartesian square at the boundary.

Step 5 uses the full boundary-acyclicity statement, including its family naturality, rather than its proof alone. All objects substituted into it are named. The lisse Omega-extension and its finite-dimensional E-boundary model were verified in step 2. Its full-family automorphism clause gives the first action face. The remaining faces and degeneracies are its parameter naturality applied to the explicit formulas of step 3.

Step 6 spells out the comparison cospan whose maps are actual units, counits and evaluation, not an arbitrary collection of derived isomorphisms. Cech-injective-column-model supplies the geometric coherent model. Root-tower-puncture-invariance supplies the invertible open unit, integral-fibre-section-specialization supplies the precise boundary counit adjunct, parameter-root-integral-nil-fibre verifies its integral/nil-fibre hypotheses, and profinite-constant-derived-functions supplies the normalized function comparison. These are general inputs about the full source, individual terms and arbitrary profinite parameters, rather than new clauses restating the whole item.

Step 7 resolves that specified cospan as one small diagram. Ringed-site-grothendieck-abelian verifies the category hypothesis, grothendieck-functorial-injective-embedding supplies the functorial embeddings, functorial-bounded-injective-resolution supplies the same nonnegative resolution functor on all arrows, and derived-injective-resolution-naturality supplies its canonical comparison on the indexing diagram. Free-parameter-evaluation-coherence supplies the simultaneous parameter/module-map square at the function end, including matrices varying over profinite slices. First-quadrant-total-column-comparison gives invertibility after totalization. I checked that this argument uses the specified natural transformations, and never asserts strictifiability from equality only in the triangulated category. Every operator is retained before taking the total. A further resolution index still has nonnegative degrees and finite diagonals.

Step 8 uses exact point pullback from profinite-point-pullback and the finite-diagonal nature of descent. The bar theorem identifies exactly the internal derived Hom terms and group maps already constructed. Its invariant inclusion and the degree-zero restriction normalization of the boundary/descent theorems specify the augmentation; H^0 by itself is not being used to characterize a derived arrow. Step 9 cites the naturality clauses of those three theorems and cech-augmentation-normalized-naturality for resolution independence with the augmentation retained. It applies to maps already supplied on equivariant extensions; it asserts no unproved ability to extend arbitrary puncture maps. Step 10 checks the edge cases directly.

I tested J empty (identity tower, trivial group and split identity nerve), an empty stratum (empty covering), empty chart, rank zero, and a nontrivial continuous action (the first bar differential is g*m-m, not zero). I checked that the zero-root fibre is used through a surjective nil closed immersion rather than falsely identifying its nonreduced scheme with the reduced stratum. I checked the lack of completeness of Omega causes no extra assumption in the finite-basis scalar calculation. I checked all citations against their statements, not just names or docstrings; citations.json contains those statements verbatim. No cited dependency reaches this item, so the additions create no cycle.

I checked delivery-errors B-E point by point: no new-node format/search issue, all notions remain in the unchanged statement dependencies, no off-route theorem is substituted for the unit, no clause is moved into a new node, no unsupported totalization of arbitrary unbounded products, and the maps/naturality are written explicitly. Every non-elementary step is shorter than 2000 characters. The elementary steps are finite-basis tensor, iteration of a supplied torsor isomorphism, and the explicit zero/trivial cases. Generic off-unit tool uses are declared in split_report.tool_uses; they supply localization/resolution tools, not a change to the unit's route.

## Unfinished work

None for this one-level stage-1 split. Existing dependencies retain their own proof obligations. Independent maintainer review remains required after delivery.

## Previous validation (returned delivery)

The required deliver.py --no-push finished with exit 0 and printed OK (not pushed) at dc757209cc8: preflight passed. No overlapping delivery command was started. The prepared split has 10 steps, none longer than 2000 characters, and introduces no new nodes or Mathlib leaves.

## Review by O4 — repair of landing refusal L

The returned split was approved mathematically, but landing refused the stale statement of lem-sfb-cech-augmentation-normalized-naturality. I began with the required dry run; it exited 1 and identified exactly its step-9 quotation. I compared the retained item and citations with the current read-only DAG: the live item is still unsplit, its statement and statement dependencies agree with the retained delivery, and all other step/node quotations remain verbatim. I reread all 21 cited statements, the current main-20261015 direct-images paragraph (3), and the chapter/unit records. The prior proof, source references, report and search log are retained. No new searches or nodes are needed for this unchanged statement.

The revised cited theorem explicitly uses canonical coherent element-site restrictions; step 6 already obtains that model from cech-injective-column-model. It explicitly assumes the refined cover remains an epimorphism; our refinements are covering refinements of the supplied root torsor, so this holds. It also corrects the type of the counit-normalization assertion: project to the Cech-zero column, express that component as f_*(eta_I), and take the identity transpose of eta_I on the source before applying f_*. Step 9 now spells out these substitutions and this restriction. Resolution independence concerns the whole augmentation; the counit assertion concerns its projected column-zero component. Applying exact boundary inverse image preserves these equalities and the finite-diagonal total. Thus the old informal sentence has been substantively repaired, not merely re-quoted. The revised statement of the cited theorem is copied verbatim into citations.json.

I rechecked B-E for the repair: every cited claim is still supplied by its statement; no new node restates a clause or duplicates an existing node; the statement, coefficient category and route are unchanged; the refinement epimorphism and exact inverse-image hypotheses are explicit. The empty-stratum, empty-J and rank-zero cases remain as in step 10. All non-elementary steps remain below 2000 characters. No Lean or compiler was used and only the sandbox was written. The delivery tool will rebuild the repaired commit against the current DAG before the final push.

## Repair validation

The repaired deliver.py --no-push exited 0 and printed OK (not pushed) at 585f2e8f65a: server preflight passed. All 27 citations match current statements and all 10 proof steps are below 2000 characters. The dry run completed before the push was started. The earlier dc757209cc8 validation above records the returned attempt only. No new nodes or Mathlib leaves.
