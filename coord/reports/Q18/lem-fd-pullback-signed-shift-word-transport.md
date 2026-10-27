# Q18: lem-fd-pullback-signed-shift-word-transport

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-pullback-signed-shift-word-transport.json: statement, split in nine steps; no exact Mathlib match for the whole statement. The statement and its statement dependencies are unchanged.
- citations.json: one verbatim statement quotation for every step/node pair (30 entries).
- searches.jsonl: actual msearch output log; existing item searches were retained and this turn's actual searches appended to mathlib_searches.
- report.md: this report. write_split.py is sandbox-only preparation, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. The existing generic lemma lem-a1-strict-roos-shift-localization gives the cone sign, coherence, inclusion normalization and localization, so creating another node for these facts would duplicate it. The finite-word substitution and coherence inputs also already exist.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, ShiftCoordinates, ShiftDescent, signed shift spellings and shift/word combinations, and read the broader Roos search results. Generic project Roos comparisons do not state all clauses of this item. No project declaration was claimed as finished merely because it exists.

## WANTED

None. The current blueprint file and the local Stacks files used here are available. No external document, SGA source, Lean edit or compiler was used.

## Audit findings and changes

The sandbox initially contained only dispatcher brief markers: no item, split, report, search log or delivery outcome. Process inspection showed no active deliver.py invocation for this item. There was therefore no pending delivery to repeat. I copied the current unsplit live node and checked that no released repair note exists.

The item had a detailed statement but no proof. The signed coordinates and finite-word realization formulas were not themselves missing mathematical lemmas: existing DAG nodes state their general versions. The supplied hypotheses deliberately retain complete intermediate realizations and actual primitive/counit normalizations. I kept those restrictions, and did not replace entire quotient-system morphisms with statements about their separate evaluations. No statement dispute or source error was found.

The actual new searches were: LeanFinder on the normalized Roos/shift/coherence statement; Loogle on CochainComplex.mappingCone.shiftIso; grep for roos|mappingCone.*shiftIso in Algebra/Homology; a second grep for def shiftIso|shiftIso_hom|shiftIso_inv in the Pretriangulated file; and LeanSearch on a differently phrased augmentation/finite-word question. All services answered. I read the returned generic cone-shift declaration in Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:347 and its formulas through line 375. It supplies a general cone-shift isomorphism, not the entire normalized pro-etale pullback/counit statement. The single-file grep prints line numbers in its file column; the recorded results explicitly describe that output, rather than presenting the numbers as filenames. Searches are recorded with their actual tool and query, without inventing a query or a failed-service verdict.

Blueprint searches used blueprint_refs.py ancestor for this item and search for signed, cone, Roos and finite word, across the whole imported blueprint. DAG searches used the notions ShiftCoordinates, ShiftDescent, Roos/shift/localization and K-flat/localization. No imported blueprint node states this whole conjunction. The nearest ancestor remains def-fd-trace-function, with its existing via list. Its final coefficient-category sentence is the place being supported; no chapter or unit route is changed. This item is not the unit's key statement, so no realization record is edited.

## Not duplicates

No new nodes. In particular, the existing generic signed-Roos localization, whole-system substitution, and mixed-coherence nodes are cited, not replicated. A dependency traversal verified that the generic shift, operation-descent, localization, scalar-completion and word-coherence inputs do not reach this item.

## Review by Q18

I read coord/delivery-errors.md B through E in full, the standing stage-1 brief, the chapter and unit records, the three blueprint levels in SETUP.md, GOAL.md, and the current blueprint source literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md. The source's final sentence asks for the PBC coefficient-category presentation; the extra normalization argument is explicitly agent-written. For the mathematical source I read Stacks derived.tex definition-cone (Tag 014E) and sites-cohomology.tex lemma-derived-limit-is-ok (Tag 0941), including its K-injective tower proof and ordinary-limit inclusion. These explain why the sign belongs on the shifted product and why the inclusion's shifted coordinate is zero. There are no new nodes needing independent source reviews.

For step 1 I opened def-pur-integral-derived-operations, lem-weil-proetale-countable-products-exact and def-fd-integral-pullback-shift-coordinates. The first specifies the actual finite quotient transitions and termwise Roos construction, the second explicitly covers any completed coefficient sheaf on the small pro-etale site, and the third specifies levelShift and productShift. Thus this step may identify the shifted transitions, not merely their derived evaluations. Its exact-product hypothesis is supplied for R_{E,U}; it is not inferred from a definition of the pro-etale site.

For step 2 I opened lem-a1-strict-roos-shift-localization and the coordinate definition. The former really states the reversed-coordinate sign, coherence, inverse, naturality and the normalized inclusion square, for strict towers in an abelian category. It has no geometric restriction to the A1 schemes suggested by its id. The step also writes both differentials and checks the sign directly. For r=0 the map is identity; for r=1 and r=-1 it changes only the shifted coordinate; composition of opposite shifts gives identity. If 2=0 the sign becomes identity, still satisfying the differential calculation. Zero towers and augmentations (0,z) are fixed.

For step 3 I opened lem-weil-strict-roos-comparison, lem-a1-strict-roos-shift-localization and def-pur-kinjective-complex. The comparison statement actually gives rho=[j]^{-1}[H(q)], naturality and resolution independence; it is not just existence of a homotopy-limit object. The generic shift lemma supplies the j square. The step verifies that q[r] has injective terms and is K-injective by shifting back an acyclic source, so the canonical Rlim shift is computed on this eligible resolution. Substituting the two equations proves the normalized rho square; no unproved uniqueness of cones or of maps from their level projections is invoked.

For step 4 I opened def-pc-kflat-complex, def-pc-tensor-complex-sheaves, lem-pur-integral-operations-well-defined, lem-weil-pbc-localization-universal-property, def-fd-integral-pullback-shift-coordinates and lem-weil-pbc-integral-stratified-perfect-characterization. The good-class condition is preserved by reindexing and the signed total-tensor shift isomorphism. The well-definedness theorem states the natural comparisons with the displayed construction on good representatives, not just independence of objects; the localization statement explicitly descends natural transformations and their equations. The displayed conjugation is precisely ShiftDescent, with the eta factors retained. The characterization statement gives shift closure of the full integral categories under the exact noetherian/finite-dimensional/invertible-ell hypotheses used here. No additional finite-type-over-a-field assumption is imported.

For step 5 I opened lem-fd-scalar-pullback-realization-identification, lem-fd-normalized-integral-completion-comparison and the generic shift lemma. The first identifies the actual PBC scalar arrow and its framework cone map, including chi conjugation; the second explicitly states shift compatibility of chi and its inverse. I wrote the equality of the two diagonal/sign composites. An arbitrary degree-zero d_n need not be invertible; neither this calculation nor its localization uses that. Quotient coefficient maps are not assumed flat.

For step 6 I opened lem-fd-pullback-augmentation-counit-matching, lem-fd-pbc-completed-compositor-normalization, lem-fd-scalar-pullback-realization-identification and lem-trf-counit-realization-substitution. Their statements respectively supply the same simultaneous whole-system counit model, the actual unit/compositor normalization, the actual scalar normalization, and the formula for r and every specified realized comparison, including whiskering. All hypotheses of substitution are retained: normalized systems, constructible-complete intermediate realizations, and the same chosen counit. The finite-word induction starts at the empty word; its composite step displays the cancellation at the common intermediate r. Thus the proof does not disguise an assertion that level evaluations are faithful.

For step 7 I opened lem-trf-quotient-system-mixed-coherence and the substitution theorem. The former explicitly states the entire-diagram composition, unit, equal-scheme-map and scalar tower equations, before realization. The latter explicitly gives the chi-conjugated ordinary tensor associator and multiplication/completeness equal-field unit. Therefore the elementary operation here is conjugating already stated equations, rather than proving those equations from a definition. Taking E=L=M or inserting identity scheme maps uses their stated unit formulas; the empty-word case reduces to the identity. Reassociation of three or more maps uses the same full-system associativity, not an unstated claim about two maps.

For step 8 I reread augmentation/counit matching, signed-Roos localization, word substitution and scalar-completion shift compatibility. The first actually identifies epsilon as [q]^{-1}[Delta lim I -> I], rather than merely naming an adjunction. Reindexing q and its limit projections gives its shift compatibility; the sign fixes every zero-coordinate augmentation. Degree-zero balanced tensor maps commute with the same sign. The recursion for r then proves the word shift square, including inverses and whiskerings, from the primitive squares. The simultaneous model hypothesis is essential here and is present in the item.

For step 9 I opened def-weil-rationalization-karoubi and the two whole-system statements. Raw localization has the same objects and scalar-localized Hom, with induced shifts; f maps to f tensor 1 and composition is bilinear. This directly preserves the proved equations. I displayed the inverse conjugation formula and noted how to obtain the inverse shift square by multiplication. The coherence and substitution statements expressly avoid finite Tor-amplitude and flatness of quotient scalar maps; those absences have not been replaced by hidden hypotheses.

I checked B's statement-only/new-definition/duplicate/leaf obligations: there are no new nodes and no purported new leaf. I checked C1 and C4 by opening each cited statement; citations.json contains the full verbatim statement so that every used clause is visible. I checked D by leaving the actual coordinate, descent and cancellation arguments in the item, without moving a clause into a renamed child. I checked E with the small cases above and by keeping the ambient and complete categories distinct. All nine proof steps have fewer than 2000 characters, so there is no long step hiding an unexamined auxiliary lemma. The report declares the off-unit generic tools in split_report.tool_uses; no maintainer field is set.

## Unfinished work

None in the stage-1 split. No claim is made to have written a Lean proof. Required server dry run and direct push follow this report.
