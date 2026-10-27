## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-exact-adjunction-unit-shift-descent.json: item, split into five proof steps, Mathlib searched; no exact match.
- citations.json: seven step/node quotations copied verbatim from the current statements.
- report.md: this report. searches.jsonl is the search command's own log.

Attachments: none. Searches in lean/WeilConjectures for the blueprint tag, mapDerivedCategoryAdjunction, degreewise adjunctions and shift/unit compatibility found useful partial results, but no declaration giving every clause of the item. In particular, CategoryTheory.NatTrans.commShift_mapHomologicalComplex in WeilConjectures/Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean proves compatibility on complexes, while DerivedCategory/Shift/ExactFunctor.lean proves compatibility for isomorphisms and composition comparisons, not this generally noninvertible unit. Neither is an attachment for the whole item.

WANTED: none.

No statement correction or dispute. The blueprint's coherence paragraph does not itself supply the signed computation or descent argument: the item is expressly an extracted obligation. Its statement and original searches are retained. The proof is marked agent-written, expanding that obligation. Exactness and the existence of ordinary derived categories suffice. No SGA source is used.

Nothing remains unfinished for this one-level split. No Lean was written, and no compiler, Lake or build tool was run.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The existing Mathlib leaf lem-weil-pbc-localization-universal-property already supplies both localization of natural transformations and detection of their equality. The elementary cochain computations are steps, rather than new clauses disguised as nodes.

## Searches and blueprint

Read the current item, its parent lem-pur-open-adjunction-shift, the chapter and unit records, and the current fix-prop-coherence.proof.md paragraph concerning units and counits. blueprint_refs.py ancestor returns thm-pur-rational-and-qbar-purity, as the existing ancestry records. Searches for 'unit shift' and 'degreewise unit' return no blueprint matches; 'shift compatibility' returns only def-sf-orientation, which concerns geometric purity orientation rather than an arbitrary exact-derived adjunction. The broader adjunction search and whole-DAG searches for localization/precomposition and unit/shift notions reveal no duplicate of this obligation. same_as remains empty.

All six fresh searches are recorded exactly from searches.jsonl, including their actual hits; the inherited searches were preserved. LeanFinder with the first phrasing returns exact-derived comparison instances and generic derived-adjunction units. The second phrasing returns commShiftOfLocalization and localization comparison interfaces. LeanSearch returns localization_unit_app and shift_unit_app. Loogle returns Adjunction.CommShift constructors and instances. The latter assume compatibility of the adjunction's fixed comparisons; that hypothesis is precisely what must be established here, so shift_unit_app alone cannot close this item. Grep locates the degreewise identity comparison and the generic natural-transformation equality test. These were read in HomotopyCategory/Shift.lean:247–282, Shift/Adjunction.lean:65–87, and Localization/Predicate.lean:270–289. The existing exact-functor factorization node already owns the appropriate Mathlib comparisons.

## Not duplicates

No new-node pairs arise. Reused lem-weil-pbc-exact-functor-derived-factorization and lem-weil-pbc-localization-universal-property rather than creating specialized replacements.

## Review by ND

I read the item's blueprint source fix-prop-coherence.proof.md, its parent open-adjunction proof, and the statements of every cited node. I also read Stacks derived.tex, lemma-right-derived-exact-functor (015F), and categories.tex, lemma-properties-left-localization (04VG). The former gives exact functors on unbounded derived categories computed by every complex. The latter gives localization of functors; it does not by itself state detection of natural-transformation equality. That stronger fact is explicitly clause (3) of the cited existing localization node and is independently realized by Mathlib Localization.natTrans_ext. I did not substitute the weaker Stacks statement for that clause. The existing exact-derived-adjunction definition was checked against OpenTensorNormalizationData.lean:533–545: it localizes the actual degreewise adjunction using the standard factorization squares.

Step 1 uses the exact-functor factorization node for its precise termwise shift comparison. Additivity accounts for negative signs, and identity maps account for naturality and the zero/addition laws. These computations do not require a separate lemma. I checked a=0, a=1 and a=-1, as well as characteristic two and the zero complex: no parity or nonzero-object assumption is used.

Step 2 writes the cochain-map condition as naturality of the original unit at each differential, and compares the two sides degree by degree. Both have component eta at X^{m+a}; the right comparison is the given identity, not a shift structure inferred abstractly from adjunction. Naturality is verified for each component of an arbitrary cochain map. This step uses only the given adjunction and the definitions already introduced in the statement.

Step 3 uses def-weil-abstract-derived-category for Q and its shift comparison; the factorization node supplies both phi_L and phi_P with the stated orientations; def-weil-exact-derived-adjunction explicitly says its units and counits are the localized original ones. Consequently kappa composed with the fixed derived unit is Q(u). I checked domains: kappa maps P_D L_D QX to Q C(P) C(L) X. This step does not infer anything about an arbitrarily specified derived adjunction.

Step 4 uses exactly clause (2) of the factorization node twice. The proof spells out the two naturality moves (for the right shift comparison and phi_P), so the composite comparison equation is not asserted by the word 'transport'. Its source is H_D Q(X[a]) and its target is (QHX)[a]. All terms are isomorphisms of the appropriate categories, and the comparison is the prescribed composite s. This is a direct composition of the two cited squares and naturality, not a hidden new comparison lemma.

Step 5 applies naturality at t_X, then gives the full five-line equality and cancels only t_X and kappa_X[a], which are isomorphisms. It never cancels the unit, which need not be invertible. The equation first holds at QX, and clause (3) of the localization node extends equality of the two natural transformations to every derived object. Their common source is the shift functor, and their common target is shift after H_D. The category can be unbounded, and Q is a localization at quasi-isomorphisms by the cited derived-category definition. There is no unsupported use of a small indexing category, injective preservation, monoidality or a resolution.

Against B–E: all objects are introduced in the item or locally in its proof; every non-elementary input is an existing cited statement, not a source tag alone or an argument from a node's proof; quotations in citations.json are literal substrings. No new node, route change, extra hypothesis, weakened clause or circular reference was introduced. The longest step is below 2000 characters. The proof_origin correctly marks the expansion as agent-written. No mathematical correction was needed; the missing localization argument was filled explicitly.

## Repair of returned delivery 8d47cecc2fb

The return was a landing-state mismatch: the approved side completion had not been promoted to the live DAG. I retained that delivery's five-step argument, all citations and all recorded searches, and compared the retained node with the current read clone before redelivery. The current live item is unsplit, has no reviewed or Lean completion record, and has no released repair note. Its statement, statement dependencies, source, blueprint ancestry, title and creation metadata agree with the retained node; the differing fields are exactly status, proof, proof_deps, proof_origin, mathlib_searches and split_report. The delivery tool reconstructs the commit on the current server base, so this submission does not carry forward the old side-completion state.

I re-read all four cited current statements, including those whose changes could otherwise invalidate the old proof. The exact-functor factorization still provides the termwise identity comparison and clause (2)'s localization/shift square; the abstract-derived-category definition still supplies Q and its shift comparison; the specified exact-derived-adjunction definition still fixes the localized original unit; localization universal property clause (3) still detects equality after precomposition with Q. All seven retained citation quotes are literal substrings of these current statements. Thus no dependency substitution, statement correction or mathematical change to the approved proof is needed. I checked the composite square in step 4 and the cancellation chain in step 5 again with these orientations; only isomorphisms are cancelled, never the unit.

The refreshed project-source search also found CategoryTheory.Adjunction.commShift_mapHomologicalComplex_unit and CategoryTheory.Adjunction.commShift_mapDerivedCategoryAdjunction in lean/WeilConjectures/CategoryTheory/DerivedCategory/MapDerivedCategoryAdjunctionShift.lean (lines 34 and 90). The former covers the cochain clause. The latter has additional monoidal, countable-colimit, tensor, functorial-flat-resolution and K-injective-resolution hypotheses (lines 72–86), absent from this item's general statement. Consequently these declarations do not give an attachment for every clause under this item's hypotheses. The earlier attachment-search paragraph records the previous search state; this paragraph updates it for the current library. No fresh Mathlib search question or new node was introduced, and the six recorded search outputs were read and retained.

The initial current-base dry run passed at b3b7f1b72b5. This report and the item's split_report now explicitly record the current-DAG repair; a final dry run and push follow this update. No source, launcher or repository file was written.
