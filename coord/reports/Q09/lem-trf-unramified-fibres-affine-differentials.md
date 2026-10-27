# Stage-1 report: lem-trf-unramified-fibres-affine-differentials

## Files written

- dag/nodes/sec-trace-formula/lem-trf-unramified-fibres-affine-differentials.json — statement, split into four steps; no Mathlib match for the whole statement.
- citations.json — nine verbatim statement quotations, one for each step/node pair.
- searches.jsonl — the search command's unmodified execution log.

No new nodes and no new Mathlib leaves. The unchanged statement uses only existing notions. The new proof has step lengths 347, 610, 797 and 635 characters; no step exceeds 2000 characters.

## Attachments

None. The item tag has no declaration under lean/WeilConjectures. Searches for the unramified/fibre and affine-fibre notions found related lemmas, not a finished declaration giving every clause. In particular the affine fibre sections theorem concerns only the section-ring comparison. No compiler or build was run.

## WANTED

None. All mathematical sources used are already present under literature/stacks-project.

## Findings and changes

The imported item is true and its statement is unchanged. It previously had no proof. Its cover clause is already the explicit definition of locally finite type in def-weil-finite-type-morphism, so no new affine-chart lemma is needed. The pullback and restriction facts also already have nodes. The proof spells out the residue-field and projection compatibility instead of hiding them in an unexplained identification.

The inherited Mathlib searches were preserved. Five further searches were executed with msearch.py, logged under this sandbox and read: two LeanFinder phrasings, Loogle, grep and LeanSearch. All services answered successfully. The APIs for finite-type appLE, affine fibre comparison and formal unramified appLE supply different parts; no single result specializes in one line to the whole covering-and-fibre assertion. Read Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:43–54, AlgebraicGeometry/Fiber.lean:79–93 and Morphisms/FormallyUnramified.lean:53–79. Existing Mathlib leaves are reused, not copied into new nodes.

## Not duplicates

No new nodes. Reused lem-weil-pbc-fibre-product-affine-spectra (01JQ), lem-weil-pbc-open-fibre-product (01JR), lem-weil-pbc-affine-open-stalk-localization (01HV), lem-weil-pbc-unramified-base-change-open (02G6 restriction), and lem-weil-pbc-unramified-ring-map-iff-unramified-affine (02G6 affine criterion). DAG searches by tag and concept, and blueprint_refs searches for unramified, fibre product and affine fibre, found no existing blueprint statement equal to the entire item. blueprint.same_as remains empty.

## Review by Q09

I read the item's source in morphisms.tex: 01T1 (definition-finite-type), 01T2 (lemma-locally-finite-type-characterize), 02G6 (lemma-unramified-characterize), and 02G8 (lemma-unramified-etale-fibres). I also read the affine-product and open-product statements and proofs in schemes.tex, 01JQ and 01JR. These are the actual local geometry underlying the ordinary-fibre criterion, and do not change the chapter or unit route. There are no new nodes requiring additional sources. The chapter sec-trace-formula and unit sk-i-curve-zero were read; this item is a subordinate scheme-theoretic reduction in the normal-cone branch, not the unit's key theorem, so its realized fields are untouched.

Step 1 uses the complete statement of def-weil-finite-type-morphism: it explicitly gives an affine cover over EVERY affine target open by finitely generated algebras. The step simply chooses this cover. It never asserts that the cover is finite or that h is quasi-compact.

Step 2 uses lem-weil-pbc-affine-open-stalk-localization, whose clause (c) identifies the stalk with the localization via the actual germ map. I checked the R-algebra compatibility and used the residue-field definitions to take the quotients by the maximal ideals. The canonical residue-field morphism in def-pc-scheme-fibre is induced by that same quotient of the stalk, so on R it sends each section to its germ modulo the maximal ideal. This proves the compatibility needed for Spec kappa(p) to be the chosen point morphism. There is no additional theorem hidden in taking the quotient of a ring isomorphism. The definition citations and the localization clause are quoted verbatim in citations.json.

Step 3 uses exactly the statements of lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. I checked both applications of the former: h(U_i) lies in V by construction and the residue point map lies in V by step 2; the other source open is the whole Spec of the residue field. Its range formula therefore gives precisely the inverse image of U_i, not merely an open subset of it. The second application with the whole U_i identifies the fibre over V with the fibre over B. The affine-product node explicitly states both projection formulas, so its comparison is over the specified residue-field spectrum. No claim that intersecting arbitrary affine opens gives an affine open is used.

Step 4 uses only clause (2) of lem-weil-pbc-unramified-base-change-open, whose statement I opened and read; its input is the unramified fibre assumed in the ITEM, not a hypothetical unramified h. The open D and the whole target meet that clause's hypotheses. The affine criterion node explicitly gives an equivalence with finite generation AND zero differentials for arbitrary commutative rings; its forward direction gives the asserted zero module for C. It is applied after the base-compatible comparison, so it is the correct kappa(p)-algebra structure. The off-unit open-restriction node is declared as a generic tool use in split_report.tool_uses. No other off-unit nonleaf result is used.

I checked delivery-errors B–E against these statements: no new node restates a clause or hides a proof; no unsupported fact is attributed to a definition; no source tag substitutes for a cited non-elementary theorem; every node cited has a verbatim statement quote. proof_deps is exactly the union of uses. There is no dependence on the ordinary-fibre parent or its differential-vanishing sibling, hence no upward cycle. Steps 1 and 2 are elementary selections and quotient/map computations from the cited statements; steps 3 and 4 are marked non-elementary.

Small cases checked: empty h^{-1}(V) permits an empty cover; the empty affine chart has A_i=0, tensor product zero, empty open fibre and zero differentials. If R=0 there are no primes. The identity morphism gives residue fibre kappa(p) and zero relative differentials. For Spec(R/I) to Spec R, fibres are either empty or the residue-field spectrum, and the same calculations apply without flatness. A polynomial affine line over a nonempty base fails the assumed unramified-fibre condition, as expected, and is not incorrectly treated by the proof. Neither a Noetherian assumption nor separability, smoothness, flatness, finite presentation, or nonemptiness is introduced.

## Unfinished work

None for this one-level split. No Lean files were written. Delivery validation and push are performed with the required launcher tool.
