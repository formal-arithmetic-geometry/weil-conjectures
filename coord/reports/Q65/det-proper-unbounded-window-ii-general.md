# Q65: det-proper-unbounded-window-ii-general

## Files written

- dag/nodes/sec-six-functors-basics/det-proper-unbounded-window-ii-general.json — statement, split into six proof steps; no Mathlib match for the item.
- citations.json — verbatim statement excerpts for all 10 step/node citation pairs.
- searches.jsonl — actual msearch.py search log. prepare.py is a sandbox-only preparation script.

## New nodes

None. In particular, the general unbounded cohomology criterion already exists as lem-weil-pbc-unbounded-derived-iso-cohomology, status mathlib, matching DerivedCategory.isIso_iff at Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean:88–89. It is reused, not recreated. No new Mathlib leaves.

## Attachments

None. Searched the project WeilConjectures/ (and Comparator/) in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint identifier, ind-constructibility names, and proper/direct-sum/coproduct terminology. The only nearby pro-etale unbounded coproduct discussion is SixFunctors/ProEtale/ExceptionalAdjoint.lean. Its HasAmbientExceptionalRightAdjoint.isLeftAdjoint theorem at lines 151–153 is sorry and has an additional FullCD hypothesis about all ambient sheaves. It neither supplies this statement nor permits attachment. Its finite-coefficient etale-origin theorem is also sorry. The source does not have the newer ModuleObject/BaseChangeTheorems/Proper module; the upstream master is not treated as a finished proof.

## WANTED

None. The current blueprint statement, proof, unit and chapter are present, as are Stacks derived.tex and the pinned Mathlib source for the general criterion.

## What was wrong and what changed

The imported statement has no mathematical dispute. I retained its assertion and added the explicit meanings of its coefficient, small-family, ordinary unbounded derived-category and ind-constructibility notation. These are explanatory definitions, not extra hypotheses: in particular no common bound is imposed on the original complexes, no constructibility is substituted for ind-constructibility, and no completed derived category or constant-discrete coefficient sheaf replaces the pulled-back condensed ring. The comparison is now characterized by its restrictions to coprojections.

The imported proof silently used closure under sums and truncations, commutation of cohomology with sums, and detection of unbounded derived isomorphisms by cohomology. The first three are exactly det-ambient-ind-derived-sums; the last is the existing unbounded Mathlib leaf. The bounded-below criterion lem-weil-pbc-derived-plus-iso-on-cohomology is insufficient here and is not cited. The compatibility sentence in the imported proof is expanded into a canonical map b and explicit naturality equations for u and v, rather than assuming a map K -> WK exists. It generally does not: the window comparison is a zig-zag K <- tau_le K -> WK.

The imported source metadata pointed to the statement .md while the proof lives in the separate .proof.md. Each new proof step and proof_origin now identifies that proof file. The proof remains agent-origin, as required for a blueprint argument. All inherited blueprint_*, import_flags and ownership metadata are retained. This is the detail node for unit paragraph 2, not the unit's key statement; no unit realization fields are changed.

A shared-DAG metadata omission was observed: the current DAG has the detail nodes det-ambient-ind-derived-sums and det-ambient-ind-derived-triangulated, but no node file named sk-cor-ambient-ind-derived (although the unit and blueprint exist). Similarly sk-prop-ind-heart is a unit without a node file here. I did not add dependencies on these missing ids or recreate their assertions. The item defines Dic and IndCons explicitly using the existing constructible-sheaf definition and cites the extant detail node for the properties actually used.

## Not duplicates

No new nodes were created. Whole-DAG searches by cohomology detection, DerivedCategory.isIso_iff, sums/truncations and ind-constructibility found the interfaces reused here. Whole-blueprint searches using tools/blueprint_refs.py covered "cohomology direct sums", "quasi-isomorphism", "isomorphism cohomology", "Direct sums of arbitrary", "proper direct image" and "truncations commute". The parent sk-lem-proper-unbounded-window-ii is the unit theorem, with no specified fibre bound; the bounded detail concerns uniformly bounded families and is a dependency, not an equivalent replacement. Finite-coefficient proper coproduct results concern a different coefficient category. Thus the item's same_as is empty.

## Mathlib searches

Every query was run through msearch.py, and the item records the actual tool and exact query. Two semantic phrasings were tried for the item. LeanFinder returned generic pushforward additivity, induced exact functors on derived categories, and site/coefficient constructions; none is the proper ind-constructible theorem. LeanSearch returned finite-coproduct preservation for additive functors and generic coproduct definitions, which cannot imply arbitrary coproduct preservation for this right derived functor. Loogle returned no hits for the combined preservation/derived-category name pattern. The broad grep had 25 generic hits (including occurrences of the substring "property"), so I followed it with an AlgebraicGeometry grep for ind-constructibility and proper sum preservation, which had zero hits. None of these is an exact match or a one-line specialization. Separate exploratory searches for the cohomology criterion found DerivedCategory.isIso_iff; its existing node was then located by declaration-name search and read, so no leaf was created.

## Review by Q65

I read the current main-20261015 chapter sec-six-functors-basics, the unit sk-lem-proper-unbounded-window-ii, and the item's statement and entire separate proof. The chapter distinguishes module objects over pulled-back condensed rings from fixed discrete coefficients; the revised statement maintains that distinction. The unit's second paragraph explicitly calls for the finite-window reduction, and all six steps follow that route. For the generic final criterion I read Stacks derived.tex, Tag 05RT, label lemma-acyclic (acyclic complexes form the kernel of derived localization), and Mathlib HomologySequence.lean:88–104, whose isIso_iff statement is for the unbounded category and all integer degrees. There are no new statements whose literature source needs a separate review.

Step 1 takes the cohomology-of-sums identity and closure of Dic under sums from clause (1) of det-ambient-ind-derived-sums; I opened that node and checked its statement applies to any family in the ambient category, not only constructible or bounded ones. This also supplies the identity on Y for the family Rp_* K_alpha. The step does not assume Rp_* already preserves sums.

Step 2 uses the explicit kernel/cokernel good-truncation formulas and retained-cohomology assertion in def-kun-truncations, which are initially stated for an arbitrary abelian category. Its later etale examples are not used as a restriction. Clauses (1) and (2) of det-ambient-ind-derived-sums supply exactly the sum identity and the truncation-closure assertions. The existing unbounded cohomology criterion promotes the calculated H^n(b) to an isomorphism in the ambient derived category. The family can be unbounded in both directions. I checked that the map b has the correct direction from sum W K_alpha to W(sum K_alpha), and that in an interior degree its cohomology is the map with the original coprojections. Enlarging a fibre bound to max(d,0), when necessary, does not add a hypothesis.

Step 3 uses precisely the last assertion of sk-lem-proper-unbounded-window, which explicitly supplies the window identification induced by K <- tau_le_q K -> tau_ge_(q-2d-1) tau_le_q K. Its hypotheses are the same proper p, coefficient Lambda and uniform fibre bound as the item. Step 1 supplied L in Dic, so the assertion applies to L as well as to every K_alpha. The functoriality of good truncations is explicitly part of def-kun-truncations. The equations f u_T = u_T' tau_le f and W(f) v_T = v_T' tau_le f give naturality after inverting the first cohomology map. This checks the imported proof's zig-zag compatibility rather than hiding it behind the word "natural".

Step 4 opens and uses det-proper-unbounded-window-ii-bounded, whose statement accepts any family in Dic with cohomology in a common interval. The same nonnegative d gives a <= q, with a=q-2d-1; this is a finite interval for every integer q. Truncation formulas provide that bound uniformly in alpha, and the closure statement provides membership in Dic. Thus no boundedness hypothesis is smuggled into the original family.

Step 5 is elementary diagram algebra from steps 1–4. On the alpha-th coprojection both routes are the equality in step 3 with f=iota_alpha, using b iota_alpha^W = W iota_alpha. Coproduct universality proves equality of the assembled maps. The sum of the theta inverses is explicitly checked to invert the sum of the theta maps. Rp_* b is invertible because b is invertible, which is functoriality, not a claim that Rp_* preserves sums. This is why the step has no new citation or auxiliary node.

Step 6 uses the exact statement of lem-weil-pbc-unbounded-derived-iso-cohomology, instantiated with the abelian category of Lambda_Y-module sheaves. The statement has no lower bound or smallness restriction on cohomological degrees. I avoided the tempting bounded-below analogue. All cited statements are quoted verbatim in citations.json, including the full window formula, rather than a proof-only assertion from their files.

For small cases I checked an empty index family (zero comparison), singleton families (the functorial identity), d=0 (the window [q-1,q]), negative q, a complex with cohomology above or below the window, and families whose nonzero degrees have no common upper or lower bound. In the last case the window still gives one common interval for fixed q. The empty scheme permits enlarging any dimension bound to a nonnegative one. These checks require no convergence of a spectral sequence, no interchange of infinite products with sums, and no ambient FullCD assumption. I found no false statement or source error. The corrections were to missing interfaces and the unstated compatibility argument, and were made in this sandbox only.

B1–B9 are vacuous for new-node shape because none are created; B10 was checked against the project source. For C1–C4 the precise statement interfaces are as described step by step above, C5 was checked across the DAG and blueprint, and C6 is checked by the delivery preflight. The two source-unit interfaces (finite window and bounded family) are preserved, so D1–D5 do not arise by moving the item into new nodes. The sole off-unit non-leaf tool, det-ambient-ind-derived-sums, is declared under split_report.tool_uses for its generic sum/truncation interface. No SGA source is used.

## Repair of returned delivery

The landing return identified `sk-def-sfb-derived-categories` as changed since the reviewed delivery. I re-read its current main-DAG statement in `dag/nodes/sec-proetale-coefficients/sk-def-sfb-derived-categories.json` before this repair. It still states that the relevant module-sheaf derived categories are ordinary unbounded localizations (with the pulled-back ring-object module category in the layer used here), and that the constructions are taken in the fixed universes. The item’s explicit sentence defining the ambient categories and its `stmt_deps` citation therefore remain accurate; no coefficient category, boundedness condition, or derived-functor meaning was silently changed. The item’s proof does not use an unstated theorem from that definition node: all non-elementary proof interfaces are cited in the six steps and rechecked against their current statements. I regenerated the delivery from the current `origin/newtargets-dag` base and reran the citation, DAG, and review preflight.

## Unfinished work

None in the one-level split. The cited imported nodes remain independent future stage-1 work; this delivery does not assert their Lean proofs are complete. This sandbox is for the second reader; no push is authorized for this first reading.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against `sk-lem-proper-unbounded-window-ii-general.md` and the unit statement; the coefficient rings, pulled-back module categories, arbitrary small family, proper fibre-dimension bound, and canonical coprojection comparison all agree hypothesis by hypothesis.
- Step 1: checked against `det-ambient-ind-derived-sums` clause (1), including its arbitrary-family scope and its closure of `Dic` under sums; the use on `Y` is a direct instantiation, and no preservation by `Rp_*` is assumed.
- Step 2: checked against `def-kun-truncations`, `det-ambient-ind-derived-sums` clauses (1)–(2), and the unbounded cohomology criterion; the finite window has the stated cohomology in `[q-2d-1,q]`, the assembled map has the correct direction, and arbitrary two-sided unboundedness is retained.
- Step 3: checked against the full window assertion in `sk-lem-proper-unbounded-window`; its hypotheses match the item, the truncation maps are functorial, and the displayed naturality equations justify the zig-zag compatibility on each coprojection.
- Step 4: checked against `def-kun-truncations`, `det-ambient-ind-derived-sums` clause (2), and `det-proper-unbounded-window-ii-bounded`; the truncated family has one common finite interval and no bound is added to the original family.
- Step 5: checked the coprojection calculation and cancellation directly from steps 1–4; the equality is established componentwise and the inverse sum is justified by coproduct universality, with no uncited geometric input.
- Step 6: checked against `lem-weil-pbc-unbounded-derived-iso-cohomology` and Stacks `derived.tex`, Tag 05RT (`lemma-acyclic`); the criterion applies in every integer degree in the ordinary unbounded derived category.
- New nodes: none; consequently B1–B7 were checked as vacuous, and no duplicate or unnecessary node remains. The existing Mathlib leaf is reused rather than recreated, with its declaration and source lines recorded in the worker review.
- Small cases: rechecked the empty family, singleton family, `d=0`, negative `q`, complexes supported outside the window, and families with no common global cohomological bounds; each is covered by the stated construction.
- Changes made in second reading: no mathematical or metadata repair was necessary; this section records the independent source/interface audit and the successful dry run (`OK (not pushed) ... at 3029b41eb5`).

## Second reading by Q65

- Item statement: checked against blueprint `sk-lem-proper-unbounded-window-ii-general.md` and the unit statement hypothesis by hypothesis; the prime, fixed algebraic closure, finite extension, coefficient alternatives, proper morphism, integer fibre bound, arbitrary small family in `Dic`, and coprojection comparison all agree. The added prose defines the notation already used and adds no common cohomological bound or coefficient change.
- Step 1: checked against the statement of `det-ambient-ind-derived-sums`; its arbitrary-family cohomology/sum clause gives both `L ∈ Dic` and the cohomology sum on `Y` after instantiation to `Rp_* K_α`. The comparison direction and degreewise reduction are correct.
- Step 2: checked against `def-kun-truncations`, clauses (1)–(2) of `det-ambient-ind-derived-sums`, and `lem-weil-pbc-unbounded-derived-iso-cohomology`; the canonical map `b : ⊕ WK_α → WL` has the required direction, is an isomorphism in every degree including outside the window, and imposes no bound on the original family.
- Step 3: checked against the full window assertion of `sk-lem-proper-unbounded-window` and the functorial truncation maps in `def-kun-truncations`; the zig-zag maps have the stated directions, and the displayed equations establish naturality for each coprojection.
- Step 4: checked against `def-kun-truncations`, clause (2) of `det-ambient-ind-derived-sums`, and `det-proper-unbounded-window-ii-bounded`; the truncated family lies in `Dic` and has the common finite interval `[q-2d-1,q]`, so the bounded comparison applies without strengthening the item's hypotheses.
- Step 5: checked componentwise from steps 1–4; coproduct universality gives the displayed equality, and the sum of the inverse window maps is verified on each coprojection. The argument uses only functoriality of `Rp_*` and no unlisted preservation claim.
- Step 6: checked against `lem-weil-pbc-unbounded-derived-iso-cohomology` and Stacks `derived.tex`, Tag 05RT (`lemma-acyclic`); all integer-degree cohomology maps detect an isomorphism in the ordinary unbounded derived category.
- New nodes: none. I checked the existing DAG and blueprint for duplicates and confirmed that the existing Mathlib leaf is reused rather than recreated; B1–B7 therefore do not apply.
- Edge cases: checked the zero and empty families, singleton family, empty scheme, `d=0`, negative `q`, truncations with zero cohomology, and two-sided unbounded families. Each is covered by the stated construction.
- Changes made: no mathematical or metadata repair was needed. The worker's node and citations remain accurate after this independent reading; this report section records the checks required for delivery.
