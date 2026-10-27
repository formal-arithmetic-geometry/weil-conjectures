# Q35: lem-per-ind-etale-height-one-valuation

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-ind-etale-height-one-valuation.json: existing statement, now split in seven steps; no whole-item Mathlib match.
- citations.json: one verbatim statement quotation for each of the thirteen step/node citations.
- report.md: this report. searches.jsonl is the search command's unmodified log.

There are **0 new nodes and 0 new Mathlib leaves**. The reusable ingredients already have DAG nodes, so creating nodes for flatness, the local fibre, the DVR conclusion, or valuation preservation would duplicate existing results or isolate elementary consequences. The item's statement and its six statement dependencies are unchanged. The existing blueprint reference and all prior Mathlib search records are retained, with Q35's actually executed searches appended.

## Attachments

None for the item. A project-wide search under lean/WeilConjectures found no declaration with the item's blueprint tag and no declaration giving all its clauses. The project has Algebra.IndEtale and residue-field separability results in RingTheory/ProEtale/IndEtale.lean, and specialized inertia/ramification valuation comparisons; these do not state this general Noetherian normal-domain theorem. The existing lem-sc-normal-dim1-dvr is already Lean-closed and is reused as such, without changing it.

## WANTED

None. Every mathematical source used is present under literature/stacks-project/.

## Problems found and changes

The live item was a statement-only node, with no earlier sandbox split or report. There is no repair note for it. The source statement is correct; no STATEMENT-DISPUTED correction is needed. Its phrase about going down is implemented by the existing flat height formula (Tag 00ON), which already includes that input. I did not assume finite presentation of B over A, module finiteness, excellence, or henselianity. In particular the Mathlib ramification-index search candidate cannot supply the item: Mathlib/NumberTheory/RamificationInertia/Unramified.lean:34-36 requires EssFiniteType.

I read the current blueprint/latest copy of lem-per-artin-gabber-affine-curve and its proof. The inherited ancestry records this as a local algebra input to the regular-pair modification / strict-local Cartier-test branch below its cosupport proof. No unit statement, unit realization, or chapter route is changed. I read the chapter and sk-p-dl-a1-perverse unit records, the three-level contract in SETUP.md, GOAL.md, and delivery-errors B through E (including the repeated historical sections).

## Searches and reuse

The Mathlib searches ran only through batch2/msearch.py and their results are retained as produced in searches.jsonl. Q35 ran LeanFinder with the general height/valuation phrasing, then the localized DVR ramification-index phrasing; Loogle with Algebra.Etale, Ideal.height; LeanSearch with the local maximal-ideal/dimension phrasing; and two greps (ind-etale terminology in RingTheory and combined etale-height/valuation expressions across Mathlib). All services answered. I read the returned etale-locus, height, formally unramified and ramification-index hits, and opened the ramification-index source to check its extra finite-type hypothesis. None gives the item or a one-line specialization to it.

Before deciding to add no nodes, I searched the full DAG for Tag 0AH1, fibre structure, flat dimension/height formulas, normal localization, DVR characterization, uniformizers, and going down. I opened the matching existing statements, rather than relying on names. blueprint_refs.py ancestor identified lem-per-artin-gabber-affine-curve; searches over the imported blueprint for ind-etale, valuation and height-one found no equivalent whole-item node. The existing normal-dimension-one DVR node states only the DVR characterization, and the field-extension-order node assumes an algebraically closed residue field and a specific tensor base change, so neither is a whole-item duplicate.

## Not duplicates

No new nodes. The apparent overlap with lem-sc-dvr-field-extension-order is only the final elementary exponent calculation: that statement concerns a particular scalar extension R tensor_k k', whereas this item concerns arbitrary ind-etale Noetherian normal domains and all their primes, with dimension and maximal-ideal comparisons.

## Review by Q35

I read Stacks more-algebra.tex, Tag 0AH1 (lemma-filtered-colimit-etale-noetherian-fibres), including the proof: Noetherianity is used to turn the reduced zero-dimensional fibre into a finite product of fields; no finiteness of its residue extensions is claimed. For the other inputs I read proetale.tex Tag 097N (lemma-ind-etale-implies) and algebra.tex Tags 00HT (lemma-flat-localization), 00FN (lemma-Noetherian-permanence), 00GY (lemma-localize-normal-domain), 00ON (lemma-dimension-base-fibre-equals-total), and 00PD (lemma-characterize-dvr), including the final fraction-valuation calculation. The local-fibre formulas appear in algebra.tex Tag 00OL; the quotient/localization argument is Tag 00CT. There are no new nodes whose sources need a separate review.

For Step 1 I checked that lem-weil-pbc-ind-etale-stability explicitly says an ind-etale map is weakly etale, and that def-weil-pbc-ind-etale-algebra explicitly includes flatness in the equivalent weakly-etale condition. Flat tensor exactness comes from lem-weil-pbc-flat-tensor-exact, not from a definition of flatness. The domain hypothesis on A makes multiplication by a nonzero a injective, and nontriviality of the domain B excludes phi(a)=0. This also constructs the fraction-field embedding explicitly.

For Step 2 I checked both clauses of lem-weil-pbc-flat-local-ring-maps: it supplies local flatness and Noetherian localizations. lem-weil-pbc-localization-normal-domain supplies normal domains and the fraction-field identifications, using A minus p and B minus q, neither containing zero. Injectivity of the localized map follows from the embedding already established, without adding faithful flatness as a hypothesis.

For Step 3 I checked the full statement of lem-weil-pbc-henselization-finite-separable-fibres. Despite its name, it is stated for every filtered etale colimit with Noetherian B and not just a henselization. Its isomorphism is the canonical map to the residue fields of exactly the primes above p. Thus our q selects an actual nonempty factor. I do not use finite degree of a residue extension: separable algebraic extensions can be infinite here.

For Step 4 I checked that def-weil-pbc-localization-at-prime gives C=B_p/pB_p and that lem-weil-pbc-fibre-ring-primes-residue-fields identifies Q with the chosen q, including the canonical residue-field map. I applied lem-weil-pbc-localization-at-prime-of-quotient with R=B_p and I=pB_p, exactly within its hypotheses. The inverse image of Q is qB_p; denominators from A minus p stay outside q. The two iterated-fraction maps are written explicitly, so there is no unspecified transport of local rings. Inverting the coordinate idempotent e_j in the finite product kills every other factor and leaves a field. The final ideal equality uses locality of S and the inclusion pS contained in qS. These are short calculations from the cited statements, not new lemma nodes.

For Step 5 I checked that lem-weil-pbc-flat-height-formula applies to Noetherian A and B with the flatness already proved; it explicitly states both the height equality and the local-dimension formula with S/pS. A field has exactly the zero prime, so its dimension is zero, including when p=q=(0) in field examples. This establishes dimension equality for every prime before restricting to height one.

For Step 6 I checked that lem-sc-normal-dim1-dvr literally states the Noetherian normal local domain criterion and is already closed in the project's audit. Normality and dimension one have both been proved before applying it to R and S. def-sc-discrete-valuation-ring defines a uniformizer as a generator of the nonzero maximal ideal. Extending pR=(pi) gives pS=(phi(pi)); Step 4 then gives precisely qS=(phi(pi)), with nonzero maximal ideal since S is a DVR.

For Step 7 I checked that lem-weil-pbc-dvr-unit-times-uniformizer-power supplies the nonnegative factorization for each nonzero numerator and denominator in R. I use neither an unstated uniqueness clause nor a fraction factorization theorem. Both factors are nonzero, and units remain units by the explicit inverse identity. Normalized valuations give a unit value zero and a uniformizer value one; subtracting the numerator and denominator exponents treats all f, including negative values. This is an elementary consequence of the factorization and of the definition of the DVR valuation.

I checked delivery-errors B-E point by point against these files. All citations have verbatim quotes in citations.json; every non-elementary input has its own existing node; no step cites a proof in place of a statement; and generic off-unit tools are declared in split_report.tool_uses for the maintainer's review. There is no new node that restates a clause of the item and no source route through SGA. All seven steps are shorter than 2000 characters. Small cases checked: the identity map, field extensions with only height-zero primes, a localization A to A_s, and an infinite algebraic separable extension of fields. The localization example confirms that global faithful flatness is not required, while the field examples confirm that the theorem makes no spurious DVR assertion at height zero. Ramified DVR extensions do not contradict the result: they fail the ind-etale hypothesis, and their nonreduced closed fibre would fail Step 3.

## Unfinished work

None in the stage-1 split. Existing cited non-leaf nodes retain their own status; this delivery changes only the assigned item. No Lean file was written and no compiler, Lake or build tool was run. Required dry run and delivery results are recorded below when complete.

## Validation

The first dry run requested a longer quotation for the ind-etale stability citation (the exact sentence was shorter than the tool's 40-character minimum). I replaced it with the node's entire verbatim statement; the mathematical citation and proof are unchanged.
