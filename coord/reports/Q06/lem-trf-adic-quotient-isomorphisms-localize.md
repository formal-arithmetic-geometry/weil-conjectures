# Stage-1 report

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-adic-quotient-isomorphisms-localize.json` (statement, split). The statement and its definition dependency are unchanged. Six proof steps replace the empty proof. There are no new nodes and no new Mathlib leaves. `citations.json` contains one exact statement quotation for every step/node pair. `searches.jsonl` records the actual additional searches.
2. Attachments: none. Searches in `lean/WeilConjectures/` for the blueprint id and for quotient-isomorphism/localization and adic-isomorphism language found no exact declaration. The nearby `RingTheory/LocalCompletionQuotient.lean` proves a different completion comparison, not this statement.
3. WANTED: none.
4. The imported item had a complete statement but no proof. Its seven inherited Mathlib search entries were retained. Two additional semantic phrasings, Loogle, LeanSearch, and two source searches found useful tools but no declaration giving this entire statement. The source bodies of `Localization.localRingHom`, `IsLocalization.ringEquivOfRingEquiv`, the quotient-localization instance, and `Ideal.map_pow` were read. The first two do not by themselves prove prime-extension equality or the quotient hypotheses required here. Existing DAG Mathlib leaves already provide both non-elementary tools, so no new node is justified. No statement error was found.
5. Unfinished mathematics: none at this one-level split. The required server checks and push are recorded below after execution.

## Sources and route

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current blueprint's `sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`/`.proof.md`. This item is an auxiliary algebra comparison in the inherited completion branch, not the unit's key statement. No unit realization fields are changed. The proof follows the fraction comparison of Stacks Tag 00CT, `algebra.tex`, `proposition-localize-quotient`, whose statement and both inverse fraction maps were read. The additional prime-extension and compatibility calculations are explicitly agent-written. No SGA source is used.

## Not duplicates

No new nodes. Whole-DAG searches for Tag 00CT and localization/quotient language located `lem-weil-pbc-localization-at-prime-of-quotient`, which is reused, and the principal-localization and localization-prime variants, which do not state this item. Searching ideal-power language located the general `lemma-nagata-localization-ideal-pow`, which is reused. Blueprint reference searches for `localization quotient`, `quotient isomorphism`, and `00CT` returned no blueprint duplicates; ancestor lookup confirms `lem-trf-local-term-locality` as the existing `from.node`.

## Review by Q06

I checked the six steps against the actual statements of all three cited nodes and against the fraction maps of Tag 00CT. The source has no all-powers theorem hiding behind this tag: the proof therefore writes out what has to be added.

Step 1 uses only the given surjectivity at exponent one and contraction of Q. The lift of an element of Q differs from it by an element of pD, which is already contained in Q. This proves Q = pD without confusing the domain C/p with a field. Step 2 cites `lemma-nagata-localization-ideal-pow`; its statement is for every unital map of commutative rings and every ideal, and gives precisely all three equalities of extended powers used here. No Noetherianity, flatness, or finite generation is needed.

Step 3 cites `def-weil-pbc-localization-at-prime`, whose statement actually gives the fraction equivalence and identifies the maximal ideal. The map is checked on that equivalence. I wrote out the numerator criterion for membership in an extended prime: finite sums give a common denominator, and primality removes the extra denominator from a fraction equality. Applying the same argument in D gives the asserted inverse image and the induced quotient maps. This is an elementary calculation, not an appeal to a general uncited theorem on local homomorphisms.

Step 4 cites `lem-weil-pbc-localization-at-prime-of-quotient` and the localization definition. That lemma explicitly identifies R_p/IR_p with (R/I)_pbar by the specified fraction formula. Its hypotheses hold for I = p^n and I = Q^n because n is positive; the quotient ideals p/p^n and Q/Q^n are prime and contract back to p and Q. Combining its statement with the zero-fraction relation gives exactly the two denominator certificates subsequently used. These are ordinary ring isomorphisms, so no derived-object issue arises.

Step 5 uses Step 4's certificates and the stated bijectivity of alpha_n. For surjectivity both numerator and denominator are lifted at the same exponent n; the lifted denominator is outside p because its image differs from the original denominator by an element of Q^n contained in Q. For injectivity the annihilating target denominator v is lifted modulo Q^n; its lift t is again outside p. Then injectivity of alpha_n, rather than injectivity of f, gives tc in p^n. This checks the necessary denominators and ideal hypotheses explicitly. Step 6 evaluates the two transition composites on the same representative c/s, so the required canonical compatibility is established, not merely asserted.

I tested p = 0 with f an isomorphism and Q = 0 (fraction-field case), identity maps with a nonmaximal prime such as (x) in k[x,y], rings with nilpotents such as C = D = Z/4 at (2), and n = 1 and k = n. The reasoning uses neither reducedness nor separatedness of the adic filtration. In particular it never identifies D with C from isomorphisms of all their finite quotients. Prime ideals exclude the zero ring automatically. Every step is below 2000 characters. All non-elementary tools are existing nodes whose statements were opened; the remaining arguments are explicit fraction or ideal calculations. There are no new unsplit statements, no circular dependencies introduced through a new node, and no clauses moved into restatement nodes. The B–E checks required no statement correction.

## Server validation

The required `deliver.py Q06 lem-trf-adic-quotient-isomorphisms-localize --no-push` exited successfully: `OK (not pushed)`, preflight passed at `af99ed75d60`. The dry run completed before the push invocation.
