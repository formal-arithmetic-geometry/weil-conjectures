## Worker report

Q105 split `lem-trf-exact-evaluation-transformation-descent` in `dag/nodes/sec-trace-formula/lem-trf-exact-evaluation-transformation-descent.json`. Seven proof steps; the statement and its hypotheses are unchanged. `citations.json` supplies a verbatim statement extract for every cited node in every step. The original research entries are retained; `searches.jsonl` records the additional six searches actually run by Q105.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing leaves `lem-weil-pbc-localization-universal-property`, `lem-weil-pbc-exact-functor-derived-factorization`, and `def-weil-abstract-derived-category` suffice.

## Attachments

None. Searched the live project under `lean/WeilConjectures/` for the exact blueprint tag and for localization transformation names. Its exact-functor comparison declarations cover isomorphisms and canonical compositors, not this whole statement for arbitrary noninvertible transformations and fixed composite factors. No exact project declaration was found.

## WANTED

None. The needed categorical source and Mathlib source are present locally.

## Findings and blueprint

The item was unsplit, with an empty proof. I read the fixed chapter `sec-trace-formula`, unit `sk-d-weil`, and the current main-20261015 ancestor proof `lem-trf-frobenius-operator-compact-description.proof.md`. The ancestor sentence “transports the pair ... along the compact-support base-change identification” is the place served by this exact-functor normalization lemma. No chapter or unit route is changed. Searches of the entire DAG by localization, natural-transformation and exact-functor concepts, and `blueprint_refs.py search` for localization, natural transformations, descent of transformations and 04VG found the existing localization universal-property leaf. The existing `lem-sp-exact-derived-transformation-pasting` and `lem-pod-derived-exact-square-composition` were also read: they use standard derived comparisons, whereas this item specifies recursive factors and arbitrary compatible t_m. There is no need to create another pasting or descent node.

The Stacks source Tag 04VG is only the ordinary localization universal property for functors; it does not alone assert descent of noninvertible natural transformations. That additional content is explicitly supplied by the statement of the existing localization leaf and verified against Mathlib `CategoryTheory/Localization/Predicate.lean` lines 278–350 (fully faithful precomposition, component formula, detection, identity and composition). The proof is honestly marked agent-written for the explicit termwise/composite-factorization refinement. No SGA source is used.

## Review by Q105

I read Stacks `categories.tex`, label `lemma-properties-left-localization` (Tag 04VG), and the cited Mathlib localization declarations above, along with `Algebra/Homology/DerivedCategory/ExactFunctor.lean` lines 36–56 and `Algebra/Homology/Additive.lean` lines 161–192. I then opened the complete statements of all three cited DAG nodes. The exact-factorization node asserts preservation of quasi-isomorphisms and a natural factorization; the localization node explicitly states descent of arbitrary natural transformations with prescribed factors in clause (2), and detection in clause (3). I did not take these facts from a definition or from an uncited proof.

Step 1 uses the complex and chain-map definition in `def-weil-abstract-derived-category`. Naturality at each differential gives the chain condition and naturality at each component of a chain map gives the natural-transformation condition. This is an elementary calculation, including for T_m and its inverse.

Step 2 uses exactly the quasi-isomorphism preservation assertion of `lem-weil-pbc-exact-functor-derived-factorization`, for G and each H_r. Since the target localization inverts the resulting quasi-isomorphisms, both functors to which descent is applied invert the source class. The prescribed w is natural by composing the two given factorization squares. No boundedness, injective resolution, or invertibility of alpha is introduced.

Step 3 uses clause (2) of `lem-weil-pbc-localization-universal-property`: its phi_1 is v and its phi_2 is w, so the order of the formula is w^{-1} L_B(C(alpha)) v, as in the item. All input hypotheses were established in Steps 1–2. The inverse-arrow equation was checked by multiplying the ordinary naturality equation by the two functor images of the inverse quasi-isomorphism. Alpha is never inverted.

Step 4 uses both the exact-factorization and localization nodes for arbitrary finite words. I checked the recursion a_FE = a_F at C(E)K composed with D(F)(a_E): its domain is D(F)D(E)LK and its codomain is L C(F)C(E)K. With outermost G the output is D(B), otherwise it is D(M). The identity and composition calculations cancel only the common intermediate factor. These are formulas for the specified factors, not an assumed identification with unspecified canonical comparisons.

Step 5 uses no additional theorem: its two displayed naturality squares give the two whiskering identities by substitution of Step 4. In particular right whiskering requires naturality at a_E, which is a derived isomorphism rather than a chain map; Step 3 supplies that naturality. The hypothesized equation for t_m is exactly the conjugation formula for T_m, with the source factor e_1 at C(H_m)K composed with Q_1(e_m). Thus that hypothesis is used, not silently omitted. I also checked its inverse by inverting this equation.

Step 6 is structural induction on finite expressions, with base cells, identity, composition and both functor-image operations handled in the preceding steps. Clause (3) of the localization node detects equality of the resulting natural transformations. It is not an assumption that localization is faithful on chain maps. Step 7 is elementary restriction: fullness retains all components with endpoints in C; the naturality equation is the ambient equation for the same arrow. V need not take values in C, because its codomain remains D(B). No representative is required to lie in C.

For B–E of the delivery-errors checklist I checked that no unsplit statement, duplicate, relabelled clause, or new definition is introduced; all cited uses have exact statement quotations; proof_deps is the union of the uses; and no new off-unit dependency other than existing Mathlib leaves is used. The detailed whiskering calculation is under 2000 characters and hides no comparison lemma. I corrected notation in the draft to put primes in exponents and to say that G is the outermost functor, consistent with the composition convention in the item. I retained all original research entries and the original statement.

Small cases checked: zero alpha gives a zero conjugate without an inverse of alpha; identity H_r and identity factors reduce the formula to localization of alpha; all-identity compositors satisfy the identity formula; a complex with zero differential has unrestricted degreewise components subject only to alpha naturality; and the zero and empty full subcategories impose no extra condition. Nontrivial factors are retained on both sides of each conjugation and cancel in the correct order. An arbitrary full subcategory need not be replete: Step 7 restricts the already constructed ambient transformations and does not replace its objects by representatives. No statement dispute was found.

## Unfinished work

None in the split. The first server dry run exited 0 with OK (not pushed), preflight passed, at 87ee0b62458. A final citation-only refinement quotes localization clause (3) for Step 6; final validation follows that refinement.
