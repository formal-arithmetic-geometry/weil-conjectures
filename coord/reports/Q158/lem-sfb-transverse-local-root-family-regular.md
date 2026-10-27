1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-transverse-local-root-family-regular.json: existing statement, now split into seven proof steps. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- citations.json: ten verbatim statement quotations, one for each proof-step citation.
- searches.jsonl: current searches made through the required msearch.py command; old item searches retained in its JSON.

2. Attachments

None. Searched WeilConjectures/ for the blueprint tag and transverse/partial-root notions. RootAlgebraRegularAtRoot provides the existing one-variable input, not the full item; other root-model declarations have stricter hypotheses or only normality conclusions. The item has no exact finished project declaration.

3. WANTED

None.

4. Problems found

The item was statement-only, created by the earlier re-split of lem-sfb-snc-finite-root-regular-ring. Its statement is correct and is preserved. The parent review and its original simultaneous-induction route were read. The dimension equalities must be used before applying the root-at-root lemma: a quotient merely being regular does not establish a nonzerodivisor. Step 2 explicitly rules out zero using the finite dimension difference and then uses the regular-local domain theorem. It is essential to induct for all J simultaneously, rather than claim the root-ring regularity and its quotient regularity in a circle.

The blueprint ancestor command returns None. Retained the existing null ancestor and complete via list; retained the explicit paragraph location and same_as=[]. Read the chapter and unit records. The inherited unit is sk-thm-sf-ctf-stability (whose chapter label differs from this item's inherited chapter); neither record is changed. This is a generic commutative algebra calculation below the unit, not a change to its route.

5. Unfinished

Nothing in the assigned split. The existing cited nodes retain their own status and future obligations.

## Not duplicates

No nodes were created. DAG statement searches for monic bases, polynomial regularity, regular-local localization, finite-algebra Noetherianity, and Tags 00NU/07PF found the existing inputs used in the proof. Blueprint searches for regular root, regular polynomial, root algebra, transverse, parameter, monic and Kummer produced no statement of this whole local theorem. In particular lem-per-snc-root-algebra-structure assumes strict henselianity, roots of unity, and all root parameters in the maximal ideal. lem-sfb-snc-finite-root-face-regular is geometric, assumes global irreducible branches, and is already a sibling of the parent; it is not used to shortcut the current simultaneous local induction. The parent now depends on the item, so citing it would be circular.

## Review by Q158

I read ILO Expose IX Proposition 2.1 and the full-root display before invariants on printed p.133 (PDF page 139). It works strictly locally for its Kummer-cover purpose and leaves the regularity calculation implicit; our statement removes those unnecessary auxiliary choices for this algebra calculation. I therefore mark the proof as agent-written, following that display with the cited Stacks algebra lemmas. I read Stacks algebra.tex at 00NU (lemma-regular-mod-x), 0AFS (lemma-localization-of-regular-local-is-regular), 00NP (lemma-regular-domain), 00KQ (proposition-dimension), 00FN (lemma-Noetherian-permanence), and more-algebra.tex at 07PF (lemma-quotient-regular). The polynomial regularity source is also used in the immediately subsequent degree-p-extension-regular proof. There are no new-node sources to review and no SGA sources are used.

For step 1 I opened lem-weil-pbc-monic-quotient-free: its statement supplies the power basis for a monic quotient, not just its module finiteness. I also opened lem-weil-pbc-finite-algebra-noetherian: the finite free monomial basis gives its module-finiteness hypothesis, while the given regular-local R_J is Noetherian. The iterated basis argument is written out, including uniqueness; no unproved tensor-basis assertion is used. The presentation comparison is proved by maps on generators.

For step 2 I opened lem-weil-pbc-noetherian-local-finite-krull-dimension, which asserts finite integer dimension for exactly the Noetherian local rings in force. This licenses cancellation of the finite integers in the dimension equalities. I opened lem-sc-regular-local-domain, which supplies that R_J is a nonzero domain. Thus a nonzero parameter acts injectively, as required later. This avoids assuming the root ring is a domain, which is false when unit roots split.

For step 3 I opened lem-weil-pbc-regular-local-localization: its consequence explicitly says regular local rings are regular rings. The strong induction quantifies over every J and K, and therefore makes both A=B_{J,L} and the further boundary quotient available at smaller |K|.

Step 4 uses only the hypotheses, the monomial basis already proved in step 1, the injectivity proved in step 2, the earlier induction hypotheses, and the explicitly given generator maps. If a is inactive, its image stays a unit and no containing-root prime can exist. If active, J union {a} is a subset of S and L remains disjoint from it. Reducing the coefficient ring gives exactly B_{J union {a},L}; it is not a quotient by a root variable of a different algebra. This step is elementary and cites no new black box.

For step 5 I opened lem-sbc-root-algebra-regular-at-root. Its statement takes a Noetherian coefficient ring, an element acting injectively, a regular quotient, and a positive exponent, and gives regularity at every prime containing the root. Each hypothesis was established before applying it. Its statement does not require the coefficient algebra to be local, a domain, henselian, or to contain roots of unity. Only that stated conclusion is used.

For step 6 I opened lem-weil-pbc-localization-of-regular-ring, lem-trf-polynomial-ring-regular-base, and lem-weil-pbc-hypersurface-derivation-regular. These statements give, respectively, regularity of A[1/f], of its one-variable polynomial ring, and of a hypersurface whose derivative is a unit in the quotient. The derivative here is computed as n*T^(n-1), and the displayed inverse of T proves its invertibility. The localization A[1/f] is chosen so the criterion really has a globally unit derivative in the quotient. It is not incorrectly applied to A[T] merely because the derivative misses q. The coefficient n remains a unit under all algebra maps. The polynomial node is a Mathlib leaf (MvPolynomial.isRegularRing_of_isRegularRing, source lines 108--114 read); it is a generic algebra fact and imports no trace-formula theorem despite its filing chapter. The other off-unit algebra tools are declared in split_report.tool_uses with their specific purposes.

Step 7 uses def-weil-regular-scheme for the literal ring definition: a Noetherian ring with regular local prime localizations. The two localization presentations at q are compared using their inverse universal-property maps. The root-containing and root-missing cases cover all primes, giving the induction conclusion without a hidden descent claim.

I checked delivery-errors B--E: no new statement-only node is needed or fabricated, the item introduces all its own objects and retains its definitions; TeX has single logical backslashes; every non-elementary input has a node whose statement was opened and is quoted in citations.json. No proof of a cited node is used as an extra conclusion. No node is restated under a new id and no cyclic reference to the parent is introduced. All seven steps are below 2000 characters, and the two elementary steps contain their actual coefficient and localization arguments. The substantive inputs remain the three separate generic regularity tools rather than one new node carrying the item.

Edge cases checked: K empty (R_J with basis 1); I empty (R itself); J=S (only inactive unit equations remain); n=1 (T=f and derivative 1); dimension-zero regular R (a field, so S must be empty by the dimension condition); a nonhenselian DVR with a uniformizer and a unit such as 1+s (split unit-root factors are permitted); and a two-parameter regular local ring with both boundary equations. Repeated parameters and a zero parameter fail the dimension equalities, as does the false SNC triple (s,u,s+u) in dimension two. Removing invertibility of n would fail already for unit roots in characteristic p; it is used precisely in step 6. No stronger hypotheses have been added.

Current Mathlib searches ran with the required command (leanfinder twice, loogle, grep, leansearch). I read their returned signatures: regular sequences, Kummer field extensions and standard-etale presentations do not give this theorem; the polynomial-regularity hit is already the cited Mathlib leaf. No search was invented, and the inherited unavailable LeanSearch entry is preserved as unavailable rather than silently converted to a negative result.
