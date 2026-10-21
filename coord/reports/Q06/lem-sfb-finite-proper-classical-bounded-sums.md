## Worker report

Item: lem-sfb-finite-proper-classical-bounded-sums. Group Q06. Stage 1, direct delivery, 2026-10-21.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-proper-classical-bounded-sums.json: statement node, now split; no exact Mathlib match.
- citations.json: a verbatim statement quotation for each node used in each numbered proof step.
- report.md: this report. searches.jsonl contains the actual msearch results; write_split.py is sandbox-only preparation.

There are zero new DAG nodes and zero new Mathlib leaves. The item is not its unit's key node; no unit or chapter record was changed. The statement and statement dependencies are unchanged.

### Attachments

None. I searched WeilConjectures for the item tag, the bounded coproduct notion, and the relevant direct-image/coproduct declarations. AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_bounded in WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/LowerStarCoproducts.lean is a genuine proof of the bounded invertibility assertion. It does not state the item's full closure, natural good-truncation compatibility, and the specified composite for every choice of origins, so it does not attach the whole item. The related EtaleOriginHomology.lean declarations are useful partial coverage, not an attachment of this item. Only the live library supplied in the brief was searched; no Lean was written or compiled.

### WANTED

None. The needed blueprint, Stacks TeX, and Bhatt–Scholze paper are present.

### Findings and changes

The item had no proof and no saved sandbox attempt. Its current statement is mathematically consistent: it already makes étale coproduct preservation a hypothesis and restricts essential-image transport to bounded-below objects. I retained both restrictions. In particular I did not reproduce the ancestor blueprint's unsupported unbounded equivalence assertion. This item only realizes the bounded transport part of the ancestor's Transfer paragraph; it does not replace the unit's étale direct-image theorem or its unbounded truncation argument.

The split proves the sum and truncation assertions using exactness and termwise sums, obtains bounded étale origins with exactly the same interval by reflecting zero cohomology through the fully faithful sheaf inverse image, and proves the named-map factorization on each coprojection. This calculation verifies the actual comparison, not just existence of some isomorphism. No source or statement correction was necessary.

Mathlib queries were run through msearch only, using the exact query strings now appended to the item's mathlib_searches and preserved in searches.jsonl. Both semantic phrasings, Loogle, LeanSearch, and two source greps returned generic coproduct/derived-exact-functor infrastructure or unrelated scheme results. Their returned types do not assert the classical pro-étale comparison or the complete item. The generic infrastructure is already represented by existing DAG nodes. No unavailable service was recorded as a negative result.

### Unfinished work

None in this one-level split. The existing dependency nodes retain their own proof obligations and statuses.

## Not duplicates

No new node was created. Whole-DAG searches for Tag 07D9, classical derived equivalences, Grothendieck ring-sheaf categories, exact derived functors, and separated/quasi-separated morphisms found the existing nodes used below. Whole-blueprint searches for classical, coproduct, and direct sums found broader, narrower, or differently-coefficiented statements; none is the entire item. The blueprint ancestor is det-ctf-finite-proper-localizing, through lem-sfb-finite-proper-classical-coproducts, and the item's from.place now identifies the bounded Transfer argument precisely. The related lem-sfb-finite-classical-localizing assumes a prime-power-annihilated ring, whereas this item allows any finite commutative ring; I reused the general sheaf-category tools instead of applying that more restrictive result.

## Review by Q06

I read the chapter and unit records, the current main-20261015 ancestor proof, the item's full statement and previous search records, and delivery-errors sections B–E (including their repeated historical copy). For the mathematical sources I read Stacks injectives.tex at Tag 079B (definition-grothendieck-conditions), Tag 079Q (remark-existence-D and its ringed-site example), and the statement and proof of Tag 07D9 (lemma-derived-products); derived.tex at Tag 015F (lemma-right-derived-exact-functor); proetale.tex at Tag 09A6 (lemma-morphism-comparison); and Bhatt–Scholze §5.1–5.2, especially Lemma 5.1.2, Corollary 5.1.6, Proposition 5.2.6, and §5.4 Lemma 5.4.3. The module-coefficient assertions are taken from the existing explicit module statements, rather than inferred solely from the abelian-sheaf versions in the paper. No new node needs an additional source.

Step 1 uses lem-weil-pbc-ring-sheaves-grothendieck, whose statement covers arbitrary ring sheaves on any small site, and lem-kun-grothendieck-derived-coproducts, whose statement explicitly supplies the termwise complexes and their coprojections, including the empty family. The common universe and constant coefficient sheaves meet these hypotheses on both sites. I wrote out the finite-partial-sum/filtered-colimit argument for exactness, so no uncited AB4 assertion is hidden here.

Step 2 uses the latter termwise-coproduct theorem and the actual kernel/cokernel formulas in def-kun-truncations. Exactness from step 1 gives the image and quotient formulas too. The boundary-degree maps show naturality and compatibility with the canonical truncation inclusion and quotient maps, not merely cohomological agreement. The derived coproduct is explicitly the ambient one.

Step 3 uses det-pe-classical-sheaves-modules for exactness, full faithfulness and the module adjunction; it really states all three. The Hom calculation proves sheaf sum preservation directly. The termwise-coproduct node then supplies derived sum preservation, and lem-weil-pbc-exact-functor-bounded-below explicitly states natural cohomology commutation for every integer and every unbounded input. Thus no unbounded derived full faithfulness is used.

Step 4 uses det-pe-classical-sheaves-modules to choose sheaf origins in each degree, sk-def-pe-classical-definition for the predicate on complexes, and def-kun-truncations for which cohomology survives truncation. All further deductions are the computations of steps 2–3 and the fact that exact inverse image sends zero to zero. This is an elementary consequence, not a new lemma node.

Step 5 applies det-pe-classical-derived-equivalence only after checking its derived-unit hypothesis with sk-prop-sf-comparison. Each L_s is bounded below because it lies in [a,b]. The exact-functor cohomology statement and full faithfulness on sheaves prove that each chosen origin has the very same two bounds. I wrote out zero-object reflection and used def-sbc-standard-tstructure-derived-category for the meaning of the interval. Neither a bound on the morphism's cohomological dimension nor an unbounded equivalence is assumed.

Step 6 reads properness from def-weil-proper-morphism, quasi-compactness from def-weil-finite-type-morphism, and quasi-separatedness from lem-pc-separated-quasi-separated. The latter is an existing Mathlib leaf with exactly this conclusion. These establish the hypotheses of sk-thm-pe-direct-image-comparison. The common lower bound survives the coproduct by step 2. I constructed t and its inverse from the coprojections and identified alpha_Y by the same universal property; there is no additional transport lemma hidden in this step.

Step 7 uses the explicitly assumed étale coproduct preservation and inverse equations for the displayed factors, so it cites no external theorem. Step 8 uses the natural transformation explicitly stated in sk-thm-pe-direct-image-comparison. I checked source and target of its naturality equation at B_s to the sum B and wrote the cancellation calculation to get G(iota'_s) exactly. Coproduct uniqueness then proves equality with sigma_L for every choice of origins. This is a short elementary application of the cited naturality, not a restatement of a clause in a new node.

Step 9 checks the empty family separately: zero is bounded in every interval, theta_0 is therefore available, and coproduct uniqueness still works without components. I also checked a singleton family (the formula cancels to the canonical identity comparison), a family of zero objects, the degenerate interval a=b, the zero coefficient ring, and the identity morphism. There is no nonemptiness, nonzero-ring, invertible-characteristic, finite-type-over-a-field, or uniform cohomological-dimension hypothesis introduced by the proof.

Every cited node's statement was opened and its quotation in citations.json is an actual substring, not text from its proof. proof_deps is exactly the union of uses. The quoted generic results from other units are declared in split_report.tool_uses, with their purposes; they implement the comparison and ambient derived-category tools and do not replace the unit's route. All nine steps are shorter than 2000 characters. No new node is elementary, duplicated, a clause of the item, or an unsearched Mathlib fact, because there are no new nodes. The sandbox contains no Lean file or repository change.
