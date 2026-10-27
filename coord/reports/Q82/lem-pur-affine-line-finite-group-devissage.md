# Worker report: Q82

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-affine-line-finite-group-devissage.json`: statement, now split in seven steps; no Mathlib match for the geometric canonical-map assertion.
- `citations.json`: verbatim statement evidence for all 16 step/node citations.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. `searches.jsonl` records the actual Q82 searches; `prepare.py` is a sandbox-only reproducibility script, not part of the delivery. No Lean, compiler, Lake, library writes or worker-run git commands were used.

## Attachments

None. The project search for `(blueprint: lem-pur-affine-line-finite-group-devissage)` and the item id found no declaration. I read `WeilConjectures/AlgebraicGeometry/Curve/AffineLineKummer.lean`, especially lines 290-318. `AlgebraicGeometry.AffineSpace.subsingleton_sheafH_constantSheaf_line` proves positive-degree vanishing, not all the item's clauses. The relative results in `EtaleCohomology/Purity/Smooth/AffineLine.lean` and `AffineLineRelative.lean` concern constant ring coefficients or constructible finite-Tor module complexes and do not directly state the canonical bounded-below abelian constants comparison for every finite primary group, its naturality, and the order assertion. Thus this is not an ATTACH claim.

## WANTED

None.

## Audit and changes

The live item was statement-only and no earlier sandbox split or report existed. I copied it, retained its statement, source, provenance, inherited searches and blueprint chain, and supplied the proof. There is no released repair note for this item. The chapter, unit, GOAL and the three levels in SETUP were read. This is not the unit's key statement, so no unit record was changed.

The proof follows the current `main-20261015` affine-line Kummer proof's Coefficients, Clause (c), and Degrees 0 and 1 paragraphs. Its prime coefficient calculation is an existing node; its extension from prime cyclic groups to every finite primary group is an explicit cardinality induction. The nearest blueprint ancestor remains `lem-pur-frame-independence`, Shear paragraph, through ordinary and supported affine-line invariance. I also read the ancestor's current proof in `sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md`.

The imported `def-sc-mu-trivialization` statement says merely “Given a root of unity,” whereas its current blueprint explicitly says “Given a primitive ... root.” The claimed isomorphism needs primitivity (the choice 1 would fail for n>1). This delivery does not edit that other node: Step 2 explicitly obtains and uses a primitive root from `lem-sc-primitive-root`, so it satisfies the correct hypothesis and never applies the defective wording to an arbitrary root. The item's statement itself needs no correction.

Mathlib search was repeated under Q82 using the prescribed command, with two geometric semantic phrasings, LeanSearch, Loogle and source grep. The returned affine-space coordinates, algebraic formal-etaleness facts, sheaf-cohomology definitions and unrelated homology vanishings are not this assertion. A separate logged algebra search returned `IsPGroup.exists_card_eq` and related p-group facts; no node was created from it because the required prime cyclic subgroup and order assertion have the explicit elementary induction below. The original Q116 search records were preserved.

Whole-DAG and whole-blueprint searches included affine line, constant coefficients, prime cyclic, prime order, annihilated, and the relevant existing ids. I reused the Kummer root computation, primitive-root existence, abelian sheafification exactness and homological tools instead of creating duplicates. The finite-free Kummer theorem alone would not cover an arbitrary group annihilated by a prime power; no freeness was silently inserted.

## Review by Q82

I read delivery-errors B through E in full and checked each step against the cited node statements, not their proofs. I also read the current blueprint proof of sk-prop-a1-kummer, the current primitive-root and trivialization texts, and the local Stacks source for the homological passages. The proof is agent-written because the precise arbitrary-primary-group induction and canonical resolution maps refine the blueprint argument.

Step 1 states the simultaneous strong induction, including the order assertion, constants in degree zero and all positive-degree vanishings. `def-weil-pbc-constant-sheaf` gives sheafification of the constant presheaf; `lem-weil-pbc-sheafification-exact` preserves zero, giving the zero coefficient sheaf. `def-weil-pbc-sites-and-cohomology` gives its resolution formula. The zero resolution consists of injectives, so this base case is literal, with group cardinality 1 = ell^0. These are elementary consequences of the cited statements.

Step 2 uses `lem-sc-primitive-root` for existence, with ell positive and invertible in the algebraically closed field. `def-sc-mu-trivialization` supplies the displayed sheaf isomorphism, used only for that primitive root. `lem-pur-kummer-root-line-computation` says exactly that for the affine-line index the positive cohomology vanishes and its H0 equivalence takes 1 to the constant root. Applying H0 to the sheaf isomorphism identifies the constants map, not an unspecified group isomorphism. The computation's hypotheses are m=ell>=1, invertibility in k and primitivity; all were checked. Its underlying source is the Kummer/affine-curve argument of the current blueprint, Stacks 03PL and 03SC. I did not assume that the choice of root is canonical.

Step 3 constructs the subgroup rather than citing Cauchy's theorem without a node. From nonzero x choose the least positive r with ell^r x=0. The preceding power y is nonzero and killed by ell. Bezout for a nonzero residue j modulo ell shows that j*y cannot be zero, so the cyclic subgroup K has exactly ell elements. Translation bijects K with each coset. Counting the finite cosets gives |D|=ell*|D/K|, and the quotient has smaller cardinality and the same annihilating power. These elementary arguments are written in the step; they do not warrant a new node.

Step 4 uses `def-weil-pbc-constant-sheaf` and the exact abelian sheafification statement to get the actual short exact sequence of abelian sheaves. I read Stacks sites.tex, lemma-sheafification-exact (00WJ), and sites-modules.tex, lemma-abelian-abelian (03CN) and lemma-limits-colimits-abelian-sheaves (03CO), including the sectionwise-kernel and sheafified-colimit explanations. I deliberately used the abelian statement to avoid assuming that a module-valued calculation has already been compared with abelian cohomology. `def-weil-pbc-sites-and-cohomology` supplies enough injectives and additive left-exact global sections; `lem-weil-pbc-derived-functor-long-exact` supplies exactly the H0 and positive-degree sequences required. Its source is derived.tex, lemma-higher-derived-functors, Tag 015B (1)-(2), which I read. The H1(K)=0 needed to end the H0 sequence comes from Step 2. The constants square commutes because the sectionwise maps send a constant to its coefficient image.

Step 5 uses the exact segments already established, so no further citation is hidden. I wrote the injectivity and surjectivity chase instead of citing an unstated five lemma: lift to D after using c_Q inverse and correct the difference with a K section. Positive vanishing has zero groups on both sides of Hq(D); the cardinality assertion uses the same subgroup and quotient induction. This is the whole inductive step, with the smaller quotient and the base case identified in advance. No new node merely restates a clause of this item.

Step 6 uses the actual map B[0] -> Gamma(C,I), consisting of constant sections followed by the resolution augmentation. Its differential is zero because the augmentation lands in cycles. The resolution formula is `def-weil-pbc-sites-and-cohomology`; the meaning of quasi-isomorphism and its inversion is `def-weil-abstract-derived-category`. I read derived.tex, section-derived-categories (05RR), definition-unbounded-derived-category (05RU), and lemma-acyclic (05RT). The map induces c_B on H0, both complexes have zero negative terms, and positive cohomology is Step 5, so it is precisely a quasi-isomorphism of bounded-below complexes. No separate theorem asserting conservativity on arbitrary derived morphisms is smuggled into a definition citation.

Step 7 uses `lem-weil-pbc-lift-along-injective-quasi-iso` for a strictly commuting resolution lift and `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` for its independence. I read their actual Stacks statements in derived.tex, lemma-morphisms-lift (013P (2)) and lemma-morphisms-equal-up-to-homotopy (013S). The augmentation is a degreewise monic quasi-isomorphism, including all zero degrees, and the target resolution is bounded below and termwise injective. Evaluating the strict lift equation gives the precise naturality equation, not a claim that the maps “transport.” Sections preserve the homotopy equation term by term. `lem-weil-pbc-bounded-below-homotopy-invariance` is applied to localization of abelian-group complexes, which inverts quasi-isomorphisms by the cited abstract-derived-category statement; it is not applied to global sections on arbitrary sheaf quasi-isomorphisms. Resolution comparisons and their inverses are checked by the same uniqueness statement. This proves derived naturality, even when source and target coefficient groups require different annihilating powers, since the comparison argument itself uses no common exponent.

The homological statements outside the unit are generic tools, listed in `split_report.tool_uses` with their purposes. They implement the unit's coefficient devissage rather than replacing its Kummer route. Every cited statement was reopened for this review and its used clause copied verbatim into citations.json. There are no new-node statements needing further source or duplicate comparisons. Every non-elementary step is shorter than 2000 characters; none contains an unextracted “standard comparison.”

For small cases I checked B=0, B=Z/ell, B=Z/ell^2, and B=(Z/ell)^2 viewed as a Z/ell^2-module. The last two use the same prime subgroup and quotient argument; the last is not free over Z/ell^2, showing that the proof does not rely on the free-module case. With ell=2 the Bezout argument still applies, and the order exponent for B=0 is 0. The assumptions exclude ell=char(k), as required for the Kummer input. Negative degrees vanish in the chosen nonnegative resolutions. Identity, zero and composable coefficient maps satisfy the displayed chain-level naturality equation, which survives localization.

## Not duplicates

No new nodes. Existing results are cited, and the order-ell subgroup, finite-coset count and H0 diagram chase remain elementary steps.

## Unfinished work

None in this one-level split. The item's non-elementary mathematical inputs remain in their existing nodes. A server review_split check passed with zero new nodes before this report; final delivery preflight is run next.
