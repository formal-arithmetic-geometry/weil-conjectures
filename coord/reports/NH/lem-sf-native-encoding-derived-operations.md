Files written:

- `dag/nodes/sec-six-functors/lem-sf-native-encoding-derived-operations.json`: statement split into seven proof steps; no new nodes; no Mathlib leaf.
- `citations.json`: 26 verbatim statement citations, one for every node used by every step.
- `searches.jsonl`: the six msearch searches run for the item are retained.

Attachments: none. I found no sorry-free upstream declaration stating this complete native encoding and derived-operation comparison; the existing declarations only cover component definitions or individual finiteness results.

WANTED: none. The Bhatt–Scholze PDF and the Stacks sources used below are present in `literature/`.

The imported item is an agent-formulated native comparison statement. Its source explicitly says that Bhatt–Scholze supplies the module model but not the whole native encoding theorem, so I kept the statement and supplied the missing construction and comparison argument. I did not change its hypotheses or conclusion. I found no duplicate node with the same complete statement; existing coefficient and fixed-pair nodes are cited as generic tools rather than restated.

No part of the proof was left unfinished. No Lean file was written and no compiler, Lake or build tool was run.

## Review by NH

I read the item node, the native framework definition, the finite-span coefficient comparison, the internal module-operation transport, the fixed-pair derived-forgetting comparison, and the exact-square K-injective comparison. I also read the source files named by the item: `WeilConjectures/SixFunctors/ProEtale/Adic/Module.lean` for the native module category and pullback, `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean` for preservation of K-injectives and the derived comparison, and `WeilConjectures/WeilSheaf/LowerStar.lean` plus `WeilSheaf/Category.lean` for the native Frobenius transport and direct-image construction. The literature check used Bhatt–Scholze Definitions 6.8.1, 6.8.3 and Remark 6.8.15, Stacks Tags 03D6, 03D7, 03EK, 015F, 070I, 070Y and 079Q, and the statements of every cited DAG node were opened before writing `citations.json`.

Step 1 is the only newly explicit encoding argument. It uses the framework's definition of a $B_T$-module object, the sheafified tensor definition, and the underlying native category; the constant function $c_a$ supplies the inverse $Omega$-action. I checked the edge cases $a=0$, the zero module, and an empty site: the unit and associativity equations still give inverse actions, and no nonempty-object assumption is used. I corrected the first draft's `elementary` flag to `false`, because the step is a genuine construction even though it is short.

Step 2 uses the existing finite-span comparison for the sectionwise $R_T$-module category and the existing equivalence lemma for exactness. It verifies that both directions preserve the underlying abelian sheaf and restrictions, and that scalar transport is along the stated ring isomorphism $\theta_T$; no claim about constructibility is smuggled into the encoding.

Step 3 uses the exact-functor descent statement and the definition of K-injective complexes. The Hom-in-the-homotopy-category calculation is the required hypothesis-by-hypothesis check: an acyclic source stays acyclic under an exact equivalence, and the quasi-inverse gives reflection. This establishes the ordinary unbounded derived equivalence without imposing boundedness.

Step 4 uses the finite-span operation comparison, the cartesian-coefficient isomorphism, the ring-realization comparison, the module pushforward/pullback definition, and the native framework. I checked the direct-image action is precomposition on sections and the pullback is $B_X\otimes_{f^{-1}B_Y}f^{-1}(-)$. The coefficient square is exactly $\theta_X\alpha_f=\rho_f f^{-1}\theta_Y$; invertibility of $\alpha_f$ is the cited reason pullback is exact. Applying the same square to Frobenius automorphisms gives the required coefficient-map compatibility.

Step 5 uses the small-site Grothendieck module theorem, the exact equivalence lemma, the finite-span comparison, the fixed-pair derived-forgetting theorem, and the native framework/module-operation definitions. I checked that the common larger universe is part of the item hypotheses, that $B_T$-module categories are Grothendieck, and that geometric Frobenius and its inverse provide the autoequivalence hypotheses. The natural isomorphism $F_Y^*f_*\cong f_*F_X^*$ is the native Frobenius transport, so the fixed-pair theorem applies to the actual native direct image.

Step 6 applies the exact-functor derived factorization to native pullback. Since the coefficient map is invertible, the module pullback is exact and is computed degreewise; this is precisely the stated $Lf^*=f_R^*$ comparison. I checked that no K-injective choice is needed for this side.

Step 7 uses the exact-square K-injective comparison, the fixed-pair derived-forgetting comparison, the right-derived-functor definition, and the module derived push-pull definition. For a native Weil K-injective resolution I checked that forgetting Frobenius and then applying the coefficient equivalence gives K-injective representatives on both sides, and that the two derived direct images are represented by the same underived comparison. The normalization on the resolution is the given Frobenius transport map. The argument is on the ambient unbounded categories and introduces no constructibility or properness condition.

I ran all required Mathlib searches recorded in `searches.jsonl`: LeanSearch, LeanFinder, Loogle and Mathlib-source grep with the exact query strings copied into the item. The hits were generic sectionwise sheaf, scalar-restriction and site-equivalence declarations; none states the native vector-module plus Frobenius-equivariant unbounded comparison, so no Mathlib leaf was attached. No new node was created, hence there is no duplicate-node pair to record.
