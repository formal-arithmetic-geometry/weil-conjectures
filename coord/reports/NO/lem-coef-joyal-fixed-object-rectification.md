# Stage-1 delivery: lem-coef-joyal-fixed-object-rectification

## Files written

- dag/nodes/sec-six-functors/lem-coef-joyal-fixed-object-rectification.json: statement, split into fourteen proof steps; not in Mathlib.
- dag/nodes/sec-six-functors/lem-coef-joyal-presentable-monoidal-localization.json: new statement-only foundational node; not in Mathlib.
- dag/nodes/sec-six-functors/lem-coef-cartesian-matrix-model.json: new statement-only foundational node; not in Mathlib.
- citations.json: verbatim statement paragraphs for every proof-step citation.

## Attachments

None. Searched all WeilConjectures/ in slopmaster2 for the exact blueprint tag and for rectification, Joyal and fixed-object terminology. No matching declaration. Upstream master is reference material only; it provides no attachment. The Mathlib simplicial-category definition and strict bicategory of quasicategories are not this theorem.

## Wanted literature

WANTED: Rune Haugseng, Rectification of enriched infinity-categories, arXiv:1312.3881v4, Definitions 3.16 and 5.1, Lemmas 3.19-3.20, Proposition 5.2, for the item. Read the online HTML version; no shared archival copy was found.

WANTED: Fernando Muro, Homotopy theory of nonsymmetric operads, Algebraic & Geometric Topology 11 (2011), Definition 10.1, Remark 10.2, Proposition 10.3, printed pp.1595-1597, for lem-coef-cartesian-matrix-model. Read the online PDF.

WANTED: Jacob Lurie, Higher Topos Theory, Theorem 2.2.5.1, Corollary 2.2.5.4, Proposition 2.2.5.8 and the model-category localization background; Higher Algebra, section 1.3.4 and Proposition 4.1.7.4 / Example 4.1.7.6, for lem-coef-joyal-presentable-monoidal-localization. Read the online PDFs.

No Stacks tag states these infinity-categorical/model-theoretic results. No SGA source is used. The item's proof_origin is agent because the available local source is the agent-written blueprint; the online references and missing shared archives are explicit.

## Issues found and changes

The item was unsplit and its specialized source reference did not supply a checked proof. Its statement is retained without a change. In particular this is the fixed-object localization at homwise categorical equivalences, not a varying-object DK localization, and the algebras on the right are not subjected to completeness. The existing similarly named enriched rectification is for chain complexes, and the existing simplicial free calculus is for Kan weak homotopy equivalences: neither can be used as a Joyal theorem.

I supplied the two genuine missing inputs below the item: structural properties of the Joyal base and the matrix convolution model on graphs. The latter is about graphs before any associative algebra is formed. Neither new node restates a clause of fixed-object rectification. Transfer, word filtration, cellular factorization, sifted-colimit preservation, the free categorical-algebra formula and the infinity-monadic comparison all already have nodes and are reused. No unit statement or route is changed; this foundation supports the coherent mapping-adjunction paragraph of prop-coef-integral-exceptional-adjoint through the existing ancestry.

The ordinary strict path product is in reverse order and the categorical-algebra free product is in forward order. The comparison uses cartesian reversal explicitly. The analogous chain-complex sign argument is not copied here. I also used a fibrant replacement of the target in the conservativity argument: Joyal-enriched categories need not all be fibrant.

## Unfinished work

No part of this item's split is left unfinished. The two new nodes are intentionally unsplit and contain statements only. Stage 2 and all Lean/compiler operations are excluded.

## Not duplicates

lem-coef-joyal-presentable-monoidal-localization vs lem-coef-joyal-model-structure: the existing statement gives the two weak factorization systems and quasicategory fibrancy, but does not assert left properness, combinatoriality, or identify its symmetric monoidal infinity localization with cartesian Cat-infinity.

lem-coef-joyal-presentable-monoidal-localization vs lem-coef-cat-infinity-colimits-cartesian-closure: the existing statement describes coherent limits, colimits and exponentials in Cat-infinity, without the Joyal presentation, saturation, or its ordinary combinatorial model structure.

lem-coef-joyal-presentable-monoidal-localization vs lem-coef-combinatorial-localization-presentability: the existing theorem assumes a combinatorial monoidal model category; it does not prove those hypotheses or the Cat-infinity identification for Joyal simplicial sets.

lem-coef-cartesian-matrix-model vs lem-coef-graph-product-model: the existing product model is only for graphs of chain complexes over a commutative ring; the new statement has an arbitrary all-cofibrant cartesian model base and a nonsymmetric convolution model structure.

lem-coef-cartesian-matrix-model vs lem-coef-matrix-biclosed-monoidal-structure: the existing statement is only for chain-complex graphs and only the biclosed monoidal structure; it cannot supply the Joyal graph model or monoid axiom.

lem-coef-cartesian-matrix-model vs lem-coef-associative-algebra-model-transfer: the latter assumes a biclosed monoidal model category and monoid axiom, then transfers to its algebras. The new node constructs precisely the graph base to which that theorem applies, without asserting a model structure on enriched categories.

Blueprint searches: ancestor item gives prop-coef-integral-exceptional-adjoint; searches rectification, monadic, categorical algebra, monoidal model, Joyal, matrix, graph, left proper, convolution were read. No blueprint node states either new result. DAG statement searches also checked the existing dg and Kan variants named above. Lean concept searches found no missing attachment. Mathlib searches are actual msearch.py calls with the original service output in searches.jsonl; second semantic phrasings were tried. The pointwise Pi monoidal structure was read and rejected: it has no sum over intermediate vertices. Kan-Quillen boundary/horn code and the quasicategory bicategory code were read and rejected for the Joyal localization claim.

## Review by NO

I read Haugseng's Lemma 3.20 and its matrix argument, Definition 5.1 and all six parts of the proof of Proposition 5.2, including the free monad formula and the naturality paragraph. This is the source route of the item, with the already existing comparison criterion replacing an uncited appeal to monadic recognition. I read Muro's Definition 10.1 through Proposition 10.3 for the graph node: its nonsymmetric matrix tensor and the two exponential formulas use the same indices as our statement. The extra left properness is coordinatewise, and the all-cofibrant assumption makes every auxiliary initial map a cofibration; iterated pushout products with a trivial input and their cellular closure are trivial cofibrations, so the stronger nonsymmetric monoid axiom is valid. For the Joyal node I read HTT Theorem 2.2.5.1 and the boundary-generation argument in its proof, the cartesian equivalence corollary, the comparison of definitions in Proposition 2.2.5.8, and HA's construction of the monoidal localization. No simplicial model-category axiom for the Joyal model is assumed: cosimplicial frames are used instead.

I opened every node cited by a proof step and checked its statement. Step 1 uses the new Joyal structural node, the existing cartesian pushout-product node and the new graph node only for their explicitly stated properties. Step 2 applies algebra transfer with every monoidal-model hypothesis verified in step 1; the terminal category is computed, and fibrancy is exactly the existing Joyal fibrancy criterion. Step 3 uses the boundary-cell theorem, Joyal cofibrations, coordinate generators and the transfer generator clause; cellular factorization applies because the transferred category is locally presentable. Its lifting/retract diagram gives the asserted characterization, including domain-fixed retracts.

Step 4 uses the actual free-word adjunction, with matrix powers expanded and the empty-path unit retained. Step 5 uses the frame theorem's actual Kan mapping-space formula; a family of these frames is a frame because graph latching colimits and classes are coordinatewise. The full-essential-image theorem then promotes full faithfulness plus coordinate representatives to an infinity-equivalence. Step 6 invokes precisely the derived Quillen adjunction and combinatorial presentability, not an ordinary homotopy-category adjunction. Discrete coproducts are derived by the coproduct/diagonal adjunction, and all entries are cofibrant. Step 7 represents an arbitrary arrow by a map from a cofibrant source to a fibrant target using the frame statement; the new Joyal saturation clause then detects its homwise equivalences.

Step 8 applies the sifted-localization theorem to the graph model rather than assuming the algebra model itself left proper; the theorem's hypotheses are properties of the base. Its conclusion explicitly includes geometric realizations. The existing categorical-algebra free-monad statement gives the other side's left adjoint, conservativity and realization preservation, as well as the forward path formula. Steps 9 and 10 construct an actual operator comparison by strong monoidal localization, check block-substitution and empty blocks, and descend it through localization using the functor-category universal property. The free algebra theorem's conservative clause detects algebra equivalences; no proof internal to that node is used.

Step 11 checks the canonical adjunct of the specified unit, using the free algebra theorem's clause describing exactly that adjunct on each path. Its product permutation is an equivalence at length zero, length one and every positive length. Step 12 applies the existing monadic comparison only after recording all its hypotheses. Step 13 writes the substitution for a function of object sets on both sides and explains why all composition diagrams descend together; functorial localization is an existing cited statement, not an unexplained claim of compatibility. Step 14 factors in the fixed-object model category and transports the specified algebra equivalence to a fibrant representative; it keeps object labels and units rather than making independently chosen hom equivalences.

Small cases were checked before writing: for O empty the graph category and both algebra categories are terminal and there are no generating arrow cells; for one object matrix convolution is the base product and transfer gives associative monoids, not commutative ones; for two objects the off-diagonal unit is empty and each convolution summand has the correct source and target. Loops and n=0 boundary cells add arbitrary endomorphism vertices, and repeated or collapsed labels under O to O' preserve the substituted composition formulas. The nullary free path occurs only on the diagonal. The generic graph statement does not assume its nonsymmetric matrix tensor is cartesian or symmetric. No properness on the right is invoked, which would be false for the Joyal model. All fourteen proof steps are shorter than 2000 characters, and their mathematical arguments and hypotheses were checked, not merely their lengths. Every new unsplit statement has empty proof and proof_deps, explicit notions, ancestry and real logged searches. There are no statement disputes or source errors requiring a changed statement.
