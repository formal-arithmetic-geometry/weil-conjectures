# Worker report: lem-cbc-ringed-open-extension-products

1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-cbc-ringed-open-extension-products.json`: existing statement, unchanged verbatim, re-split into a 2082-character assembly proof in five steps.
   - `dag/nodes/sec-smooth-purity/lem-cbc-retraction-product-comparison.json`: new statement, status unsplit; no Mathlib match. Extracts the open-restriction comparison and its projection-compatible identification, for arbitrary categories and functors.
   - `dag/nodes/sec-smooth-purity/lem-cbc-exact-pair-detects-isomorphisms.json`: new statement, status unsplit; no Mathlib match. Extracts joint detection of isomorphisms from joint detection of zero objects by exact functors.
   - Sandbox support: `citations.json`, the genuine `searches.jsonl`, and `original-item.json` preserving the complete original node and proof. No Lean, unit, chapter or repository file was changed.
2. Attachments: none. The exact blueprint tag has no match under `lean/WeilConjectures/`; related general extension/product occurrences do not state this item. I read the attached `lean/Sheaf/AlgebraicGeometry/ProEtaleRingedOpenExtensionProducts.lean` in full. It contains the implementation and the private helper `jointly_detect_iso`; these are reference material for extracting the work, not a reason to ignore the human's express re-split assignment. No compiler or axiom audit was run. The two new nodes have no new Lean attachment.
3. WANTED: none.
4. The defect being repaired is the human-identified concentration of proof work in one node, rather than a mathematical error. The arbitrary ring sheaf, quasi-compactness of the open, absence of ambient qcqs assumptions, all small families and naturality are retained. No STATEMENT-DISPUTED finding and no alteration of the unit's route.
5. No mathematical part left unfinished in the item. The two new nodes are deliberately statement-only for independent stage-1 workers. Their proof material is retained below rather than inserted into their statements or proof fields.

## Work distribution and preservation of the old argument

The old Step 1 (reduced complement and the precise ringed recollement hypotheses) remains Step 1. The old Step 2 becomes the new retraction lemma plus its application in Step 2. In particular its comparison is specified by projections, not by an unspecified isomorphism of endpoints, and the new statement retains the actual identity beta composed with J(c) equals theta_Q. The old Step 3 (closed restriction of both sides is zero) remains Step 3, with the product-of-zero-modules calculation explicit. The kernel/cokernel portion of old Step 4 is the new exact-pair lemma; its localization-based zero-detection hypothesis is verified explicitly in Step 4. The entire naturality argument and empty-family treatment of old Step 5 remain Step 5. Neither new node asserts that extension by zero preserves products: one concerns a comparison after a functor, and the other concerns an arbitrary morphism in any abelian category.

The original detailed arguments appear at the end of this report verbatim. The original item is also retained as `original-item.json` in the sandbox. Thus no argument is lost through shortening the parent; the new nodes intentionally carry no proof steps, as required by the re-split brief.

## Sources and searches

I read Stacks `proetale.tex`, lemma-j-shriek-limits (09BP), together with lemma-closed-immersion (09AA), lemma-open-immersion (09BN), lemma-jshriek-zero (09AG), and lemma-ses-associated-to-open (09AH). The source 09BP gives the abelian product result using a kernel expression; the existing ringed proof instead checks the particular comparison on the two restrictions. This re-split keeps that existing ringed argument. The source is not being claimed to state the new generic categorical results verbatim: those are agent-formulated extractions from this argument, and their source fields say so.

For the retraction lemma I read `categories.tex`, definition-product, Tag 002I, including its empty-index remark. The new assertion additionally packages the product-preserving J comparison and the natural theta projection calculation from old Step 2. The statement introduces both categories, both functors, a small index set, the required products, preservation, theta and its naturality, and both specified maps. Its equation is an assertion rather than a proof sketch.

For the exact-pair lemma I read `homology.tex`, lemma-exact-functor, Tag 010N, especially the proof identifying the image of a kernel with the kernel of the image map and its dual. I also read the existing private helper at lines 37-57 of the item's Lean module. This is the self-contained reusable kernel/cokernel argument, separate from all geometric and product inputs. It specifies preservation of zero morphisms, finite limits and finite colimits, the joint zero-object hypothesis, and an arbitrary morphism. It requires neither individual faithfulness nor individual conservativity.

Before creating either id I searched all DAG node statements and titles for joint detection, joint conservativity, zero-object detection, retractions and product comparisons; searched Stacks tags 002I, 010N and 09BP and related ringed tags; searched the whole blueprint with `tools/blueprint_refs.py search` for product comparison, jointly, retraction, zero objects, reflect isomorphisms, natural isomorphism and 010N; and searched both Lean roots by concept and the private helper name. The ancestor command gives `lem-cbc-completed-extension-zero-comparison`; both new nodes use that ancestor and via `[lem-cbc-ringed-open-extension-products]`. The precise ancestor paragraph was read in the current main-20261015 proof: the final countable-product parenthesis. The generic exact-sequence-reflection node assumes joint reflection of isomorphisms and therefore cannot supply our joint-zero-detection criterion. The joint-adjunction embedding node proves a monomorphism into a product, not reflection of arbitrary isomorphisms. The condensed-support derived localization node has different categories and coefficient hypotheses.

Every recorded new-node Mathlib query was actually run with `batch2/msearch.py` under NB and this item, with genuine results in `searches.jsonl`. Each node has LeanFinder, Loogle, LeanSearch and source grep; both conceptual questions were phrased twice. For the first I read the returned `piComparison`, `piComparison_comp_π` and `PreservesProduct.iso` in Shapes/Products and Preserves/Shapes/Products: they construct comparisons and prove the comparison invertible when that same functor preserves products. They do not identify J applied to the comparison for L from an isomorphism JL = id; in particular we must not assume L preserves products. The binary `prodComparison_comp` candidate concerns two objects, not arbitrary small S. For the second I read Functor/ReflectsIso/Jointly and Exact: `JointlyReflectIsomorphisms.isZero_iff` assumes joint isomorphism reflection and proves the zero criterion, which is the reverse implication. `Functor.reflects_exact_of_faithful` requires faithfulness, not our hypothesis. `exact_tfae` only characterizes preservation of exact sequences. The Serre-class candidate describes kernel/cokernel membership, and does not supply the joint criterion in one specialization. No direct match was found. No new node is a Mathlib leaf.

## Not duplicates

lem-cbc-retraction-product-comparison vs def-weil-category-product: the existing node defines a product and product of morphisms; the new node proves an invertible, projection-normalized comparison after J from JL naturally isomorphic to identity and preservation by J.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sfb-kernel-cokernel-finite-exactness: the existing node derives finite (co)limit preservation from kernel/cokernel preservation; it has no joint zero detection or isomorphism-reflection conclusion.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sfb-preserving-colimits-additive: the existing node derives additivity of one functor from finite-colimit preservation; it has no joint detection criterion.

lem-cbc-exact-pair-detects-isomorphisms vs lem-pc-single-degree-exact-term-hom-quasi-iso: the existing node concerns internal Hom from a single-degree sheaf complex and quasi-isomorphisms, not joint reflection by two functors on abelian categories.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sfb-local-homology-quasi-iso: the existing node transports a homology isomorphism forward under a functor with specified local kernel and cokernel preservation; the new node reflects arbitrary isomorphisms using two exact functors and zero detection.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sp-exact-functor-half-plane: the existing node transports large-page spectral-sequence data and filtrations; it has no zero-object detection hypothesis or joint isomorphism-reflection conclusion.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sp-exact-functor-preserves-homology: the existing node supplies kernel/cokernel and homology preservation by one exact functor; it does not reflect isomorphisms from joint detection of zeros.

lem-cbc-exact-pair-detects-isomorphisms vs lem-weil-pbc-exact-functor-complex-cohomology: the existing node constructs a cohomology-commutation isomorphism for one exact functor; it does not prove joint reflection of isomorphisms.

lem-cbc-exact-pair-detects-isomorphisms vs lem-weil-pbc-abelian-presheaves-evaluation-exact: the existing node proves exactness of presheaf evaluations; it has no abstract joint-zero-detection-to-isomorphism criterion.

lem-cbc-exact-pair-detects-isomorphisms vs lem-weil-cohomology-commutes-scalar-extension: the existing node concerns scalar extension of vector-space complexes and its cohomology; it has no arbitrary abelian-category joint reflection assertion.

lem-cbc-exact-pair-detects-isomorphisms vs lem-weil-pbc-jointly-reflect-short-exact: the existing node assumes joint reflection of isomorphisms and deduces reflection of short exactness; that assumption is the conclusion needed here.

lem-cbc-exact-pair-detects-isomorphisms vs lem-sfb-joint-adjunction-model-embedding: the existing node assumes right adjoints and proves an adjunction/product map monic, rather than arbitrary morphisms invertible from their images.

## Review by NB

I checked delivery-errors B through E with the source, all cited statements, and both new files open. This is direct self-review under the explicit brief, not a claimed second worker review. New nodes have complete, smaller statements and no proof or proof dependencies. Source tags and labels were read, no source serves as the meaning of a notion, and definitions are cited or stated inline. Both nodes are in the item's chapter and unit. No SGA source is used.

Step 1 cites the reduced-induced-closed-subscheme statement specifically for clause (2), the reduced scheme whose image is the given closed subset. The ringed-open-closed statement explicitly assumes only a closed immersion, complementary quasi-compact open, and arbitrary ring sheaf before its separate filtered-colimit qcqs clause. Its actual statement supplies JL isomorphic to identity, IL = 0, exact L and closed direct image, and the exact localization sequence. I did not use that node's proof in place of its statement. The reduced structure on the complement imposes no condition on X.

Step 2 cites module-sheaves-limits-sectionwise for product existence, immersion-limit-preservation for the open inverse image's preservation, and the new retraction statement for the actual equality beta J(c) = theta_Q and invertibility. The inputs match: its A is modules on U with R restricted, its B is modules on X, its L and J are precisely these functors, and theta is the natural identification obtained in Step 1. The slice presentation and induced module action are already part of the item and of ringed recollement. No faithfulness or preservation by L is smuggled into this step.

Step 3 cites immersion-limit-preservation for the closed restriction and ringed-open-closed for IL = 0; the sectionwise limit statement gives the final product. Each value is the product of zero modules. There is exactly one section, including for an empty tuple, so the product is a zero module. A map between zero objects has the unique map in the other direction as inverse. These last assertions are elementary deductions, not hidden general preservation assumptions.

Step 4 uses the ringed localization sequence only to verify joint zero detection. Its outer terms vanish because the stated exact functors preserve zero objects. Module-sheaf-category explicitly states abelianness for the chosen small/essentially small site universe. Immersion-limit-preservation states additivity and exactness for arbitrary ring sheaves, giving preservation of zero morphisms and both kinds of finite (co)limits. The new exact-pair statement then gives isomorphism reflection for this particular c. The original nontrivial kernel/cokernel comparison proof is assigned to that new node; it is not marked elementary or silently omitted.

Step 5 uses sectionwise products and exactness of L from recollement. The projection calculation is written: both maps have component L(a_s composed with pr_s). Product uniqueness and functoriality are elementary. Naturality for inverses follows by composing the square with the two inverse comparisons. Empty products in module categories are the zero module sheaves, and exact L sends zero to zero.

For the retraction statement I tested S empty (all products terminal and both maps uniquely determined), singleton S, L = J = id with theta a natural automorphism, and a retraction whose L is not assumed product-preserving. Nothing claims that c itself is invertible at this stage. The formula is correctly typed JP to Q and beta J(c) from JLQ to Q. For the exact-pair statement I tested a zero source category, one of J/I zero with the other conservative, and both functors zero. In the latter case the hypothesis forces every source object zero; without that hypothesis it would fail on 0 to a nonzero module. No individual functor is required to be faithful. In the geometric application I checked the empty open, identity open, empty scheme, zero coefficient ring, empty and singleton index sets and a non-quasi-compact ambient X. Only the specified quasi-compactness of j is used.

The re-split corrects work allocation only. I preserved the statement and stmt_deps byte-for-byte, maintainer metadata, the existing blueprint ancestry, and the previous mathlib_searches. The two substantial extracted arguments can be implemented independently: open comparison by naturality/projection identities and isomorphism detection by preservation of kernels and cokernels. The remaining assembly is 2082 characters and no individual step exceeds 2000 characters. The closed vanishing calculation, localization zero test and family-map naturality are short deductions from cited statements; turning those into additional nodes would create elementary-node clutter. `citations.json` contains a verbatim useful clause for each citation of each proof step, including the new nodes.

## Validation

The required `deliver.py NB lem-cbc-ringed-open-extension-products --no-push` exited successfully: server preflight passed and printed `OK (not pushed)` for c2962fbc98b. This report update is followed by a final dry run before the direct push. No Lean writing, compilation or local DAG/preflight check was run.

## Original proof retained for the two new workers

Old Step 1:

Let $i:Z\hookrightarrow X$ be the reduced induced closed subscheme on $|X|\setminus j(U)$, supplied by [lem-weil-pbc-reduced-induced-closed-subscheme]. Write $L=j_!$, $J=j^{-1}$ and $I=i^{-1}$, with coefficients $R$, $J R=R|_U$ and $I R$ respectively. The ringed recollement statement [lem-weil-pbc-proetale-ringed-open-closed] applies: its hypotheses are precisely a closed immersion, its quasi-compact open complement and an arbitrary commutative ring sheaf. In particular there is a natural isomorphism $\theta:JL\xrightarrow{\sim}\mathrm{id}$, one has $IL=0$, and every $R$-module sheaf $M$ has the short exact sequence $0\to LJM\to M\to i_*IM\to0$. These assertions require no quasi-compactness or quasi-separatedness of $X$.

Cites: lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-proetale-ringed-open-closed.

Old Step 2:

Put $Q=\prod_s F_s$ and $P=\prod_s LF_s$, and let $c:LQ\to P$ be the map with components $L(\mathrm{pr}_s)$ in the question. These products exist as sectionwise module limits by [lem-weil-pbc-module-sheaves-limits-sectionwise]. Apply [lem-weil-pbc-proetale-immersion-limit-preservation] to the open immersion $j$. It gives an isomorphism $\beta:JP\xrightarrow{\sim}Q$ whose component at $s$ is $\theta_{F_s}\circ J(\mathrm{pr}_s)$. Naturality of $\theta$ gives $\mathrm{pr}_s\circ\beta\circ Jc=\theta_{F_s}\circ JL(\mathrm{pr}_s)=\mathrm{pr}_s\circ\theta_Q$. By the product universal property, $\beta\circ Jc=\theta_Q$, so $Jc$ is an isomorphism. The natural identification $JL\cong\mathrm{id}$ used here is exactly the one asserted in [lem-weil-pbc-proetale-ringed-open-closed]; no identification of an unrelated adjunction unit is required.

Cites: lem-weil-pbc-module-sheaves-limits-sectionwise, lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed.

Old Step 3:

Apply [lem-weil-pbc-proetale-immersion-limit-preservation] to the closed immersion $i$. Its module inverse image preserves all products, hence $IP\cong\prod_s ILF_s=\prod_s0=0$, using $IL=0$ from [lem-weil-pbc-proetale-ringed-open-closed]. The last equality follows sectionwise from [lem-weil-pbc-module-sheaves-limits-sectionwise]: the product of any small family of zero modules is the zero module, also when the family is empty. Likewise $ILQ=0$. Thus $Ic$ is the unique map between two zero objects and is an isomorphism.

Cites: lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-module-sheaves-limits-sectionwise.

Old Step 4:

The module-sheaf categories are abelian by [def-weil-sheaf-of-modules-category]. Let $K=\ker c$ and $C=\operatorname{coker}c$. Both $J$ and $I$ are exact by [lem-weil-pbc-proetale-immersion-limit-preservation], so Steps 2 and 3 give $JK=IK=JC=IC=0$. For either $M=K$ or $M=C$, the sequence of [lem-weil-pbc-proetale-ringed-open-closed] now has zero outer terms: $LJM=L0=0$ because $L$ is exact, and $i_*IM=i_*0=0$ because $i_*$ is exact. Hence $M=0$. Thus $c$ has zero kernel and cokernel and is an isomorphism in the abelian module category.

Cites: def-weil-sheaf-of-modules-category, lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed.

Old Step 5:

For a map of families $(a_s:F_s\to G_s)_s$, compare the two maps from $L(\prod_sF_s)$ to $\prod_sLG_s$. Their $s$-th components are both $L(a_s\circ\mathrm{pr}_s)=L(a_s)\circ L(\mathrm{pr}_s)$, so they agree by the product universal property. This proves naturality of the specified comparison, and of its inverse since each component comparison is invertible. If the index set is empty, both products are terminal zero module sheaves and $L0=0$ by exactness, so the unique comparison is again an isomorphism. The cases $U=\varnothing$, $j=\mathrm{id}_X$, $X=\varnothing$ and the zero coefficient ring are included by the same formulas.

Cites: lem-weil-pbc-module-sheaves-limits-sectionwise, lem-weil-pbc-proetale-ringed-open-closed.
