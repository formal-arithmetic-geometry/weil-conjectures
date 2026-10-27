# Q158 repair report

1. Files written: the item JSON (unchanged statement, five assembly steps), and three new statement-only nodes in dag/nodes/sec-six-functors/: `lem-sf-open-roos-extension-comparison` (statement, unsplit, no Mathlib match); `lem-sf-open-tensor-augmentation-limit-square` (statement, unsplit, no Mathlib match); `lem-sf-open-roos-restriction-unit` (statement, unsplit, no Mathlib match). There are 3 new nodes and 0 Mathlib leaves. citations.json records every assembly citation. searches.jsonl contains the actual new searches.
2. Attachments: none. The project's OpenProjectionRoosCompletion theorem is still `by sorry`. Searching WeilConjectures by the item id and the Roos/completion concepts found no finished declaration of the whole item. The prior Q140 attachment findings remain preserved below.
3. WANTED: none.
4. Return repaired: the nine-step 8325-character proof was too much work in one item. Its statement, original literature, searches and metadata are retained. Old steps 1–2, 4–6 and 7–8 are assigned to three independent work packages; old steps 3 and 9 stay in assembly. No new node defines Gamma or states the whole theorem. The first and third apply to arbitrary strict towers, independently of tensor factors. The second concerns the pre-Gamma augmented square and invertible quotient units. The new statements have no proof or proof dependencies. Their full inherited arguments are preserved verbatim below for their future workers; no argument was shortened away.
5. Unfinished: the new nodes are intentionally unsplit, for separate workers to prove. This delivery completes the required one-level repair; it asserts no Lean proof completion.

## Source and search review

I read the worker and stage-1 rules, the three blueprint levels in SETUP.md, GOAL.md, the chapter/unit records, and both copies of delivery-errors B–E. The main-20261015 prop-sf-pf-coherence open-factor proof is the route. Stacks proetale.tex Tag 09BP (lemma-j-shriek-limits, lines 5185 ff.) supplies the product/limit input; it requires a quasi-compact open immersion. Stacks sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok, lines 5067 ff.) supplies the strict tower derived-limit source, and Tag 0GL1 (lemma-j-shriek-and-tensor, lines 4578 ff.) supplies the ordinary tensor formula. I read Bhatt–Scholze pp.49–50, Lemma 6.5.5 and Lemma 6.5.8(2),(3), including their constructible and qcqs hypotheses. New A follows the 09BP/Roos application, new B follows the constructible completion and augmented-square refinement, and new C follows the sectionwise restriction and two-functor Roos-unit refinement. The normalized refinements are agent-formulated, not claimed verbatim from these sources. The preserved argument below states their sources and cited statements precisely. No forbidden source route is used.

Whole-DAG searches used the relevant tags and Roos/open tensor/augmentation/unit keywords. Whole-blueprint searches used blueprint_refs.py for Roos, augmentation, open tensor, strict limit, and restriction unit, and ancestor returned prop-sf-pf-coherence. No blueprint node states any of the new normalized work packages. The close existing lemmas are distinguished below. Their names and concepts were also searched in the live Lean library; none gives a finished proof of the new assertion.

For each new node I ran LeanFinder, Loogle, grep and LeanSearch with the prescribed msearch.py, and a second more general LeanFinder phrasing. I read all returned hits. The recorded results are copied from the actual search log, with the identical tool and query; all fifteen queries answered. I read the plausible ordinary-comparison sources: HomologicalComplexLimits.lean:195, Limits/Preserves/Limits.lean:58/63, Modules/Sheaf.lean:442/453, AdicCompletion/AsTensorProduct.lean:74/328/357 and Exactness.lean:184, and GrothendieckAxioms/Basic.lean:201 and Functor/Derived/Adjunction.lean's derived-unit construction. These are ordinary limits, module completion or derived-adjunction descent, and do not specialize in one line to any normalized pro-etale Roos/augmentation assertion here. Other hits about Kaehler differentials, affine transition limits, complex tensor unitors and small-object iterations have different objects/conclusions. No unavailable service was treated as a negative result.

## Work distribution and complete retained arguments

The three new nodes carry respectively 2316, 2200 and 2029 characters of the old argument (steps 1–2, 4–6, 7–8; exact text and sizes below). The two remaining arguments are old steps 3 and 9. The generic node statements do not impose separatedness, finite-Tor hypotheses or faithfulness of reduction. They state derived isomorphisms, not merely per-cohomology consequences.

### Original step 1 → lem-sf-open-roos-extension-comparison (1005 characters)

First check the geometric hypotheses needed for the product and completion results. The scheme $\operatorname{Spec}k$ is Noetherian: it has one point and its coordinate ring is a field. By [lem-weil-pbc-finite-type-over-noetherian], $U$ and $X$ are Noetherian, hence quasi-compact and locally Noetherian. By [lem-weil-pbc-locally-noetherian-quasi-separated] they are quasi-separated. Since $\operatorname{Spec}k$ is affine, $X\to\operatorname{Spec}k$ is then quasi-separated: the preimage of an affine open $V\times_kV'$ of $X\times_kX$ under the diagonal is $V\cap V'$, quasi-compact because $X$ is quasi-separated, and such products cover $X\times_kX$. Apply [lemma-nagata-open-immersion-qc-over-separated-target] to $U\to X\to\operatorname{Spec}k$: its composite is quasi-compact and its second arrow is quasi-separated. Thus $j$ is quasi-compact. Finally $\ell$ is invertible on both schemes because they are $k$-schemes and $\ell\ne\operatorname{char}k$. No separatedness of $X$ over $k$ is required.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lemma-nagata-open-immersion-qc-over-separated-target.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 2 → lem-sf-open-roos-extension-comparison (1311 characters)

Use the exact additive ringed-slice extension $F=j_!$ of [lem-pur-site-restriction-module-adjunction-exact]. Its canonical product comparison is invertible by [lem-cbc-ringed-open-extension-products], applied with $R=B_X$ and the quasi-compact open $j$. Countable products of modules over $B_U$ and $B_X$ are exact by [lem-weil-proetale-countable-products-exact]. Therefore [lem-cbc-exact-product-functor-strict-limit] applies and defines $\lambda_j$ at $S_\bullet$. Its target is $R\lim JS_\bullet$: termwise $j_!$ of the $B_U$-module complexes $S_n=\operatorname{Res}_n(\cdots)$ is $\operatorname{Res}_n$ of the finite extension $j_!^{A_n}$, compatibly with all quotient transitions, because scalar restriction commutes with these open extensions by [lem-sf-open-tensor-quotient-augmentation]. In its signed model $\mathsf H(S)^q=(\prod_n S_n)^q\oplus(\prod_n S_n)^{q-1}$, the comparison is the product comparison $\phi$ on both summands. The equations with the product projections characterize this $\phi$; it commutes with $1-s$ and the differentials by naturality. The cited lemma supplies descent, naturality, invertibility, independence of resolutions, and preservation of every strict augmentation. This gives the specified $\lambda_j$, rather than just an unspecified isomorphism between limit objects.

Cited nodes: lem-pur-site-restriction-module-adjunction-exact, lem-cbc-ringed-open-extension-products, lem-weil-proetale-countable-products-exact, lem-cbc-exact-product-functor-strict-limit, lem-sf-open-tensor-quotient-augmentation.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 3 → item assembly step 2 (682 characters)

The finite tensor comparison $\gamma_\bullet:T_\bullet\xrightarrow{\sim}JS_\bullet$ of [lem-sf-open-tensor-quotient-augmentation] is an isomorphism of the simultaneous strict systems, not just a family of derived evaluations. Apply the total derived-limit functor to this isomorphism and compose with $\lambda_j^{-1}$. By [def-pur-integral-derived-operations], $R\lim T_\bullet=j_!K\widehat\otimes^L_RP$ and $R\lim S_\bullet=K\widehat\otimes^L_Rj^*P$, with the defining representative comparisons understood. This is exactly the displayed $\Gamma_{K,P}$; it is an isomorphism. Naturality follows by composing the natural transformations $R\lim(\gamma_\bullet)$ and $\lambda_j^{-1}$.

Cited nodes: lem-sf-open-tensor-quotient-augmentation, def-pur-integral-derived-operations.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 4 → lem-sf-open-tensor-augmentation-limit-square (916 characters)

Write $a_T:H\to R\lim T_\bullet$ and $a_S:H_U\to R\lim S_\bullet$ for the maps induced by the strict augmentations $c_T,c_S$. The augmented equality in [lem-sf-open-tensor-quotient-augmentation] is $\gamma_\bullet c_T=J(c_S)\Delta(\gamma^B)$. Apply the normalized Roos functor of [lem-weil-strict-roos-comparison]. On complexes the augmentation is $z\mapsto((c_n(z))_n,0)$, so the equality gives the same first coordinates and zero shifted coordinates on both sides. Thus it is an equality of the actual induced derived maps, not an inference from equal projections out of a homotopy limit. The augmentation assertion of [lem-cbc-exact-product-functor-strict-limit] identifies the map induced by $J(c_S)$ with $\lambda_j j_!(a_S)$. Consequently
$$R\lim(\gamma_\bullet)\,a_T=\lambda_j\,j_!(a_S)\,\gamma^B.$$
All uses of $R\lim$ here are on strict complexes of towers and their strictly commuting augmentation squares.

Cited nodes: lem-sf-open-tensor-quotient-augmentation, lem-weil-strict-roos-comparison, lem-cbc-exact-product-functor-strict-limit.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 5 → lem-sf-open-tensor-augmentation-limit-square (689 characters)

By [lem-fix-constructible-tensor-completion], the quotient augmentations defining $a_T,a_S$ are precisely those defining $\chi_{j_!K,P}$ and $\chi_{K,j^*P}$, respectively. The actual-unit convention of [def-sf-tensor-completion-comparison] uses the same first Roos coordinate and zero shifted coordinate. Thus $a_T=\chi_{j_!K,P}$ and $a_S=\chi_{K,j^*P}$ under the recorded tensor presentations. Multiplying the equality in the preceding step by $\lambda_j^{-1}$ gives the required equality
$$\Gamma_{K,P}\,\chi_{j_!K,P}=j_!(\chi_{K,j^*P})\,\gamma^B.$$
In particular this identifies the specified limit construction with the conjugate of the ordinary open map by the actual completion maps.

Cited nodes: lem-fix-constructible-tensor-completion, def-sf-tensor-completion-comparison.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 6 → lem-sf-open-tensor-augmentation-limit-square (595 characters)

The statement of [lem-sf-open-tensor-quotient-augmentation] gives both $j_!K\in D^b_c(X,R)$ and $j^*P\in D^b_c(U,R)$. Together with the original assumptions on $K,P$, this allows [lem-fix-constructible-tensor-completion] to be applied to the pair $(j_!K,P)$ on $X$ and to $(K,j^*P)$ on $U$. The schemes are qcqs and $\ell$ is invertible by step 1. It follows that both displayed $\chi$ maps are isomorphisms. These applications require constructibility over the valuation ring $R$; they do not assume that the finite reductions have finite Tor dimension over the possibly nonregular rings $A_n$.

Cited nodes: lem-sf-open-tensor-quotient-augmentation, lem-fix-constructible-tensor-completion.
Source: {"document": "literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf", "place": "Lemma 6.5.5, pp.49-50; Lemma 6.5.8(2),(3), p.50; applied via the cited constructible tensor-completion and open-augmentation nodes."}

### Original step 7 → lem-sf-open-roos-restriction-unit (816 characters)

For restriction, use the localized site formula $j^*F(V/U)=F(V)$ of [def-pur-localized-ringed-site] and the sectionwise products of [lem-weil-pbc-module-sheaves-limits-sectionwise]. Evaluating on $V/U$ identifies $j^*\prod_nF_n$ with $\prod_nj^*F_n$, with their actual projections. The same sectionwise limit formula identifies $j^*B_X=B_U$ from the quotient coefficient systems. Restriction is exact and additive by [lem-pur-site-restriction-module-adjunction-exact]. Hence it too satisfies the hypotheses of the exact-product strict-limit comparison. Its comparison on a Roos complex is restriction of both signed coordinates. In particular it sends a quotient augmentation $z\mapsto((c_nz)_n,0)$ to its restricted quotient augmentation, so the tensor/restriction comparisons used here include the completion maps.

Cited nodes: def-pur-localized-ringed-site, lem-weil-pbc-module-sheaves-limits-sectionwise, lem-pur-site-restriction-module-adjunction-exact.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 8 → lem-sf-open-roos-restriction-unit (1213 characters)

Let $u:M\xrightarrow{\sim}j^*j_!M$ be the canonical open unit from [lem-sf-open-tensor-normalization], also for the strict system $S_\bullet$. That statement gives identity restriction for the simultaneous open tensor map; [lem-sf-open-tensor-quotient-augmentation] identifies $\gamma_\bullet$ with that finite tensor map with its quotient transitions. Apply [lem-cbc-exact-product-functor-strict-limit] to restriction as in step 7. The restricted product comparison defining $\lambda_j$ becomes the product of the units $u_{S_n}$: after each projection its equation is just naturality of $u$. This equality holds on both signed summands; therefore the restricted $\lambda_j$ identifies $j^*j_!R\lim S_\bullet$ with $R\lim j^*JS_\bullet$ through exactly the same $u$. Under $j^*T_\bullet\cong S_\bullet$ and $j^*JS_\bullet\cong S_\bullet$, the restricted $\gamma_\bullet$ is identity. Its Roos map is consequently identity on both products. Composing with the inverse restricted $\lambda_j$, and using $u_{R\lim S_\bullet}$, proves $j^*\Gamma_{K,P}=1$ under the stated completed tensor/restriction identifications. The augmentation calculation in step 7 shows that these are the comparisons with the actual units.

Cited nodes: lem-sf-open-tensor-normalization, lem-sf-open-tensor-quotient-augmentation, lem-cbc-exact-product-functor-strict-limit.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

### Original step 9 → item assembly step 5 (1098 characters)

Finally compare with the integral open datum requested in [def-exchange-projection]. It asks for the natural open isomorphism together with its finite-reduction identifications and units. The preceding equality, and invertibility of the two $\chi$ maps, give
$$\Gamma_{K,P}=j_!(\chi_{K,j^*P})\,\gamma^B\,\chi_{j_!K,P}^{-1}.$$
Use these actual $\chi$ isomorphisms to identify each completed tensor with its ordinary tensor presentation. Under the strict coefficient-change and open-reduction comparisons of [lem-sf-open-tensor-quotient-augmentation], reduction of the resulting map is precisely $\gamma_n$ and the transitions are precisely those of $\gamma_\bullet$. This supplies the finite-reduction normalization, simultaneously for all $n$, with no choice of morphism lifts from their evaluations. The restriction normalization is step 8. Thus $\Gamma$ is the integral open projection datum on the stated constructible domain. This supplies the open tensor component of that definition, without asserting any of its separate proper, rational or algebraically closed coefficient existence claims.

Cited nodes: def-exchange-projection, lem-sf-open-tensor-quotient-augmentation.
Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09BP, lemma-j-shriek-limits; augmentation-normalized refinement of the open-factor paragraph of prop-sf-pf-coherence, using the cited strict Roos comparison."}

## Review by Q158

I checked this repair against the sources and the statements of all original dependencies, rather than simply re-pushing the returned nine-step split. The live repository version is the available returned version; the sandbox initially contained only dispatcher marker files. I copied that version, attempted the required initial dry run, and its sole local diagnostic was the missing report. I also recovered and retained the full former Q140 report below. There was no earlier sandbox search log to overwrite. I did not modify Lean, shared repository files or launcher scripts.

Assembly step 1 uses A for its geometric conclusions and normalized lambda. The quotient-augmentation node explicitly says scalar restriction commutes with open extension and quotient transitions, so the target identification is justified by its statement. In A's retained argument the Noetherian, locally Noetherian/quasi-separated and triangle quasi-compactness lemmas apply to U→X→Spec k; the affine base argument proves the needed quasi-separatedness of the structure morphism. The ringed product theorem allows B_X and requires qc j, and exact countable products holds for both module categories. The normalized exact-product lemma states both signed coordinates and arbitrary strict augmentation preservation. This checks the hypotheses and preserves the substantial geometric/product workload of old steps 1–2.

Assembly step 2 uses the actual simultaneous isomorphism in the quotient-augmentation statement, and the displayed completed-tensor definition in integral-derived-operations. Functoriality, inversion and composition are the only elementary inferences. This retains old step 3.

Assembly step 3 uses B's explicit equality of actual maps and its invertible actual a_T,a_S=chi conclusion. B's retained arguments use the literal strict square in the quotient-augmentation statement, the strict-Roos theorem's explicit product/zero augmentation coordinates, and the exact-product theorem's augmentation equation; equality of evaluations alone is not used. The tensor-completion statement gives the same quotient augmentations, and the tensor-presentation definition specifies the zero shifted coordinate. Both input pairs are constructible by the quotient-augmentation statement; A's qcqs and invertibility of ell check the completion lemma's remaining hypotheses. Composition by inverse lambda has the correct orientation. This preserves old steps 4–6, and new B states the pre-composition square, not the item's complete Gamma theorem.

Assembly step 4 uses C's formula rho_JM j*lambda_M u_LM=L(u_M), together with rho's naturality and its augmentation preservation. The open normalization statement supplies the section-normalized invertible units and identity restriction, expressly also on strict diagram sites. The quotient-augmentation statement supplies the specific strict gamma and its transitions. Hence delta is the restricted finite tensor comparison, and the written formula follows by composing inverses and using naturality. C's retained argument checks the sectionwise formula F(V/U)=F(V), products and the coefficient limit, exact restriction, and equality of the two product-unit maps after each ordinary product projection. It is equality on both signed coordinates, not an appeal to faithfulness of homotopy-limit projections. This is the full old steps 7–8 workload, generalized to arbitrary towers.

Assembly step 5 retains old step 9: invert the actual chi maps, then use the quotient-augmentation statement's simultaneous reduction of gamma^B. The exchange-projection definition's higher coefficient paragraph asks for finite reductions carrying units and comparisons; it is used only to identify that requested open tensor component. No proper or rational existence result is inferred from this definition. All 10 step/citation pairs (with repetition by step) have verbatim substantial statement excerpts in citations.json.

For B–E specifically, I introduced every object in each new statement, supplied its definition references, and delivered empty proofs/proof_deps for the new nodes. Searches are logged actual queries. None of the three states the entire item or replaces the argument by a source citation. The original argument is explicitly partitioned above and retained, with its citations, rather than discarded. The assembly is under 3000 characters and has no step over 2000 characters. Source-sharing and the closest conceptual candidates are distinguished in the following section. The new nodes depend only on definitions and earlier generic nodes (B and C also use A), with no edge back to this item. Generic off-unit tools retained in the assembly remain declared in split_report.tool_uses; the maintainer-owned tool_uses field is preserved.

Small cases: empty U gives zero towers, augmentations and tensors. The identity open gives identity lambda, rho, unit and gamma. Zero K or P gives zero augmentation squares. An arbitrary zero tower satisfies A and C; arbitrary shifted or unbounded complexes remain allowed because both signed summands are specified and countable products are exact. The chain-map check d(c(z),0)=(c(dz),0) is exactly (1-s)c=0, so it checks the sign convention. Nonseparated finite-type X is still Noetherian and qcqs; no separatedness was added. A_1 and nonregular higher A_n are allowed without finite Tor dimension over A_n. The unit equation in C is typed from L_U M to L_U(GJM) on both sides. The original item statement is byte-for-byte unchanged.

## Not duplicates

- lem-sf-open-roos-extension-comparison vs lem-sf-open-projection-roos-completion: the existing item constructs Gamma and proves its tensor/reduction conclusions; this package only supplies one prerequisite argument, for arbitrary towers in A and C, or the pre-Gamma augmentation square in B.

- lem-sf-open-roos-extension-comparison vs lem-sfb-integral-open-extension-reduction: the existing assertion is derived scalar reduction for condensed coefficients, with separatedness; it does not specify the signed Roos/augmentation or open-unit comparison over B_W.

- lem-sf-open-roos-extension-comparison vs det-sfb-dc-restricted-functors-closed-image: the existing assertion preserves constructible complexes and gives stratum devissage; it has no normalized strict-limit comparison or two-functor unit equation.

- lem-sf-open-roos-extension-comparison vs sk-lem-proper-heart-bound: the existing assertion is a rational proper-pushforward cohomological bound and direct-sum theorem, not a ringed open strict-limit calculation.

- lem-sf-open-roos-extension-comparison vs sk-lem-uniform-constructible-ext: the existing assertion bounds rational constructible Ext, not normalized open derived limits.

- lem-sf-open-roos-extension-comparison vs sk-lem-int-tensor: the existing assertion is integral constructible stability for inverse image/tensor/extension, not a signed Roos comparison with actual augmentations or the open unit.

- lem-sf-open-roos-extension-comparison vs det-uniform-constructible-ext-integral: the existing assertion is an integral Ext vanishing bound for strata, not an open strict-limit comparison.

- lem-sf-open-roos-extension-comparison vs lem-sfb-condensed-open-extension-products: the existing assertion preserves products in pulled-back condensed coefficient derived categories; this package uses ordinary B_W-module strict towers and records normalized derived-limit augmentation or unit data.

- lem-sf-open-roos-extension-comparison vs det-cor-int-compactness-ii-extension-zero: the existing assertion is limit/reduction and constructible/localizing stability; it does not pin the derived strict-limit Roos map or its unit equation.

- lem-sf-open-roos-extension-comparison vs det-proper-heart-bound-lattice: the existing assertion is the 2d+1 cohomology bound for a proper fiberwise lattice, not open strict-limit normalization.

- lem-sf-open-roos-extension-comparison vs det-lem-int-tensor-shriek: the existing assertion is constructible stability and stratum generation; it does not specify normalized strict derived limits and actual augmentation/unit equations.

- lem-sf-open-roos-extension-comparison vs lem-cbc-ringed-open-extension-products: the existing assertion is the module-sheaf product isomorphism; it does not establish the finite-type geometric hypotheses or its derived strict-limit normalization and open-unit compatibility.

- lem-sf-open-roos-extension-comparison vs lem-cbc-ringed-open-scalar-limit-coherence: the existing assertion compares extension with scalar restriction along a ring map; this package has no such ring-change square and C instead compares geometric restriction, extension and their actual adjunction unit.

- lem-sf-open-roos-extension-comparison vs det-sp-integral-direct-image-tower: the existing assertion is smooth compact-support direct-image realization and Tor bounds, with separatedness; it has no arbitrary-tower open-unit equation.

- lem-sf-open-roos-restriction-unit vs lem-sf-open-projection-roos-completion: the existing item constructs Gamma and proves its tensor/reduction conclusions; this package only supplies one prerequisite argument, for arbitrary towers in A and C, or the pre-Gamma augmentation square in B.

- lem-sf-open-roos-restriction-unit vs lem-sfb-integral-open-extension-reduction: the existing assertion is derived scalar reduction for condensed coefficients, with separatedness; it does not specify the signed Roos/augmentation or open-unit comparison over B_W.

- lem-sf-open-roos-restriction-unit vs det-sfb-dc-restricted-functors-closed-image: the existing assertion preserves constructible complexes and gives stratum devissage; it has no normalized strict-limit comparison or two-functor unit equation.

- lem-sf-open-roos-restriction-unit vs sk-lem-proper-heart-bound: the existing assertion is a rational proper-pushforward cohomological bound and direct-sum theorem, not a ringed open strict-limit calculation.

- lem-sf-open-roos-restriction-unit vs sk-lem-uniform-constructible-ext: the existing assertion bounds rational constructible Ext, not normalized open derived limits.

- lem-sf-open-roos-restriction-unit vs sk-lem-int-tensor: the existing assertion is integral constructible stability for inverse image/tensor/extension, not a signed Roos comparison with actual augmentations or the open unit.

- lem-sf-open-roos-restriction-unit vs det-uniform-constructible-ext-integral: the existing assertion is an integral Ext vanishing bound for strata, not an open strict-limit comparison.

- lem-sf-open-roos-restriction-unit vs lem-sfb-condensed-open-extension-products: the existing assertion preserves products in pulled-back condensed coefficient derived categories; this package uses ordinary B_W-module strict towers and records normalized derived-limit augmentation or unit data.

- lem-sf-open-roos-restriction-unit vs det-cor-int-compactness-ii-extension-zero: the existing assertion is limit/reduction and constructible/localizing stability; it does not pin the derived strict-limit Roos map or its unit equation.

- lem-sf-open-roos-restriction-unit vs det-proper-heart-bound-lattice: the existing assertion is the 2d+1 cohomology bound for a proper fiberwise lattice, not open strict-limit normalization.

- lem-sf-open-roos-restriction-unit vs det-lem-int-tensor-shriek: the existing assertion is constructible stability and stratum generation; it does not specify normalized strict derived limits and actual augmentation/unit equations.

- lem-sf-open-roos-restriction-unit vs lem-cbc-ringed-open-extension-products: the existing assertion is the module-sheaf product isomorphism; it does not establish the finite-type geometric hypotheses or its derived strict-limit normalization and open-unit compatibility.

- lem-sf-open-roos-restriction-unit vs lem-cbc-ringed-open-scalar-limit-coherence: the existing assertion compares extension with scalar restriction along a ring map; this package has no such ring-change square and C instead compares geometric restriction, extension and their actual adjunction unit.

- lem-sf-open-roos-restriction-unit vs det-sp-integral-direct-image-tower: the existing assertion is smooth compact-support direct-image realization and Tor bounds, with separatedness; it has no arbitrary-tower open-unit equation.

- lem-sf-open-roos-extension-comparison vs lem-sf-ringed-open-roos-preservation: that node preserves distinguished Roos triangles but does not specify a natural comparison of total derived strict limits preserving every augmentation. A additionally carries the finite-type geometric hypothesis check.
- lem-sf-open-roos-extension-comparison vs lem-cbc-exact-product-functor-strict-limit: the generic theorem assumes exactness, exact products and canonical product preservation; A establishes those and geometric qc hypotheses for the actual ringed open operation.
- lem-sf-open-tensor-augmentation-limit-square vs lem-sf-open-tensor-quotient-augmentation: the existing statement is before total derived limit and does not identify or prove invertible the actual tensor completion maps.
- lem-sf-open-tensor-augmentation-limit-square vs lem-fix-constructible-tensor-completion: the existing theorem gives chi for a pair on one qcqs scheme; B assembles the augmented open square with the specified extension/limit comparison and checks both different schemes/input pairs.
- lem-sf-open-tensor-augmentation-limit-square vs lem-pur-completed-open-tensor-system-realization: that theorem realizes a completed tensor map through semilinear reduction/limit unit/counit substitutions; B instead pins the scalar-restricted signed Roos lambda and the actual pre-Gamma quotient augmentations. Identifying these normalizations is not a one-line specialization.
- lem-sf-open-roos-restriction-unit vs lem-sf-open-exchange-roos-restriction: that theorem concerns a completed base-change square and its pullback compositors; C concerns arbitrary strict module towers and the general extension/restriction unit equation, without a base-change square or tensor factors.
- lem-sf-open-roos-restriction-unit vs lem-sf-open-roos-unit-adjunction: that node constructs the completion reflector and restricted complete adjunction; it does not state the two normalized strict-limit functor comparisons' compatibility with the actual open unit for arbitrary towers.
- lem-sf-open-roos-restriction-unit vs lem-sf-canonical-open-restriction-model: that node produces a strict representative for a scalar reduction mate from supplied tensor/extension models; C is a product/total-limit open-unit comparison for arbitrary strict towers.
- lem-sf-open-roos-restriction-unit vs lem-sp-slice-restriction-strict-derived-limit: that node gives the derived restriction/limit comparison and its projections, but not its signed strict-augmentation normalization or the equation comparing extension, restriction and the actual open unit.
- lem-sf-open-roos-restriction-unit vs lem-pur-roos-comparison-horizontal-coherence: that node is a general cochain-map horizontal-composition identity in different signed cone coordinates; C establishes the particular geometric coefficient restrictions and the derived, augmentation-normalized open-adjunction identity. This requires geometric specialization and normalization/descent, not a one-line instantiation.
- lem-sf-open-tensor-augmentation-limit-square vs lem-sf-open-projection-roos-completion: B states the augmented pre-Gamma square and checks invertibility of the two actual quotient units; it neither constructs the requested Gamma nor supplies its restriction identity and finite-reduction datum. These require the independent A and C work packages and the remaining assembly.

## Preserved previous report (Q140, verbatim)

# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-sf-open-projection-roos-completion.json`, split into nine proof steps. No new nodes and no Mathlib leaves. `citations.json` records 24 step/dependency pairs with verbatim statement excerpts. The original statement, source, creation record and blueprint ancestry are preserved; the original Mathlib searches are retained and the searches actually run by Q140 are appended.
2. Attachments: none. Searches of `lean/WeilConjectures/` by the blueprint tag, Roos, open projection, augmentation and completion unit found no declaration stating all clauses. `SixFunctors/Etale/Derived/OpenImmersionLowerShriekProjection.lean` concerns the ordinary etale projection map, without the completed pro-etale quotient tower or its actual completion unit. `SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean` concerns condensed coefficient module objects and its open projection input is explicitly `sorry`. Neither is an attachment.
3. WANTED: none. The item source and the supporting literature are available locally.
4. The original item had a statement but no proof. In particular its advertised normalized limit comparison needed its exactness, product-preservation and geometric hypotheses checked. The proof now does this, and proves equality using simultaneous augmented strict complexes rather than equality after finite evaluations or projections from a homotopy limit. There is no statement dispute and no change of coefficient category or proof route.
5. Unfinished: no required part of this one-level split. Existing dependencies remain separate items. This report does not claim their Lean proofs are complete.

## Sources and searches

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-pf-coherence.json`, and the current item. I read the main-20261015 `prop-sf-pf-coherence.proof.md`, particularly its open-factor paragraph, and the `lem-cbc-completed-extension-zero-comparison.proof.md` supporting the limit-comparison source. The latter's loose claim that extension by zero is sectionwise and therefore preserves products is not used: the proof uses the ringed product theorem instead.

For the item I read `literature/stacks-project/proetale.tex`, Tag 09BP, `lemma-j-shriek-limits`, including its proof by the open/closed exact sequence; `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`; and `sites-modules.tex`, Tag 0E8I, `lemma-j-shriek-and-tensor`. I read Bhatt–Scholze, physical PDF pp.49–51, particularly Lemmas 6.5.5 and 6.5.8. The precise normalized Roos augmentation assertions come from the statements of the existing generic nodes; they are agent refinements, not claimed as verbatim Stacks or Bhatt–Scholze assertions. `proof_origin.by` is consequently `agent`. No SGA source is used.

Mathlib searches were run through the prescribed `msearch.py`, with results in `searches.jsonl`: LeanFinder both for exact product functors/augmented derived limits and for completed open tensor/actual units; Loogle for `CategoryTheory.Limits.PreservesLimits, HomologicalComplex`; LeanSearch for the completed open formula with actual units; and grep for Roos/derived-limit/completed-tensor names and for the returned ordinary comparison declarations. I inspected `AdicCompletion.ofTensorProduct_naturality` at `AsTensorProduct.lean:74`, `CategoryTheory.preservesLimitIso_hom_π` at `Limits/Preserves/Limits.lean:58`, `HomologicalComplex.preservesLimitsOfShape_of_eval` at `HomologicalComplexLimits.lean:195`, and the scheme-module restriction declarations at `Modules/Sheaf.lean:442–453`. These are ordinary module completion, ordinary categorical limit comparison, termwise complex limits, and Zariski structure-module restriction, respectively. None states this completed pro-etale assertion. Both natural-language phrasings were read before recording no match. All services answered; no unavailable result is presented as a negative search.

DAG searches by 09BP, augmentation/completion, completed tensor/restriction, and the existing node names found the reusable ringed product, strict Roos, completion, and open normalization results. Whole-blueprint searches using `tools/blueprint_refs.py search` for `open projection`, `Roos`, `09BP`, and `tensor completion` found no alternative blueprint node stating the item. The nearest ancestor is `prop-sf-pf-coherence`, via `lem-sf-pf-open-factor-coherence`; its precise open-factor place is already recorded. No chapter or unit record is changed.

## Not duplicates

No new nodes are created. The entire argument reuses existing statements. In particular the general exact-product strict-limit theorem is used as a tool, and the item's actual augmentation and restriction equations are proved by applying it to the supplied finite tensor square.

## Review by Q140

I checked the item against the Stacks and Bhatt–Scholze sources named above and read the statement of every dependency used below. There are no new node sources to review. The argument stays on the unit's open-factor route, making its integral completion normalization explicit. Generic tools from other units are explained in `split_report.tool_uses`; I did not set the maintainer-owned top-level field.

Step 1 uses `lem-weil-pbc-finite-type-over-noetherian` for the Noetherian conclusion, `lem-weil-pbc-locally-noetherian-quasi-separated` for quasi-separatedness, and `lemma-nagata-open-immersion-qc-over-separated-target` for quasi-compactness of j. I checked the actual triangle U → X → Spec k: its composite is finite type and hence quasi-compact, its second morphism is quasi-separated, and the base is Noetherian since k is a field. This verifies the qcqs and quasi-compact-open hypotheses without adding separatedness to X.

Step 2 uses `lem-pur-site-restriction-module-adjunction-exact` for exactness and the adjunction, `lem-cbc-ringed-open-extension-products` for the canonical module product comparison, `lem-weil-proetale-countable-products-exact` for exact countable products, and `lem-cbc-exact-product-functor-strict-limit` for the specified signed comparison and its augmentation clause. I checked that the product theorem applies to a ring sheaf B_X, not just constant or abelian coefficients, and that the limit theorem supplies the normalization rather than only existence of an isomorphism. The coefficients on U are the ringed-slice restrictions, as required.

Step 3 uses `lem-sf-open-tensor-quotient-augmentation`, which explicitly provides an isomorphism of simultaneous strict systems, and `def-pur-integral-derived-operations`, whose displayed definition identifies their derived limits with the two completed tensors. Applying a functor to an isomorphism and composing natural isomorphisms is the elementary argument here; no derived-limit existence theorem is inferred from a definition.

Step 4 uses the exact augmented equation in `lem-sf-open-tensor-quotient-augmentation`, the signed augmentation formula and functorial descent in `lem-weil-strict-roos-comparison`, and the augmentation-preservation clause of `lem-cbc-exact-product-functor-strict-limit`. I explicitly evaluated both signed coordinates. This is what proves equality of actual morphisms. An argument using only finite derived evaluations or the limit projections would not prove that equality, and is not used.

Step 5 uses the explicit quotient map description of `lem-fix-constructible-tensor-completion` and the actual-unit coordinate convention of `def-sf-tensor-completion-comparison`. These identify a_T and a_S with the actual chi maps. The remaining argument is composition with the inverse lambda in the equality already proved. I checked the direction: lambda goes from j_! of the limit to the limit of J, so its inverse belongs on the left in Gamma.

Step 6 uses the actual constructibility clauses of `lem-sf-open-tensor-quotient-augmentation` and the isomorphism assertion of `lem-fix-constructible-tensor-completion`. I checked both pairs and both schemes separately. R is the valuation ring of the finite coefficient field, and ell is invertible on the qcqs schemes. I did not assume finite Tor dimension over A_n, which would be an unjustified extra hypothesis.

Step 7 uses the section formula of `def-pur-localized-ringed-site`, the evaluation/limit formula of `lem-weil-pbc-module-sheaves-limits-sectionwise`, and exact restriction from `lem-pur-site-restriction-module-adjunction-exact`. Evaluating a product on V/U gives the same product with its projections, and this supplies the product hypothesis for restriction. The same formula restricts the coefficient limit. This is a direct verification of those formulas, not a new comparison theorem hidden in an elementary step.

Step 8 uses `lem-sf-open-tensor-normalization` for its invertible, section-normalized units and its explicit strict-system extension; `lem-sf-open-tensor-quotient-augmentation` to identify the particular gamma system; and `lem-cbc-exact-product-functor-strict-limit` for restriction and extension comparisons on both signed summands. The projection identities in the argument are used only for maps to an ordinary product, where they determine the maps; equality on the resulting Roos complexes then proves the derived equality. Thus j^*Gamma is identity under exactly the prescribed units and completed tensor/restriction identifications, and the augmentation convention is retained.

Step 9 uses `def-exchange-projection` only for the data it requests and `lem-sf-open-tensor-quotient-augmentation` for reduction of the ordinary gamma and all strict transitions. The displayed conjugation formula comes from steps 5 and 6. Transporting the actual completed tensors through these chi isomorphisms gives their ordinary tensor presentations, in which the supplied quotient comparisons compute each reduction as gamma_n. This verifies the integral open tensor component; it does not assert the other existence and coherence inputs of the exchange definition.

I checked B–E of `coord/delivery-errors.md` point by point: self-contained original statement and definition references retained; no unsplit node carrying a hidden proof; no invented search; no off-unit proof substitution; no citation of a dependency's proof for a claim absent from its statement; no restatement of the item as a new node; no missing argument replaced by a source citation. The citations file contains a literal statement excerpt for each of the 24 cited pairs and was checked against the statements when written. The proof steps are all shorter than 2000 characters, and each has one identified task.

Small cases checked: for U empty all tensors, towers and maps involving j_! are zero; for j identity the canonical product comparisons, units and finite gamma maps are identities, giving Gamma identity; if K or P is zero the augmented coordinate equations are zero equations. The first quotient A_1 is allowed, and higher nonregular A_n require no extra Tor assumption. Nonseparated finite-type X still satisfies the quasi-separatedness argument used in step 1. The signed fiber differential d(x,y)=(dx,(1-s)x-dy) makes (c(z),0) a chain map because strict augmentation says (1-s)c=0; this checks the sign and shifted-coordinate convention directly.
