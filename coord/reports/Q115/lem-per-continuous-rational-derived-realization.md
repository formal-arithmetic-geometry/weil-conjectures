# Q115 stage-1 repair: lem-per-continuous-rational-derived-realization

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-continuous-rational-derived-realization.json: original statement unchanged; seven assembly steps, 2070 proof characters.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-module-realization-functor.json: statement; unsplit; Mathlib no match. Task from old steps 1, 2, 3.
- dag/nodes/sec-deligne-laumon-a1/lem-per-constructible-rational-hom-comparison.json: statement; unsplit; Mathlib no match. Task from old steps 4.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-stratum-integral-models.json: statement; unsplit; Mathlib no match. Task from old steps 6, 7.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-realization-finite-cone-models.json: statement; unsplit; Mathlib no match. Task from old steps 5, 8, 9.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-realization-degree-reflection.json: statement; unsplit; Mathlib no match. Task from old steps 10, 11.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-realization-pullback-comparison.json: statement; unsplit; Mathlib no match. Task from old steps 12, 13.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-pullback-composition-coherence.json: statement; unsplit; Mathlib no match. Task from old steps 14.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-realization-scalar-coherence.json: statement; unsplit; Mathlib no match. Task from old steps 15, 16.
- dag/nodes/sec-deligne-laumon-a1/lem-per-continuous-coefficient-slice-normalization.json: statement; unsplit; Mathlib no match. Task from old steps 17.
- report.md and citations.json; searches.jsonl and the saved actual search answers are retained in the sandbox.

## Attachments

None. The project-root search in lean/WeilConjectures for the item tag and continuous/rational realization found no theorem stating this item. The existing Sheaf.Paper.ContinuousRationalDerivedRealization declaration at line 948 ends with sorry, so it is reference material, not an attachment. No Lean file was written or compiler invoked.

## WANTED

None: the Bhatt–Scholze PDF and all referenced blueprint/DAG material are present.

## What was wrong and what changed

The human returned the already reviewed item because its proof carried 17,062 characters of implementation work in one node. This is a deliberate re-split, not an obsolete claim on a finished node. The initial sandbox had only dispatcher markers; I copied the current live item, whose 17 proof texts have exactly this total length. The item statement, source and maintainer metadata have been retained. Nine new self-contained statements distribute its arguments; all nine have status unsplit, empty proof and proof_deps, null proof_origin, source, complete blueprint provenance and actual recorded Mathlib searches. The parent now assembles their statements in 2,070 characters. No parent-sized replacement node was introduced.

The task map below is exhaustive and disjoint on the old proof steps. The full text of every old step, its cited nodes and source are preserved verbatim in the final section of this report, grouped by the new task. This is the development brief for the separate workers, not a claimed proof in the new nodes. The new statements explicitly retain each non-elementary obligation: actual completed rings; quotient normalization; Hom/coproduct continuity; sheaf-stratum and bounded-cone induction; converse degree bounds; the specified completion unit; coherent scheme, field and mixed tensor comparisons; and the normalized slice indexing argument.

| New task | Old steps | Original argument characters |
| --- | --- | ---: |
| lem-per-rational-module-realization-functor | 1, 2, 3 | 2646 |
| lem-per-constructible-rational-hom-comparison | 4 | 1151 |
| lem-per-rational-stratum-integral-models | 6, 7 | 2325 |
| lem-per-rational-realization-finite-cone-models | 5, 8, 9 | 2045 |
| lem-per-rational-realization-degree-reflection | 10, 11 | 1380 |
| lem-per-rational-realization-pullback-comparison | 12, 13 | 2255 |
| lem-per-rational-pullback-composition-coherence | 14 | 1261 |
| lem-per-rational-realization-scalar-coherence | 15, 16 | 2332 |
| lem-per-continuous-coefficient-slice-normalization | 17 | 1667 |

## Not duplicates

lem-per-rational-module-realization-functor vs lem-weil-pbc-localization-inverse-image-coherence: the existing theorem is exact localization and its inverse-image coherence on arbitrary ringed topoi; the new task constructs the triangulated raw-category functor and verifies its completed integral constructibility, rational local models, and cohomology.
lem-per-constructible-rational-hom-comparison vs lem-weil-pbc-scalar-localization-derived-hom: the old abstract theorem assumes Hom/coproduct continuity; the new statement proves that hypothesis for every integral constructible source from global derived-Hom compactness, then identifies the normalized actual rational Hom map.
lem-per-constructible-rational-hom-comparison vs lem-weil-pbc-integral-constructible-bounded-below-compactness: the old statement gives global derived-Hom continuity, not the morphism-group comparison into D(E_X), nor its normalized fraction rule.
lem-per-rational-stratum-integral-models vs lem-sfb-finite-model-stratum-filtration: the old theorem gives only a sheaf filtration for pulled condensed coefficients. The new task supplies genuine completed integral models with compatible etale-origin witnesses for its quotients and proves the open/closed-localization comparison.
lem-per-rational-stratum-integral-models vs lem-weil-pbc-continuous-constructible-integral-stratum: the latter concerns ordinary internal-module integral models on an immersed stratum. It does not place the extensions by zero in the completed integral category with compatible reduction witnesses.
lem-per-rational-stratum-integral-models vs lem-weil-pbc-continuous-constructible-integral-gluing: the latter glues ordinary internal integral sheaves from supplied models, not completed derived objects or the canonical localization/open-closed comparison asserted here.
lem-per-rational-realization-finite-cone-models vs lem-sfb-bounded-finite-model-generation: the existing result is membership in an abstract extension-closed class; the new conditional result constructs the integral raw-category cone representatives of specified connecting arrows f/varpi^n and their rescaling comparison, followed by the two finite inductions. It does not assert an equivalence, full faithfulness, or any coherence.
lem-per-rational-realization-finite-cone-models vs lem-weil-pbc-continuous-constructible-integral-model: the latter uses the ordinary integral internal-module category of def-weil-pbc-continuous-integral-coefficients. Here models belong to the actual raw completed category with etale witnesses, and the conditional construction specifies the integral cones of lifted connecting fractions.
lem-per-rational-realization-finite-cone-models vs lem-weil-pbc-directed-triangulated-image: the existing theorem proves abstract essential-image closure. The new task includes the denominator/cone representatives and the finite sheaf-filtration and cohomology-truncation inductions. The closure theorem is an available ingredient, not copied as a new standalone lemma.
lem-per-rational-realization-degree-reflection vs prop-weil-localized-tstructure: that proposition constructs source truncations; it does not identify them with rational continuous-module cohomology or reflect both ambient degree bounds under J_X.
lem-per-rational-realization-pullback-comparison vs lem-tw-ordinary-completed-integral-pullback: I reuse that theorem explicitly for ordinary pullback membership and the specified unit. The new task adds the rational comparison through its inverse, localization of the coefficient map, balanced derived tensors, and descent to raw fractions.
lem-per-rational-pullback-composition-coherence vs lem-weil-pbc-continuous-coefficient-pullback-composition: the latter compares the ring maps, not the rational realization transformations conjugated by the specified quotient-tower completion units.
lem-per-rational-pullback-composition-coherence vs lem-sf-scalar-pullback-composition: the latter is the constant-ring scalar-pullback comparison. The new task compares completed integral to rational continuous ring sheaves for general scheme morphisms and must preserve their specified completion units.
lem-per-rational-realization-scalar-coherence vs prop-weil-pbc-scalar-extension: the existing theorem supplies raw coefficient extension and its associators. The new task identifies it under J with ambient continuous-rational extension and checks the specified realization comparisons in the mixed square.
lem-per-continuous-coefficient-slice-normalization vs lem-weil-proetale-weakly-etale-localization: the old theorem gives the slice site and constant coefficients, not the equality between the specified inverse-image construction and slice evaluation nor its continuous integral/rational coefficient normalization.
lem-per-continuous-coefficient-slice-normalization vs lem-weil-pbc-continuous-coefficients-immersion-restriction: the old theorem treats locally closed immersions. The new statement also covers etale morphisms and every pro-etale site object, including non-noetherian ones, and pins the initial-object and finite-quotient maps.

The nine node ids were searched literally across the entire DAG and both Lean roots before creating files; none existed. I ran blueprint_refs.py ancestor for the item and search for each task phrase across the whole blueprint (all nine returned zero), and searched the whole DAG for continuous coefficients, scalar localization, integral models, stratum filtration and pullback comparisons. I read the candidates listed above and the original dependencies. No existing blueprint statement duplicates a new task. The narrower condensed realization requires a separated finite-type scheme over a positive-characteristic field; it cannot supply the general noetherian-scheme statement or silently identify the coefficient categories. No new node cites the parent, so the factorization does not introduce a parent dependency cycle.

## Review by Q115

I read the item, the chapter sec-deligne-laumon-a1, its unit sk-p-dl-a1-perverse, the ancestor lem-per-smooth-pullback-t-exact and its first-paragraph realization input. I read Bhatt–Scholze §6.8, pp. 58–62, including Lemma 6.8.2, Definitions 6.8.3/6.8.6/6.8.8/6.8.10, Proposition 6.8.11(3), Lemmas 6.8.12–13, Proposition 6.8.14(2) and Remark 6.8.15. The source explicitly reduces full faithfulness to bounded-below compactness and essential surjectivity to local systems. The extra normalized unit and coherence statements are the expanded comparison obligations of the retained proof, not claimed to be verbatim quotations from the paper. The parent proof_origin is agent for this assembly. No SGA source or alternative purity route is used.

For the functor task I checked the coefficient identification and the stratified-perfect characterization statements: the first preserves the quotient and immersion maps, while the second really includes the etale witnesses. Exact localization gives the cohomology formula without assuming that the finitely presented integral module is torsion free. For the Hom task I read the exact hypothesis of the scalar-localization Hom lemma: it is a coproduct comparison of morphism groups, not merely an assertion about internal Hom. Global derived-Hom compactness, the global-sections/internal-Hom comparison and exact countable sums are precisely the old Step 4 argument; it is retained in that task brief. The target Hom group is D(E_X).

For stratum models I checked the statement of the finite-model stratum-filtration tool and its coefficient encoding, the continuous-coefficient realization and internal/sectionwise equivalence, the lisse-lattice theorem, the integral characterization, and the exact open/closed lemma. The last really states filtered-colimit preservation of closed pushforward under qcqs hypotheses; it is used only on the qcqs open V_k. The stratum is reduced closed in a noetherian open, so it has the finite dimension and invertibility assumptions required for the lattice theorem. Extension by zero and closed pushforward give supporting-piece and zero-piece local integral models. For the finite-cone task I checked that full faithfulness is an explicit hypothesis, not smuggled in as a conclusion. A connecting arrow is in raw localized Hom and can be cleared to f/varpi^n; its rescaled cone is an actual integral cone. Filtration induction begins with zero, then standard truncation induction begins with the zero-cohomology case and decreases the finite amplitude. These are separate from full faithfulness, t-structure reflection and coherence.

For the degree-reflection task I read both integral and localized t-structure propositions. They assert integral truncations and Q tau comparisons without the additional Tor hypothesis needed only for levelwise reduction formulas. The new statement therefore uses canonical ambient truncations, not an unjustified levelwise formula. Both converse degree bounds are retained: acyclicity of the opposite truncated image and full faithfulness force the truncated identity to vanish. The heart identification uses the parent essential-surjectivity step only after this reflection.

For the pullback task I read the completed-pullback definition, the ordinary/completed integral pullback theorem, the constant/completed equivalence and its unit-and-transition clauses, and the generic ringed-derived tensor/monoidal comparisons. I verified that c_g is only a structural map for an arbitrary scheme morphism. Pulled perfect models retain the compatible witnesses via the characterization; completeness identifies the specified gamma with an invertible unit. The rational comparison is normalized by its inverse and the balanced tensor map, not an arbitrarily chosen isomorphism. For the scheme-composition task the two coefficient composites agree after each quotient projection, and both tensor composites flatten the same balanced sections; conjugation uses those very same completion units. This additional normalization is why the generic ring-map or ordinary sheaf pullback associativity results do not close the task by themselves.

For the field task I checked the full scalar-extension proposition, including its definition by actual completed integral change of rings, raw rationalization, its associators and its pullback comparison. The task statement keeps these maps and the continuous coefficient naturality; it does not assume varpi_E equals varpi_L or that the extension is unramified. The successive-field and mixed squares have the explicit balanced formulas from retained Steps 15–16. For slice restriction I read the weakly-etale localization statement and the actual inverse-image definition. The new task retains the initial-object calculation repaired by the prior reviewer: the site equivalence alone does not prove that the specified g inverse is the slice functor. Evaluation on the same underlying V gives the quotient-normalized continuous ring map even when U is not noetherian. The locally closed case cites its existing immersion theorem rather than treating all structural ring maps as isomorphisms.

For parent Step 1 I opened the new functor statement: it gives the ring identifications, actual formulas, constructibility and triangulation used there. Step 2 uses precisely the Hom isomorphism and full-faithfulness conclusion in the new Hom statement. Step 3 cites the filtration/integral-piece statement and the conditional finite-cone construction, with full faithfulness supplied by Step 2; it does not claim a new proof from a definition. Step 4 uses the explicit two iff degree bounds, canonical truncations and cohomology in the new reflection statement and essential surjectivity already proved. Step 5 uses the specified pullback comparison followed by the exact identity/composition equations in the scheme-coherence statement. Step 6 uses the field and mixed coherence statement with the same alpha, not some other tensor comparison. Step 7 uses the slice-normalization theorem and its immersion clause. I copied the substantive statement suffixes verbatim into citations.json; no parent step takes an extra assertion from a cited node proof. All parent steps are non-elementary and each is below 2,000 characters.

Edge cases: empty X and zero-rank sheaves give zero objects/empty filtrations in all model tasks; torsion integral cohomology is killed by rationalization and is not excluded. Hom continuity is only required for families with a common lower bound, including all their shifts. A complex of amplitude zero uses the sheaf case, and an acyclic complex uses zero, so truncation induction has a base. Identity g and E=L reduce to insertion/removal of 1. A ramified finite L/E still maps every nonzero E scalar to a unit. For arbitrary g no coefficient-ring isomorphism is assumed, whereas etale maps and locally closed immersions have the stated restriction isomorphisms. Arbitrary site U is exempt from the noetherian and finite-dimensional hypotheses only in the restriction task, which claims no completed constructible category on U.

B–E repair checklist: nine substantive, individually scoped statement-only tasks replace the long proof (B/D1/D2); none bundles an equivalence with all its coherences. Literal id, concept and blueprint searches preceded creation, and nearest candidates were opened (B/C5). All four Mathlib search kinds were actually executed for every new node, with two distinct semantic phrasings; invalid Loogle name queries are retained as invalid and supplemented with valid queries. No generic derived-functor, tensor-associator or sheaf-slice hit states these coefficient-specific assertions as a one-line specialization (B7/B8). Source premises, witness categories, qcqs hypotheses and actual normalized maps were checked as above (C1/C4/E). The same parent statement is retained exactly. During self-review I corrected the new functor statement to introduce F_X and both raw formulas explicitly rather than referring to an absent display. Every new proof remains empty as requested; the full argument is handed off below rather than hidden inside an allegedly finished proof.

## What remains unfinished

The nine new nodes are intentionally unsplit proof tasks for parallel stage-1 workers; this delivery does not claim their Lean proofs. No part of the requested factorization remains unassigned. Verification and delivery results are appended after the dry run.

## Retained argument, verbatim, by new task

### lem-per-rational-module-realization-functor

Old step 1 (608 characters):

Write $\mathcal C_X=D^b_c(X,A)$ for the completed-coefficient category, including its compatible etale-origin witnesses. The coefficient datum defines $B_X=\varprojlim_n(A/\varpi^n)_X$ as a ring sheaf with its specified projections. The continuous-coefficient restriction lemma identifies this ring with $V\mapsto C(|V|,A)$, and identifies its sheafified localization at $\varpi$ with $V\mapsto C(|V|,E)$. The identifications preserve constant sections and quotient projections and commute with locally closed restriction. All categories below are categories of module sheaves over these actual ring sheaves.

Uses: def-weil-pbc-bounded-constructible-complete, def-weil-pbc-adic-coefficient-datum, lem-weil-pbc-continuous-coefficients-immersion-restriction.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 6.8.2; Definitions 6.8.1, 6.8.6 and 6.8.8.

Old step 2 (695 characters):

The integral stratified-perfect characterization applies to $X$: it assumes exactly a finite coefficient field, a noetherian finite-dimensional scheme, and invertibility of $\ell$. It says that $K\in\mathcal C_X$ if and only if $K$ is bounded and its cohomology, on a finite stratification, is locally $B_S\otimes_A N$ for finitely presented $A$-modules $N$. Equivalently its local models are $B_S\otimes_A^L P$ with $P$ perfect. In particular it puts such integral sheaves in degree zero in $\mathcal C_X$, and supplies closure under shifts, cones, truncations and cohomology. This step concerns the integral category only; it does not yet identify its rationalization with the target category.

Uses: lem-weil-pbc-integral-stratified-perfect-characterization.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.6.11; Proposition 6.8.11(3).

Old step 3 (1343 characters):

Scalar localization of module sheaves is exact by the localization/inverse-image coherence lemma, applied to the identity geometric morphism with $R=B_X,t=\varpi$. Its termwise derived functor is $F_X(K)=E_X\otimes^L_{B_X}K$, as also given by derived change of rings. Exactness implies $\mathcal H^r(F_XK)=E_X\otimes_{B_X}\mathcal H^r(K)$: an exact functor preserves the kernels, images and quotients defining cohomology. On a stratum $h:S\to X$ the continuous-coefficient restriction lemma gives $h^{-1}B_X\cong B_S$ and $h^{-1}E_X\cong E_S$, and the coherence lemma (for $h$) commutes $h^{-1}$ with localization; so on an integral local model this sheaf is $E_S\otimes_A N$. A finitely presented module over the DVR $A$ has a finite presentation; after tensoring the presentation with the field $E$, its cokernel is a finite-dimensional vector space, so the last sheaf is locally finite free. Thus $F_XK$ lies in $D_{\mathrm{cons}}(X,E_X)$. Since $\varpi$ acts invertibly after $F_X$, the fraction relation defines $J_X(f/\varpi^n)=\varpi^{-n}F_X(f)$, respecting addition, identities and composition. Raw scalar localization is triangulated with distinguished triangles isomorphic to integral image triangles; hence the triangulated functor $F_X$ induces a triangulated $E$-linear functor $J_X$ into the ambient $D(\operatorname{Mod}(E_X))$.

Uses: lem-weil-pbc-localization-inverse-image-coherence, lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-pur-derived-change-of-rings, def-weil-derived-cohomology-sheaves, def-weil-pbc-rational-category, lem-weil-linear-scalar-localization-triangulated.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2): construction of the functor; Lemma 6.8.2.

### lem-per-constructible-rational-hom-comparison

Old step 4 (1151 characters):

For $K,L\in\mathcal C_X$, verify the Hom-continuity hypothesis of the scalar-localization Hom lemma. Integral bounded-below compactness gives the global-derived-Hom coproduct comparison for every countable family with a common lower bound, including its shift by any integer $q$. Take $H^0$ and use the global-sections/internal-Hom comparison to identify $H^0R\operatorname{Hom}(K,M)$ with $\operatorname{Hom}_{D(B_X)}(K,M)$. Countable sums of $A$-modules are exact, since finite-support coordinates preserve kernels and surjections; their termwise sums represent derived sums by the countable-sums lemma. Thus $H^0$ of their sum is the sum of their $H^0$'s. These observations give precisely the Hom/coproduct hypothesis, and boundedness makes $L$ bounded below. The scalar-localization Hom lemma, with $R=B_X,t=\varpi$, now gives
$$\operatorname{Hom}_{D(B_X)}(K,L[q])[1/\varpi]\cong\operatorname{Hom}_{D(E_X)}(F_XK,F_XL[q]),\quad f/\varpi^n\longmapsto\varpi^{-n}F_X(f).$$
At $q=0$ the left side is the raw category's Hom group. The lemma's identity and composition clauses prove full faithfulness of $J_X$. The target here is $D(E_X)$, not $D(B_X)$.

Uses: lem-weil-pbc-integral-constructible-bounded-below-compactness, lem-pur-rhom-global-sections, lem-kun-derived-countable-sums-exact, lem-weil-pbc-scalar-localization-derived-hom, def-weil-pbc-rational-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 6.8.12; Proposition 6.8.14(2), full faithfulness.

### lem-per-rational-stratum-integral-models

Old step 6 (1161 characters):

Let $F$ be a constructible $E_X$-module sheaf. To use the finite-model stratum-filtration tool, take the condensed ring $C(-,E)$. The continuous-coefficient realization identifies its pulled ring on every scheme with the continuous ring sheaf, naturally for coefficient maps. The internal/sectionwise module equivalence preserves underlying sheaves and actions. Thus a finite free model $E_S^r$ is exactly the tool's finite constant local model $E_S\otimes_E E^r$. This identification is used only for the sheaf filtration, never to infer membership in the completed integral category. Choose the finite noetherian affine cover of $X$. The affine-noetherian-space lemma makes each member noetherian. A descending closed chain stabilizes on each of these finitely many members, hence stabilizes globally. Thus $|X|$ is noetherian, and the filtration lemma applies and gives a finite filtration of $F$ with quotients $v_{k!}(t_k)_*L_k$, where $v_k:V_k\hookrightarrow X$ is qcqs open and $t_k:S_k\hookrightarrow V_k$ is reduced closed. Each local model of $L_k$ is a finitely presented $E$-module, hence a finite-dimensional vector space; therefore $L_k$ is lisse.

Uses: lem-sfb-finite-model-stratum-filtration, lem-weil-pbc-continuous-coefficient-realizations, def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-sc-affine-noetherian-underlying-space.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2), finite stratification devissage; filtration tool uses Stacks Tag 09Y5.

Old step 7 (1164 characters):

Each $S_k$ is noetherian, finite-dimensional and $\ell$-coprime: it is closed in the noetherian open $V_k$, affine rings are quotients of noetherian rings, irreducible closed chains have the dimension bound from $X$, and the inverse of $\ell$ survives in the quotient local rings. Choose a constructible integral lattice $N_k$ for $L_k$ by the lisse-lattice lemma. The ringed open-closed lemma supplies exact $v_{k!}$ and $(t_k)_*$, and their restrictions are $N_k$ on the supporting pieces and zero on the complements. Extending the finite stratification of $N_k$ by those zero pieces proves $M_k=v_{k!}(t_k)_*N_k$ is an integral constructible sheaf; Step 2 certifies $M_k[0]\in\mathcal C_X$, including the etale witnesses. Locally closed coefficient restrictions are the maps of Step 1. Localization is the sequential sheaf colimit of multiplication by $\varpi$, with fractions as transition classes. It commutes with $v_{k!}$ since that functor is a left adjoint, and with $(t_k)_*$ by the filtered-colimit clause of the open-closed lemma on the qcqs $V_k$. Module colimits are the underlying abelian sheaf colimits. Therefore $J_X(QM_k)\cong v_{k!}(t_k)_*L_k$.

Uses: lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-lisse-e-constructible-integral-lattice, lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-integral-stratified-perfect-characterization, lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-left-adjoint-preserves-colimits.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2), integral models for the filtration quotients; Lemma 6.8.13.

### lem-per-rational-realization-finite-cone-models

Old step 5 (724 characters):

Apply the directed-triangulated-image lemma with the singleton preorder, source the raw rationalized category, identity transition, and functor $J_X$ to the ambient $D(E_X)$. Step 3 gives a triangulated functor and Step 4 gives every arrow between its image objects an actual lift; these are the lemma's hypotheses at the unique common stage. Its conclusion makes the essential image closed under zero, shifts and distinguished triangles. If $L$ is a lisse $E_X$-sheaf, the lisse-lattice lemma produces a constructible $B_X$-module $N$ with $E_X\otimes_{B_X}N\cong L$. Step 2 puts $N[0]$ in $\mathcal C_X$, with completeness and compatible etale origins. Hence all lisse sheaves in degree zero belong to the essential image.

Uses: lem-weil-pbc-directed-triangulated-image, lem-weil-pbc-lisse-e-constructible-integral-lattice, lem-weil-pbc-integral-stratified-perfect-characterization.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 6.8.13; Proposition 6.8.14(2), lattice and cone argument.

Old step 8 (623 characters):

Induct over the finite filtration of Step 6, beginning with its zero term. Its short exact sequence $0\to F_{k-1}\to F_k\to v_{k!}(t_k)_*L_k\to0$ is a distinguished triangle in $D(E_X)$ by the short-exact-sequence clause of the heart-triangle lemma for the ambient standard t-structure. Step 7 and the induction hypothesis put its outer terms in the essential image. The connecting morphism lifts by full faithfulness, and the cone closure in Step 5 puts $F_k$ in the image. This proves that every constructible $E_X$-sheaf in degree zero has an integral derived model; it does not assert a globally lisse integral lattice.

Uses: lem-weil-heart-short-exact-triangles, def-sbc-standard-tstructure-derived-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2), sheaf extension devissage.

Old step 9 (698 characters):

For $C\in D_{\mathrm{cons}}(X,E_X)$ choose a finite cohomological interval $[a,b]$ and induct on its length. An object with zero cohomology is zero in the derived category. Otherwise its standard truncation triangle has terms $\tau^{\leq b-1}C,C,\mathcal H^b(C)[-b]$. The first has a shorter interval and the third lies in the image by Step 8 and shift closure. Step 5 gives extension closure, or equivalently lifts the connecting arrow and takes its cone. Thus $C$ is in the image. Together with Steps 3 and 4 this proves the asserted $E$-linear triangulated equivalence. In particular the full target subcategory inherits the ambient distinguished triangles; no idempotent envelope is introduced.

Uses: def-sbc-standard-tstructure-derived-category, lem-weil-heart-short-exact-triangles, def-weil-abstract-derived-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2), bounded truncation induction.

### lem-per-rational-realization-degree-reflection

Old step 10 (567 characters):

The integral t-structure proposition identifies integral truncations and cohomology with the ambient ones and keeps them in $\mathcal C_X$. The localized t-structure proposition gives $\tau_E^{\leq m}QK\cong Q\tau_A^{\leq m}K$ and the analogous upper formula. Exact scalar localization gives the cohomology formula of Step 3, so $J_X$ sends the two localized degree-bound classes into the corresponding ambient degree-bound classes. In particular it is t-exact in this direction, and $J_X(\mathcal H^r(QK))$ is $E_X\otimes_{B_X}\mathcal H^r(K)$ placed in degree zero.

Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure, lem-weil-pbc-localization-inverse-image-coherence, def-weil-derived-cohomology-sheaves.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Propositions 6.8.11(3) and 6.8.14(2): cohomology and forward degree bounds.

Old step 11 (813 characters):

Conversely, if $J_X(QK)$ has no cohomology above $m$, then Step 3 and the integral truncation formula show $J_X(Q\tau_A^{\geq m+1}K)$ has zero cohomology in every degree. It is zero in the derived category, so full faithfulness implies $Q\tau_A^{\geq m+1}K=0$ (its identity is zero). The localized truncation triangle then gives $Q\tau_A^{\leq m}K\cong QK$, putting $QK$ in the localized nonpositive class at $m$. The same argument with $\tau_A^{\leq m-1}K$ proves the converse nonnegative bound. Hence both t-structures agree under $J_X$. Uniqueness of truncation triangles, with their canonical units and counits, makes the truncation comparisons natural. Intersecting the two degree bounds identifies the heart with all constructible $E_X$-sheaves in degree zero, using Step 8 for their essential surjectivity.

Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure, lem-weil-heart-short-exact-triangles, def-weil-abstract-derived-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2): converse degree bounds and truncation/heart identification.

### lem-per-rational-realization-pullback-comparison

Old step 12 (1133 characters):

Fix $g:X'\to X$ as in the statement. Use the actual structural map $c_g:g^{-1}B_X\to B_{X'}$ defined by its finite quotient components, not an assumed isomorphism. Pull back a supporting stratification of $K\in\mathcal C_X$; its base changes form a stratification of $X'$. The trivializing pro-etale covers pull back to covers by weakly etale base change and fpqc covering stability. On each pulled-back cover, ordinary derived module pullback sends $B_S\otimes_A^L P$ to $B_{S'}\otimes_A^L P$: on the finite projective terms the balancing map is $b'\otimes(b\otimes p)\mapsto b'c_g(b)\otimes p$, with inverse $b'\otimes p\mapsto b'\otimes(1\otimes p)$. These maps commute with differentials. Derived pullback is computed on K-flat flat-term resolutions; its tensor and composition comparisons identify this local computation with the restriction of $Lg^*_{B}K$. Every new stratum is locally closed in the noetherian finite-dimensional $X'$, so has the same scheme hypotheses. The stratified-perfect characterization therefore gives $Lg^*_{B}K\in\mathcal C_{X'}$, including derived completeness and compatible etale-origin witnesses.

Uses: def-weil-pbc-completed-pullback, lemma-constructible-pullback-stratification, lem-weil-pbc-weakly-etale-composition-base-change, lem-galois-fpqc-covering-base-change, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-integral-stratified-perfect-characterization.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.6.11; Remark 6.8.15: ordinary pullback preserves the integral category.

Old step 13 (1122 characters):

The specified comparison $\gamma_{g,K}:Lg^*_{B}K\to Lg^*_{\mathrm{comp}}K$ is the quotient-tower completion unit by the completed-pullback definition and the constant/completed comparison. Step 12 makes its source complete. Intrinsic completeness says its Koszul completion unit is invertible, and the constant-completion equivalence identifies that unit with this quotient-tower unit, including transitions. Thus $\gamma_{g,K}$ is invertible, naturally in $K$. Apply localization/inverse-image coherence to $R=B_X,t=\varpi$. It identifies $g^{-1}E_X$ with $(g^{-1}B_X)[1/\varpi]$, preserving the localization unit. The map $c_g$ sends $\varpi$ to $\varpi$, so it extends to the structural map into $E_{X'}$. The ringed-topos derived pullback composition comparison now gives
$$J_{X'}(Q Lg^*_{B}K)\cong E_{X'}\otimes^L_{g^{-1}E_X}g^{-1}(E_X\otimes^L_{B_X}K).$$
Both sides flatten to $E_{X'}\otimes^L_{g^{-1}B_X}g^{-1}K$ by balancing. Composing this comparison with $J_{X'}(Q\gamma_{g,K}^{-1})$ proves the displayed completed-pullback comparison. Its naturality and the fraction rule let it descend to raw rationalizations.

Uses: def-weil-pbc-completed-pullback, def-weil-pbc-intrinsic-completion, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-localization-inverse-image-coherence, lem-sfb-ringed-derived-monoidal-comparisons, def-weil-pbc-rational-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Remark 6.8.15; Stacks Tag 099M (completion units) and Tag 099N as specified by the completed-pullback node.

### lem-per-rational-pullback-composition-coherence

Old step 14 (1261 characters):

For composable scheme maps $X''\xrightarrow h X'\xrightarrow g X$, the structural maps satisfy $c_{gh}=c_h\,h^{-1}c_g$ after the inverse-image composition comparison: composing with each finite quotient projection gives the same finite constant-coefficient map, and the limit universal property gives equality. The ambient derived pullback composition and identity comparisons are those of the ringed-derived monoidal-comparison lemma. Localization/inverse-image coherence identifies the comparison for $gh$ with the composite comparisons for $g,h$, as an equation of natural transformations. On K-flat complexes the tensor maps send a balanced representative $e''\otimes e'\otimes k$ to $e''h^{-1}(e')\otimes k$ in either order; the identity sends $1\otimes k$ to $k$. These maps give the comparisons in Step 13. Under the natural completion units $\gamma$, completed pullback on this category is ordinary pullback; conjugating by those isomorphisms gives exactly the same equations. The finite-reduction and completion-unit comparisons used here preserve the quotient maps, so the conjugation uses the specified units, not arbitrary identifications. This proves naturality, identity and composition with the ambient composition comparisons stated in the item.

Uses: def-weil-pbc-completed-pullback, lem-weil-pbc-localization-inverse-image-coherence, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-constant-completion-equivalence.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Remark 6.8.15: specified ambient identity and composition comparisons.

### lem-per-rational-realization-scalar-coherence

Old step 15 (1025 characters):

For a finite extension $E\subset L$, put $A_L=\mathcal O_L$ and $B_{L,X}=\varprojlim_n(A_L/\varpi_L^n)_X$. The raw scalar-extension proposition defines $T_{L/E}$ by the actual integral change $C_{L/E,X}K=B_{L,X}\otimes^L_{B_{E,X}}K$ followed by rationalization, and puts this object in the integral category under our scheme hypotheses. Continuous-coefficient realization is natural for $A_E\to A_L$ and $E\to L$, so these are the stated continuous ring maps. Apply the ambient derived pullback composition comparison to the same-site coefficient maps. It gives
$$J_{L,X}(T_{L/E}QK)=L_X\otimes^L_{B_{L,X}}(B_{L,X}\otimes^L_{B_{E,X}}K)\cong L_X\otimes^L_{B_{E,X}}K\cong L_X\otimes^L_{E_X}J_{E,X}(QK).$$
The maps flatten $(l\otimes b)\otimes k$ to $lb\otimes k$, with inverses inserting $1$. They are canonical on K-flat representatives, and the comparison lemma descends them to derived categories. The image of every nonzero scalar of $E$ is invertible in $L$, so the equations also hold for the raw morphisms $f/\varpi_E^n$.

Uses: prop-weil-pbc-scalar-extension, lem-weil-pbc-continuous-coefficient-realizations, lem-sfb-ringed-derived-monoidal-comparisons.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2); coefficient naturality of Lemma 6.8.2 and ordinary derived tensor balancing.

Old step 16 (1307 characters):

For $E\subset L\subset M$ both routes in the coefficient associator comparison flatten $m\otimes l\otimes k$ to $ml\otimes k$. For four fields the pentagon flattens all factors to their ordered product; the unit inserts and removes $1$. The ringed-derived comparison lemma makes these equations valid on derived complexes; the raw scalar-extension proposition identifies these associators with its specified ones. To combine with $g:X'\to X$, the square of the integral structural maps $c_g$ and coefficient change commutes, since on each quotient the two composites are postcomposition of the same coefficient map and inverse image of the same section. The continuous realization's coefficient naturality gives the localized square as well. The last clause of the ringed-derived comparison lemma for isomorphic underlying geometric composites identifies the two derived tensor routes. Its balanced map sends $l'\otimes b'\otimes k$ to $l'b'\otimes g^{-1}k$ in either order. The completion-unit comparisons of Step 13 and the scalar-extension/pullback comparison in the raw scalar-extension proposition preserve this equation. Thus the realization comparison commutes with finite coefficient extension, successive extensions, and their pullback and composition associators. No pair-category descent is used.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, prop-weil-pbc-scalar-extension, lem-weil-pbc-continuous-coefficient-realizations, lem-weil-pbc-constant-completion-equivalence.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Proposition 6.8.14(2), Remark 6.8.15: finite-field-extension and pullback coherence.

### lem-per-continuous-coefficient-slice-normalization

Old step 17 (1667 characters):

For a locally closed immersion the coefficient isomorphism is precisely the continuous-coefficient immersion restriction lemma. For an etale map $g:X'\to X$, use the weakly etale localization equivalence $X'_{\mathrm{proet}}\simeq X_{\mathrm{proet}}/X'$. The inverse image $g^{-1}$ of the pro-etale inverse-image definition is this slice restriction: for $U\to X'$ in $X'_{\mathrm{proet}}$ with structure map $s$, the pair $(U\to X,(s,\mathrm{id}_U))$ is initial in the indexing category $\mathcal I_U$, since any $(V,\phi)$ has $\phi=(s,a)$ with $a=\mathrm{pr}_2\phi$ the unique $X$-morphism satisfying $u_g(a)(s,\mathrm{id})=\phi$; hence $(u_{g,p}F)(U)=F(U\to X)$, already a sheaf on the slice, and no sheafification changes it. Restriction to this slice evaluates a coefficient sheaf on the same underlying scheme $V$, so sends $C(|V|,A)$ and $C(|V|,E)$ identically to the corresponding coefficient sheaves on $X'$. In the finite-quotient description it restricts each constant quotient to the same quotient and preserves the sectionwise limit, so the resulting coefficient map is exactly $c_g$, with the constant-section normalizations. The same evaluation argument works for any site object $U\to X$, without requiring $U$ itself to be noetherian. Inverse image with an identified coefficient ring is exact by localization/inverse-image coherence; its termwise derived functor is ordinary inverse image. Hence for the etale and locally closed morphisms the displayed module pullback is exact inverse image, and on an arbitrary site object it restricts to exact site restriction. All identifications preserve coefficient maps by their section formulas and Step 1.

Uses: lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-localization-inverse-image-coherence, def-weil-pbc-completed-pullback, def-weil-proetale-inverse-image.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Remark 6.8.15, etale and closed-immersion clauses; site localization for a pro-etale object.


## Verification

The first required deliver.py --no-push completed with exit 0 and printed OK (not pushed), preflight passed, at efd6c8f2fda. This includes the server checks; no forbidden local checker or compiler was run. I then corrected four invalid-identifier Loogle verdict labels from no match to invalid query (the valid replacement searches and both semantic searches were already run and recorded), and rerun the full required dry run before pushing. The item statement is byte-for-byte the live baseline; all nine new nodes still have empty proof arrays.
