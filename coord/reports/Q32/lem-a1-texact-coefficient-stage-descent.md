# Worker report

1. Files written: the item dag/nodes/sec-deligne-laumon-a1/lem-a1-texact-coefficient-stage-descent.json (split, statement unchanged), citations.json, and the three new statement nodes below. Mathlib verdict for all three: no match; status unsplit, empty proof and proof dependencies.
   - lem-a1-linear-texact-scalar-descent: statement, no Mathlib match.
   - lem-a1-texact-pair-descent: statement, no Mathlib match.
   - lem-a1-cohomology-comparison-pasting: statement, no Mathlib match.

2. Attachments: none. The whole project WeilConjectures tree was searched for the blueprint id and coefficient/t-exact/truncation notions. The recorded Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent theorem at lines 342-408 ends in sorry. The StageSystem descent source supplies only the additive construction; no finished project declaration states the complete item.

3. WANTED: none. All used sources were available locally.

4. The human repair note in coord/repair-notes/lem-a1-texact-coefficient-stage-descent.json requires at least three substantive new nodes and an assembly proof of at most 3000 characters. The live node had been reviewed before this re-split request; that does not discharge the dedicated repair. The original statement, its hypotheses and definitions, and all maintainer metadata are retained.

5. Nothing mathematical remains unfinished in this stage-1 assembly. The three extracted nodes intentionally remain statement-only for other workers. No Lean was written and no compiler or build was run.

## Not duplicates

No new node is the whole item: scalar descent has no directed coefficient stages; pair descent assumes exact t-exact stage functors and has no integral localization or cohomology conclusion; comparison pasting assumes t-exactness and has no localization or pair category. The repair instruction specifically asks for these arguments to be separate work items.

lem-a1-linear-texact-scalar-descent vs lem-weil-linear-scalar-localization-triangulated: the existing node constructs the triangulation of one raw localization and exactness of Q, whereas the new node constructs a specified functor between two such categories, its localized shifts, and proves preservation of their halves.
lem-a1-linear-texact-scalar-descent vs prop-weil-localized-tstructure: the latter constructs the particular pro-etale scheme rational t-structure, not functor transport between arbitrary linear categories whose t-structures are already supplied.
lem-a1-texact-pair-descent vs lem-sbc-coherent-pair-functor-descent: the existing node covers the additive pair quotient and compatible transformations (plus Karoubi extension), not the natural descended shift, triangulated exactness, or preservation of the stipulated halves. Its representative calculation is reused as background in the retained argument below, not reintroduced as an additional additive-only node.
lem-a1-cohomology-comparison-pasting vs lem-pod-texact-truncation-comparison: the existing node gives alpha and its transformation/composition laws; the new node asserts the explicit shifted double-truncation cohomology formula, its transformation and composition laws and the induced pasted squares.
lem-a1-cohomology-comparison-pasting vs lem-zl-texact-cohomology-boundary-comparison: the existing node proves compatibility with connecting maps of distinguished triangles for one functor; it does not state transformation, composition or coefficient-square pasting laws.
lem-a1-cohomology-comparison-pasting vs lem-pod-fixed-pair-truncation-cohomology: the latter is about Frobenius-fixed Weil pairs on schemes, not natural transformations between arbitrary t-exact functors.
lem-a1-cohomology-comparison-pasting vs lem-pur-coefficient-evaluation-derived-extension-coherence: that node concerns particular derived scalar adjunction mates and K-flat truncation lifts, not arbitrary bounded t-category cohomology comparison pasting.

lem-a1-linear-texact-scalar-descent vs lem-pc-base-tensor-ordinary-degree-iso: the existing statement identifies two ordinary scalar-extension modules; the new statement constructs a functor between raw localized triangulated categories with localized shifts and preservation of t-structure halves.

lem-a1-linear-texact-scalar-descent vs def-weil-pbc-module-tensor-product: the existing statement defines tensor products and their maps; it does not construct the localized exact t-exact functor asserted by the new statement.

lem-a1-linear-texact-scalar-descent vs lem-trf-reducedness-tensor-alg-equiv: the existing statement concerns reducedness of tensor-product rings under a field algebra equivalence; the new statement concerns exact t-exact functors between scalar-localized categories.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-commshift-nattrans-comp-whisker: the existing statement proves closure of shift-compatible transformations under composition and whiskering; it does not construct scalar-localized functors or establish their preservation of triangles and halves.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-commshift-nattrans-triangle-morphism: the existing statement turns a shift-compatible transformation into a triangle morphism; the new statement constructs and proves exactness and t-exactness of a scalar-localized functor.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-derived-square-iso-commshift: the existing statement concerns a particular derived inverse-image square of schemes and its shifts; the new statement applies to arbitrary linear triangulated categories and raw Hom scalar localization.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-exact-functor-derived-factorization: the existing statement descends a termwise functor of complexes along quasi-isomorphisms; the new statement descends an arbitrary linear triangulated functor along raw Hom scalar extension and preserves stipulated halves.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-triangulated-functor-composite: the existing statement composes two already triangulated functors; the new statement constructs a functor on scalar-localized Hom modules and proves its t-exactness.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-triangulated-functor-restriction: the existing statement restricts an already triangulated functor to full triangulated subcategories; the new statement extends scalars in Hom modules and proves preservation of rational halves.

lem-a1-linear-texact-scalar-descent vs thm-weil-pbc-idempotent-complete-triangulation: the existing statement constructs the triangulation and idempotent completeness of particular constructible coefficient pair categories; the new statement concerns scalar localization of a functor between two arbitrary supplied triangulated categories.

lem-a1-linear-texact-scalar-descent vs thm-weil-pbc-verdier-axioms: the existing statement verifies Verdier axioms of a particular common-stage pair category; the new statement assumes triangulations and proves scalar functor descent with t-exactness.

lem-a1-linear-texact-scalar-descent vs lem-weil-pbc-presentation-base-change: the existing statement base-changes generators and relations of a finitely presented algebra; it contains no triangulated category or t-exact functor assertion.

lem-a1-texact-pair-descent vs lem-pc-elementwise-fp-module-equiv-descent: the existing statement descends an isomorphism of finitely presented modules to a ring stage; the new statement descends a coherent family of exact t-exact functors between pair categories, without finite-presentation assumptions.

lem-a1-texact-pair-descent vs lem-pc-tensor-tail-colimit-elementwise: the existing statement gives representatives and eventual vanishing in tensor modules over a ring colimit; the new statement constructs a coherent pair-category functor and its shifts, exactness and preservation of halves.

lem-a1-texact-pair-descent vs lem-weil-pbc-base-change-diagram-elementwise: the existing statement gives element representatives and eventual vanishing in a base-change module diagram; it does not assert descent of functors between triangulated pair categories.

lem-a1-texact-pair-descent vs lem-weil-pbc-colimit-flat-relation-descent-elementwise: the existing statement descends a finite module relation using flatness over a ring colimit; the new statement uses no flatness and concerns exact t-exact functors of common-stage pair categories.

lem-a1-texact-pair-descent vs lem-weil-pbc-commutative-algebras-colimits-exist: the existing statement supplies colimits of small diagrams of commutative algebras; the new statement assumes additive pair categories and descends functors, shifts, triangles and halves.

lem-a1-texact-pair-descent vs lem-weil-pbc-directed-colimit-base-change-elementwise: the existing statement gives representatives and eventual vanishing in a directed scalar-extension module system; the new statement constructs functors between triangulated pair categories with coherent conjugation maps.

lem-a1-texact-pair-descent vs lem-weil-pbc-directed-tensor-cocones-colimit-n3: the existing statement proves that specified tensor-product ring cocones are colimits; it does not construct an exact t-exact functor between pair categories.

lem-a1-texact-pair-descent vs lem-weil-pbc-filtered-colimit-algebras-elementwise: the existing statement compares algebra and ring colimits and supplies element representatives; the new statement concerns coherent triangulated functor descent and preservation of t-structure halves.

lem-a1-texact-pair-descent vs lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise: the existing statement gives representatives and eventual vanishing after tensoring a filtered algebra colimit; the new statement supplies an exact t-exact functor of pair categories with specified shift comparisons.

lem-a1-texact-pair-descent vs lem-weil-pbc-filtered-colimit-algebras-underlying-module: the existing statement shows a filtered algebra colimit is an underlying module colimit; it asserts no triangulated pair-category functor descent.

lem-a1-texact-pair-descent vs lem-weil-pbc-filtered-colimit-localization-at-prime-data: the existing statement constructs contracted prime-localization ring diagrams and a colimit cocone; the new statement concerns coherent functors on pair categories and their t-exactness.

lem-a1-texact-pair-descent vs lem-weil-pbc-filtered-colimit-localization-at-prime: the existing statement identifies a prime localization of a ring colimit with a colimit of contracted localizations; the new statement assumes pair triangulations and descends exact t-exact functors.

## Sources and searches

Read SETUP's chapter/unit/node levels, GOAL, the stage-1 contract, and both copies of delivery-errors B-E in full. Read the chapter sec-deligne-laumon-a1 and unit sk-thm-dl-a1-upper. This generic transport lemma supports the finite-fibre restriction argument of lem-a1-finite-map-purity through its recorded ancestry; it changes no unit or chapter route. Blueprint searches for scalar localization, t-exact, cohomology comparison, cohomology functors and pair functor found no imported abstract node giving any of these three complete statements. Whole-DAG title/statement searches additionally checked the candidate nodes distinguished above, and the project category-theory Lean source was searched before creation.

Read Stacks algebra.tex lemma-tensor-product (00CX), definition-base-change (05G4), and lemma-directed-colimit (00D6), plus derived.tex definition-exact-functor-triangulated-categories (014V), including its shift-compatible transformation equation. Read BBD Proposition 1.3.3 (printed pp.29-30), Theorem 1.3.6 and 1.3.16-1.3.17 (printed p.36). Read Bhatt-Scholze Proposition 6.8.14 and Remark 6.8.15 (printed pp.61-62); they motivate coefficient localization/colimits but do not claim this abstract theorem. The original proof is correctly agent-written. No SGA route is used.

Each new node was searched with leanfinder, loogle, grep, leansearch and a second leanfinder phrasing; exact queries and unedited tool output are in its mathlib_searches, search-*.txt and searches.jsonl. Read the hits and then Localization/Linear.lean:35-91, Localization/Triangulated.lean:194-213, Triangulated/Functor.lean:260-308 and TStructure/TruncLTGE.lean:648-699. They give infrastructure rather than a one-line specialization to any whole new node. The item's earlier recorded searches were read and retained, not claimed as new Q32 searches.

## Review by Q32

I read every statement cited by every original step, including all nine original proof dependencies, and the statements of the three new nodes. For scalar descent I checked that the induced shift on raw Hom tensors is available only with linear shifts, as the scalar-localization definition stipulates; this is also the reading of the existing stage-2 statement. Identities and composition follow by bilinear extension, and the new node explicitly includes localized inverse shift maps and all integer iterates. The source-target triangle must include the third arrow composed with the shift comparison. Both rational halves are isomorphism closures by hypothesis; one cannot assume that an integral truncation remains the rational truncation without this hypothesis.

For assembly Step 1 the new scalar node states the pure-tensor functor and exact/t-exact conclusion, for exactly the R_E and pi_E used. For Step 2 the new pair node states the same conjugation formula as the item, its representative independence, descended shifts, exactness, t-exactness and exact t-exact stage inclusions. I checked the orientation of b and its inverse: common-stage source is V(FX), b carries it to F(UX), then F(u), then inverse b at the target. The tower equation and naturality give compatible maps even when the transitions kill arrows; no faithfulness is assumed. Triangle and half descent use the hypotheses of the item, not an unproved construction of a triangulation or t-structure.

Step 3 uses clause 4 of lem-weil-heart-short-exact-triangles in both directions, and its statement really gives both implications and the abelian heart. Step 4 uses the full statement of lem-pod-texact-truncation-comparison, including uniqueness and transformation/composition clauses, after boundedness and all-degree preservation are checked. The new pasting node supplies the explicitly specified q formula and the square for arbitrary b, so substituting beta is legitimate. For Step 5 the assumed finite-stage computation respects canonical maps; uniqueness identifies it with alpha for J_E. In the new square set F=J_E^C, F'=J_E^D, U=F_E, V=F_Omega; its orientation is exactly the displayed finite-stage formula. The same square for q and the beta/tower squares prove stage independence, not just an unspecified isomorphism. Every step/node pair has the complete verbatim cited statement in citations.json; this includes exactly the used formula rather than a nearby weaker declaration.

I tested zero categories/functors and zero arrows, identity and repeated coefficient extensions, arbitrary negative j, objects outside a truncation range, and torsion objects killed by rationalization. All preserve the formulas. The quotient argument tests equality only after a common later field, so nonfaithful transitions create no issue. The new nodes have no proofs, proof sketches or hidden claims in proof_deps; they introduce their own variables and carry exact blueprint ancestry. The assembly steps are each below 2000 characters and together below 3000. The extraction is not a new proof route and does not reduce the conclusion.

## Preservation of the original argument

The following is a work map for later workers; it deliberately keeps every original calculation, rather than hiding work by shortening the assembly. Original Steps 1-2 belong to the scalar node; Steps 3-5 to the pair node; Step 6 is the heart criterion retained in assembly Step 3; Step 7 is the existing canonical truncation lemma; Steps 8-9 belong to the pasting node (its alpha component already exists); Step 10 is the application to J_E retained in assembly Step 5. The arithmetic of composing q uses naturality of the intermediate alpha as well as the two composition laws. No new node claims to have proved these arguments yet.

### Original Step 1

Fix $E$ and write $A=R_E[1/\pi_E]$. On each Hom module the $R_E$-linear map induced by $F_E^{\mathrm{int}}$ extends to the $A$-linear map $f\otimes a\mapsto F_E^{\mathrm{int}}(f)\otimes a$ by [def-weil-module-base-change, def-weil-linear-functor]. In the scalar categories [def-weil-linear-scalar-localization], this preserves identity morphisms and composition, since on pure tensors both sides of the composition law are $F_E^{\mathrm{int}}(fg)\otimes ab=F_E^{\mathrm{int}}(f)F_E^{\mathrm{int}}(g)\otimes ab$; bilinearity gives the equality on finite sums. Localize the integral shift comparison $c_K:F_E^{\mathrm{int}}(K[1])\simeq F_E^{\mathrm{int}}(K)[1]$ and its inverse. Naturality on $f\otimes a$ is the integral naturality equation tensored with $a$, using linearity of the shifts and of $c$. The same calculation preserves the iterated shift comparisons. This gives precisely the specified additive $F_E$ with its shift comparison.

### Original Step 2

A distinguished triangle of $\mathcal C_E$ is, by hypothesis, isomorphic to $Q_{\mathcal C}(\Delta)$ for an integral distinguished triangle $\Delta$. Step 1 gives $F_EQ_{\mathcal C}(\Delta)=Q_{\mathcal D}F_E^{\mathrm{int}}(\Delta)$, including the third arrow composed with the shift comparison. This is distinguished because $F_E^{\mathrm{int}}$ is exact and the target triangulation is the stipulated localized one. Its isomorphic images are distinguished by [def-weil-triangulated-category]. Thus $F_E$ is exact. If $K$ is in either rational half at zero, choose an isomorphism $K\simeq Q_{\mathcal C}(K_0)$ with $K_0$ in the corresponding integral half. Its image is isomorphic to $Q_{\mathcal D}F_E^{\mathrm{int}}K_0$, in the corresponding rational half. Hence $F_E$ preserves both halves at zero. The identity $\mathcal C^{\le m}=\mathcal C^{\le0}[-m]$ and its lower counterpart [def-weil-t-structure], together with the shift comparison, give preservation at every integer $m$.

### Original Step 3

For objects $(E_i,K_i)$, choose a common field $L$; these fields form a nonempty directed set by [def-weil-finite-subextension-directed-set]. Write $X_i=T^{\mathcal C}_{L/E_i}K_i$ and $b_i^L=\beta_{L/E_i,K_i}$. The Hom-group map at $L$ is $h_L(u)=(b_2^L)^{-1}F_L(u)b_1^L$. For $M\supset L$, the tower law reads $b_i^M=\beta_{M/L,X_i}\,T^{\mathcal D}_{M/L}(b_i^L)$ after the supplied associators. Substitution gives
$$h_M(T^{\mathcal C}_{M/L}u)=T^{\mathcal D}_{M/L}((b_2^L)^{-1})\,\beta_{M/L,X_2}^{-1}F_M(T^{\mathcal C}_{M/L}u)\beta_{M/L,X_1}\,T^{\mathcal D}_{M/L}(b_1^L)=T^{\mathcal D}_{M/L}(h_L(u)),$$
where the middle equality is naturality of $\beta_{M/L}$. Thus the $h_L$ are compatible additive Hom maps. The universal property of [def-weil-directed-colimit-abelian-groups] gives well-defined additive maps on the Hom colimits; in particular equal representatives have equal images. This proves independence of the common field without assuming that coefficient transition functors are faithful.

### Original Step 4

At a common field for three objects, cancellation of the middle comparison gives $h_L(v)h_L(u)=(b_3^L)^{-1}F_L(v)b_2^L(b_2^L)^{-1}F_L(u)b_1^L=h_L(vu)$, and $h_L(1)=1$. Any two composable arrow classes admit such representatives by directedness and the representative clause of [def-weil-directed-colimit-abelian-groups]. These equalities prove the functor laws for $F_\Omega$. Its object assignment and Hom maps are exactly those in the statement. The structural functors $J_E^{\mathcal C}:K\mapsto(E,K)$ and $J_E^{\mathcal D}$ satisfy $F_\Omega J_E^{\mathcal C}=J_E^{\mathcal D}F_E$ on stage objects and arrows, with the identity-field identifications. For later fields the induced identifications are the specified $\beta_{L/E}$.

### Original Step 5

Give $F_\Omega$ the shift comparison represented at $(E,K)$ by that of $F_E$. This is independent of the stage and natural on every common-stage arrow: for a shift-compatible natural isomorphism $\eta:G\simeq H$ the required square is $c_{H,K}\eta_{K[1]}=\eta_K[1]c_{G,K}$, which is assumed for each $\beta$; naturality of $c_{F_L}$ gives the other square. Every distinguished triangle in the pair category is isomorphic to $J_E^{\mathcal C}\Delta$ for a distinguished triangle $\Delta$ of $\mathcal C_E$. Its image is isomorphic, including the shifted third arrow, to $J_E^{\mathcal D}(F_E\Delta)$, distinguished by step 2 and the assumed description of pair triangles. This proves exactness in [def-weil-triangulated-category]. Likewise every object in either half is isomorphic to $J_E^{\mathcal C}K$ for a $K$ in that finite-stage half; its image is isomorphic to $J_E^{\mathcal D}F_EK$ in the target half. Shifts give all cutoffs as in step 2 [def-weil-t-structure]. This also shows that each $J_E$ is exact and t-exact: it sends a stage triangle to a declared distinguished triangle, commutes with shifts, and sends stage halves into the stipulated pair halves.

### Original Step 6

For $F=F_E$ or $F_\Omega$, preservation of the two halves implies preservation of their intersection, the heart. Apply clause 4 of [lem-weil-heart-short-exact-triangles]: a short exact sequence $0\to A\to B\to C\to0$ in the source heart has a distinguished triangle $A\to B\to C\to A[1]$. Exactness of $F$ gives a distinguished triangle on $FA,FB,FC$, all in the target heart, so the same clause makes its first two arrows a short exact sequence in that heart. The restricted functor is additive because $F$ is additive, and it preserves every short exact sequence. This is the claimed exact functor of hearts.

### Original Step 7

The bounded t-structures for both rational stages and pair categories are hypotheses. Steps 2 and 5 verify exactness with specified shifts and preservation of both halves at every cutoff. Thus [lem-pod-texact-truncation-comparison] applies to each $F_E$ and to $F_\Omega$. It gives both natural isomorphisms $\alpha^-_{F,m}$ and $\alpha^+_{F,m}$, their uniqueness, and exactly the equations $\iota^m_{FK}\alpha^-_{F,m,K}=F(\iota^m_K)$ and $\alpha^+_{F,m,K}F(\pi^m_K)=\pi^m_{FK}$. In particular these are comparisons with the canonical maps, rather than unspecified objectwise truncation isomorphisms.

### Original Step 8

Fix $E\subset L$ and either truncation $\tau$ at $m$. Both composites $G=T^{\mathcal D}_{L/E}F_E$ and $H=F_LT^{\mathcal C}_{L/E}$ are exact and preserve both halves: apply preservation for the two factors in succession. Apply the natural-transformation and composition clauses of [lem-pod-texact-truncation-comparison] to $\eta=\beta_{L/E}:G\simeq H$. Writing the same symbol $\tau$ for the respective stage truncations, its equality is explicitly
$$\alpha_{F_L,T^{\mathcal C}_{L/E}K}\,F_L(\alpha_{T^{\mathcal C}_{L/E},K})\,\beta_{L/E,\tau K}=\tau(\beta_{L/E,K})\,\alpha_{T^{\mathcal D}_{L/E},F_EK}\,T^{\mathcal D}_{L/E}(\alpha_{F_E,K}).$$
This proves beta compatibility for each sign. For $E\subset L\subset M$, the composition clause identifies the comparison for each composite transition with the successive comparisons; apply the transformation clause also to the supplied tower associators. Substituting the assumed beta tower identity into the displayed equality makes the result for $M/E$ identical to its result first for $L/E$ and then for $M/L$. The identity clause deals with $L=E$.

### Original Step 9

Put $N=\tau^{\ge j}\tau^{\le j}K$ and let $c^j_{F,N}:F(N[j])\simeq(FN)[j]$ be the iterated shift comparison. Define
$$q_{F,j,K}=\bigl(\tau^{\ge j}(\alpha^-_{F,j,K})\,\alpha^+_{F,j,\tau^{\le j}K}\bigr)[j]\,c^j_{F,N}:F\mathcal H^jK\xrightarrow{\sim}\mathcal H^jFK.$$
All three factors are natural isomorphisms, so this is a natural isomorphism. For a shift-compatible transformation $\eta:F\Rightarrow G$, use the transformation equation of [lem-pod-texact-truncation-comparison] first for the lower truncation at $\tau^{\le j}K$ and then for the upper truncation at $K$. After shifting their composite and using $c^j_G\eta_{N[j]}=\eta_N[j]c^j_F$, the resulting equation is
$$q_{G,j,K}\,\eta_{\mathcal H^jK}=\mathcal H^j(\eta_K)\,q_{F,j,K}.$$
The composition clause for both alpha factors and the composite shift comparison give $q_{HF,j,K}=q_{H,j,FK}\,H(q_{F,j,K})$. Applying these equations to step 8 proves all beta, identity and successive-extension compatibilities for cohomology. Negative $j$ uses the inverse shift comparisons; the calculation is unchanged.

### Original Step 10

For either truncation let $\gamma_{E,K}^{\mathcal C}:J_E^{\mathcal C}\tau_EK\simeq\tau_\Omega J_E^{\mathcal C}K$ be its finite-stage computation isomorphism from the hypotheses, and similarly for $\mathcal D$. These isomorphisms respect the canonical maps by hypothesis, so uniqueness in [lem-pod-texact-truncation-comparison], applied to the exact t-exact $J_E$ of step 5, identifies them with the canonical comparisons for $J_E$. Apply that lemma's composition clause to $F_\Omega J_E^{\mathcal C}=J_E^{\mathcal D}F_E$ from step 4. It gives
$$\alpha_{F_\Omega,J_E^{\mathcal C}K}\,F_\Omega(\gamma^{\mathcal C}_{E,K})=\gamma^{\mathcal D}_{E,F_EK}\,J_E^{\mathcal D}(\alpha_{F_E,K}).$$
Thus, under the prescribed identifications, the comparison at $(E,K)$ is represented by the comparison at $E$. Replacing $E$ by $L\supset E$ gives the same morphism: the compatibility equation of step 8 is precisely the equation after the common-stage identifications by beta and the transition-truncation comparisons. Hence it is independent of further enlargement. Naturality for arbitrary pair arrows follows either from step 7 or by putting the arrow and these comparisons at its common field and using their stage naturality. Applying the formula of step 9, with shifts also computed at a stage, proves the identical finite-stage representation and independence assertions for $q$.

## Resumed dry-run repair

The first completed dry run flagged shared-tag comparisons absent from the report. I opened all 24 flagged existing statements in full and added individual distinctions above. The tensor/module and ring-colimit facts do not state functor descent; the existing shift and triangulation statements do not give raw scalar extension with preservation of the supplied halves. No node or mathematical assertion changed during this repair.
