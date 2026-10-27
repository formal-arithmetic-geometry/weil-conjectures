# Q88: lem-weil-point-derived-tensor-tower-coherence

## Files written

- dag/nodes/sec-smooth-purity/lem-weil-point-derived-tensor-tower-coherence.json: statement unchanged; proof replaced by a 2232-character assembly of two independent tasks and the two existing point data lemmas.
- dag/nodes/sec-smooth-purity/lem-weil-sections-scalar-cochain-coherence.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-weil-sections-scalar-derived-transport.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim full statements for all five step/citation pairs. report.md: this repair, review, proof allocation, duplicate comparisons and retained prior report.

## Attachments

None. I searched lean/WeilConjectures by the parent tag and declaration, by sections/tensor/tower concepts, and for the two proposed generic tasks. The recorded parent theorem in lean/Sheaf/Paper/PointDerivedTensorTowerCoherence.lean:405 still ends in sorry. The upstream exact-functor comparison tools in CategoryTheory/DerivedCategory/LeftDerivedFunctor/MapDerivedCategory.lean and the scheme tensor comparison in AlgebraicGeometry/DerivedPullbackCompositionTensorKFlat.lean do not state either new task in full. There is no exact sorry-free project attachment.

## WANTED

None. All source texts used are present.

## Repair of the return

The earlier attempt was byte-identical to the reviewed live item and reported an apparent conflict between fine splitting and duplicate avoidance. The explicit human re-split instruction resolves the scope: the eight arguments must be distributed as new tasks. I compared the retained item against the current read-clone item; they were identical before this repair. The initial required dry run exited 1 with “the item's node file is unchanged” and “the item's proof in words is still 6867 characters”. No other delivery invocation was left running.

The repaired parent keeps its statement, imports, blueprint metadata and all maintainer/stage-2 fields unchanged. It now cites two statement-only, unsplit nodes. The cochain task proves a theorem for arbitrary compatible towers of ordinary rings and sheaf rings on a site with a terminal object. The derived task accepts arbitrary additive functors and coherent natural chain comparisons as hypotheses; it handles the separate K-flat/counit/localization argument. Neither assumes the original point datum or proves the whole parent. They are comparable allocations: old steps 2, 4, 7, 8 plus the termwise part of 3 belong to the cochain task; old steps 3, 5, 6 and the derived passage of 7, 8 belong to the transport task. Old step 1 is the shared point-data verification used to apply both tasks. The complete old prose is retained below, not replaced by a shorter sketch.

The assembly is below 3000 characters; every non-elementary step has the node it needs. Two new nodes are delivered with empty proof and proof_deps, proof_origin null, six actually logged searches each, no Mathlib match, and full blueprint ancestry. Neither new statement depends on the other or on the parent, so separate workers can begin immediately. This repairs the unchanged-item and work-distribution defects rather than rebasing the earlier content.

## Sources and search results

I read main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/def-weil-finite-coefficient-point.md, particularly the final stagewise-colimit paragraph, and dag/units/sk-thm-sf-compatibility.json, coefficient compatibility clause (7). The construction remains ordinary tensor over sheaf coefficient rings; no completion theorem, SGA route, or claim about sectionwise sheaf tensor is introduced.

For the cochain node I read Stacks sites-modules.tex, section-tensor-product, Tag 03EK: the sheaf tensor is the sheafification of the sectionwise balanced tensor, and its bilinear universal property follows below the displayed definitions. I also read the sheafification universal property carried by def-weil-pbc-sheafification. For the derived node I read sites-cohomology.tex, lemma-K-flat-resolution (06YS), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), and lemma-derived-pullback-composition (0D6D), and categories.tex, lemma-properties-left-localization (04VG). Stacks supplies the K-flat composition construction; the full natural-transformation and normalization refinement is an agent argument, explicitly retained below and not falsely attributed to 04VG alone.

Before writing the nodes I searched all DAG statements by sections/associator, sections/scalar-tower, K-flat/counit/localization and the source tags, and ran tools/blueprint_refs.py search for sections tensor, derived pullback composition, scalar tower, sections-tensor, 0D6D and scalar. The nearest ancestor command returned def-weil-finite-coefficient-point. No blueprint node states the new mixed sections comparisons. I opened the generic scalar-tower, quotient-normalization, system-scalar, derived-sections-restriction and ordinary/derived section-normalization candidates as well as every duplicate pair below.

All twelve Mathlib queries in the new nodes were executed with msearch.py and read. All four services/search kinds returned successfully. Second semantic phrasings were tried for both tasks. I read Mathlib Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167 (pullbackComp), ChangeOfRings.lean:1006 and :1016 (normalized ordinary module composition and its associativity), and CategoryTheory/Localization/Predicate.lean:326, :332, :339, :350, :360 (lifting, representative formula, composition, identity and isomorphism). Those are component tools. None states the mixed sections tower theorem or its identification with universal K-flat scalar counits. The grep limited to CategoryTheory/Localization for IsLeftDerivedFunctor/leftDerived composition/KFlat returned no hits. The exact output summaries and digests are in each node, with unchanged query strings also present in searches.jsonl.

## Review by Q88

I checked the repaired statement of the parent byte for byte against the retained statement, including the all-derived-morphisms and four-field clauses. I reviewed each new statement against the source construction, rather than treating the old review as sufficient. In the cochain task the ring maps into Gamma(s,R_i) are explicitly compatible, so a module section has the required ordinary-ring action. No finite freeness, sectionwise flatness, exactness, or invertibility of the sections map is silently assumed: this task proves an equation of maps even when its sections comparison is not an isomorphism. The nested sheaf maps use repeated sheafification factorization, not generation of arbitrary sheaf-tensor global sections by global pure tensors. The derived task separately assumes quasi-isomorphism preservation for every pair and for every G_i and assumes the chain comparison isomorphisms and their coherence. These are the exact hypotheses that localization needs; its conclusion also fixes the comparison by the universal counit, so it does not merely identify the objects abstractly.

For assembly step 1 I re-opened lem-weil-point-finite-free-sections-tensor and lem-weil-point-derived-sections-tensor-descent. The former explicitly gives the constant-section ring isomorphisms compatible with inclusions, the balanced formula and termwise naturality. The latter expressly covers all complexes and the intermediate scalar extension, makes the scalar functors and sections preserve all quasi-isomorphisms, and specifies the derived counit normalization. This supplies precisely the specialization data, including no boundedness or completeness assumptions.

In step 2 the entire new cochain statement was read: its triple equation, sheaf/module inverses, action-unit equation and four-stage sections formula give all the chain-level conclusions that the step takes. I checked that Ai=O_Fi and lambda_i equal to the constant-value maps satisfy the compatibility assumed there. Step 3 uses the new derived-transport statement, which explicitly supplies the counit comparison, identifies the canonical alpha with the localized balanced map, and preserves K-flatness and flat terms after T_ij. A small site is used relative to a larger module universe, as the K-flat tool requires; the identity inverse image preserves finite limits. The required derived theta agrees with the descent dependency because both are pinned by the same representative comparison. Step 4 takes the unit, four-stage, roof-naturality and resolution-independence clauses of the same new statement. Thus no part of the inference appeals only to an internal proof of a cited node. The citations file quotes the complete statements to expose these clauses.

I tested the new claims on zero complexes, complexes in degree zero, identity coefficient maps, three or four repeated stages, the terminal one-object site, and nonflat coefficient maps. The cochain theorem remains valid for nonflat maps because it makes no derived assertion; the derived transfer excludes a nonexact tensor functor through its explicit quasi-isomorphism-preservation hypothesis. For the zero ring or empty topos all the balanced equations remain well typed. On the terminal site the sections equation reduces to the usual scalar multiplication identity. With repeated fields it is the action map, and the four-stage value is independent of parentheses because multiplication in the final ring is associative. No exclusion of ramified finite extensions is needed. I also checked the roof equation types: F(v) maps F(P) to F(C), so its inverse can follow tau_C, and naturality gives the displayed equality with codomain H(J).

The substantive correction was to extract two general, independently formulated arguments rather than fabricate more copies of scalar transitivity or K-flat resolution existence. The generic scalar associator in lem-sfb-flat-scalar-tower-coherence and K-flat transitivity in lem-sfb-successive-derived-quotient-normalization remain reusable tools for the downstream workers. Neither gives the mixed sections square, and the localization universal property alone does not say that its lifted associator is the specified K-flat one. Every new node is a proposition with its own hypotheses, source and definition dependencies; none contains a proof or a proof sketch. I found no remaining statement dispute. On the duplicate-gate repair I read the further seventeen listed statements, including the bilinear universal-property theorem, the direct-image lax pairing and the slice-scalar comparison, and distinguished their functors and conclusions below. I also expanded the transport lemma's four-stage assumptions into the full typed chain equations and named its localized unit maps, to remove an implicit convention. No Lean source or launcher file was changed.

## Not duplicates

lem-weil-sections-scalar-cochain-coherence vs lem-pe-internal-section-tensor-comparison: identifies internal module-object tensor with external sheaf tensor; it does not compare global sections with extension over a separate tower of ordinary rings.
lem-weil-sections-scalar-cochain-coherence vs lem-pe-restricted-kflat-tensor-identification: swaps scalar-first and scalar-last tensors under restriction on a K-flat model; it has no sections comparison or scalar-tower sections square.
lem-weil-sections-scalar-cochain-coherence vs lem-pe-successive-quotient-flat-complex-sequence: constructs a short exact sequence for principal-power quotients; our claim concerns the sections associator and not quotient exactness.
lem-weil-sections-scalar-cochain-coherence vs def-sfb-scalar-extension-pure-tensor-section: defines the local pure tensor section for a single map; it states none of the chain-level sections, unit or tower equations.
lem-weil-sections-scalar-cochain-coherence vs lem-sf-completed-tensor-finite-shift: intertwines a shift with a finite-reduction total tensor tower; it does not compare global sections with scalar extension.
lem-weil-sections-scalar-cochain-coherence vs lem-weil-ramified-finite-pullback-comparison: compares finite geometric pullback with ramified scalar extension at changed indices; no geometric pullback or index reparametrization occurs in our generic sections theorem.
lem-weil-sections-scalar-cochain-coherence vs lem-weil-finite-pullback-transition-generators: gives the formula for a finite pullback quotient transition; it does not state the global-sections scalar associator equation.
lem-weil-sections-scalar-cochain-coherence vs def-sf-unrestricted-reduction-complex-constructions: defines finite reduction and its canonical K-flat comparison, without any sections-tensor coherence assertion.
lem-weil-sections-scalar-cochain-coherence vs lem-trf-site-balanced-tensor-chain: associates a scalar tensor with a second module sheaf in degree zero under restriction; no ordinary-ring global sections comparison is present.
lem-weil-sections-scalar-cochain-coherence vs lem-sf-finite-intrinsic-tensor-generators: normalizes the etale-to-pro-etale intrinsic tensor comparison; our arbitrary-site coefficient-tower sections map is a different functor and no site change is assumed.
lem-weil-sections-scalar-cochain-coherence vs lem-sf-finite-intrinsic-chain-tensor-generators: compares signed total tensors through the intrinsic etale/pro-etale comparison, rather than sections through a tower of coefficient maps.
lem-weil-sections-scalar-cochain-coherence vs lem-weil-ramified-coefficient-quotient-comparison: constructs completed and finite-quotient coefficient comparisons with ramification indices; our statement assumes only compatible maps into section rings and proves their sections coherence.
lem-weil-sections-scalar-derived-transport vs lem-weil-point-derived-tensor-tower-coherence: the parent is the application to completed coefficients over a finite-field point; the transport lemma instead assumes arbitrary coherent chain data and proves a general counit-normalized passage to K-flat derived functors. It does not construct or verify the point-specific chain equations, which are the independent cochain task.
lem-weil-sections-scalar-derived-transport vs lem-sfb-exact-derived-natural-iso: lifts one isomorphism of exact functors; it does not identify the lift with a specified K-flat derived scalar-composition associator or prove the simultaneous tower/sections normalization.
lem-weil-sections-scalar-derived-transport vs lem-sfb-exact-derived-composition: gives the factorization-normalized composition of exact induced functors; it has no K-flat derived scalar functors, scalar counits or sections comparison.
lem-weil-sections-scalar-derived-transport vs lem-sfb-adjunction-localization: descends an adjunction and its triangle identities; our data are scalar associators and arbitrary coherent comparison maps, not an adjunction to be descended.
lem-weil-sections-scalar-derived-transport vs lem-weil-pbc-derived-square-iso-commshift: proves shift compatibility of a particular geometric cartesian-square exchange; our theorem is about coefficient towers, counits and K-flat models.
lem-weil-sections-scalar-derived-transport vs lem-weil-pbc-localization-universal-property: is the generic localization and natural-transformation tool used in the allocated proof; it does not identify any scalar localization with its prescribed K-flat derived functor.
lem-weil-sections-scalar-derived-transport vs lem-pur-additive-localization-descent: shows that a localized functor is additive; it says nothing about canonical derived scalar composition, comparison equations or K-flat representatives.
lem-weil-sections-scalar-derived-transport vs lem-pe-kflat-roos-representative-invariance: proves invariance of a Roos inverse-limit construction; our transfer has no products, Roos complex or inverse limit.
lem-weil-sections-scalar-derived-transport vs lem-sfb-ringed-finite-free-resolution-tensor: computes a derived tensor from a specified bounded finite-free resolution, not unbounded exact scalar/sections functors with simultaneous coherence.
lem-weil-sections-scalar-derived-transport vs lem-sbc-koszul-tensor-derived-tower: identifies ordinary and derived tensor for a particular strict dual Koszul tower; no arbitrary scalar tower comparison or counit-fixed sections transformation is asserted.
lem-weil-sections-scalar-derived-transport vs lem-sbc-scalar-extension-counit-properties: makes the counit invertible on K-flat inputs and supplies a triangulated structure for one scalar map; our theorem includes simultaneous normalized composition and transport of a given coherent comparison.
lem-weil-sections-scalar-derived-transport vs lem-sf-cochain-tensor-model-rigidity: compares bifunctor tensor models restricted to pairs of K-flat complexes; our theorem transports a mixed scalar/sections diagram, using all-representative counits for exact scalar extensions.

lem-weil-sections-scalar-cochain-coherence vs lem-sfb-flat-scalar-tower-coherence: the existing theorem gives the sheaf scalar associator and coherence, which can be reused in the allocated proof. It contains neither a separate ordinary coefficient ring tower nor a global-sections tensor comparison. The new theorem adds exactly that comparison with its chain equations.
lem-weil-sections-scalar-derived-transport vs lem-sfb-successive-derived-quotient-normalization: the existing theorem supplies derived scalar transitivity on K-flat models but no arbitrary mixed comparison functors G_i or simultaneous localization/sections normalization.
lem-weil-sections-scalar-derived-transport vs lem-pur-system-scalar-coherence: normalized scalar models and their derived associators are supplied for a coefficient system; arbitrary sections-type functors and their coherent comparisons are absent.
lem-weil-sections-scalar-derived-transport vs lem-coef-derived-sections-scalar-coherence: that statement concerns R-Gamma with restriction of scalars, not exact ordinary sections with extension of scalars or the scalar tensor associator.
lem-weil-sections-scalar-cochain-coherence vs lem-pd-section-ordinary-oplax-normalization: that statement compares internal and external pullback tensorators under a module-category equivalence, not global sections through an independent coefficient tower.
lem-weil-sections-scalar-derived-transport vs lem-pd-section-derived-tensor-normalization: that statement normalizes an internal/external derived pullback tensorator, with different functors and hypotheses from arbitrary coherent scalar/sections data.
lem-weil-sections-scalar-cochain-coherence vs lem-weil-point-derived-tensor-tower-coherence: the new theorem has no derived categories and assumes arbitrary compatible ring maps on a terminal-object site; it supplies only the independent chain-level part of the original theorem. The parent must still verify its hypotheses and perform the derived transport.

lem-weil-sections-scalar-cochain-coherence vs lem-pc-sheaf-modules-tensor-closed: supplies the closed symmetric monoidal structure for modules over one sheaf ring; it does not compare global sections with scalar extension over a second tower of ordinary rings.
lem-weil-sections-scalar-cochain-coherence vs lem-pc-sites-sheaf-tensor-bilinear-universal: is the bilinear universal-property tool for a single sheaf tensor, not its chain-level scalar-tower and global-sections compatibility.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-hom-tensor-comparison-natural: is naturality of the identification between a sheaf tensor and sheafified presheaf tensor for a fixed ring; it has no coefficient-tower sections square.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-hom-tensor-reverse-pair: curries a map into internal Hom and describes its evaluation on a pair of local tensor factors; the new theorem has no internal Hom or currying.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-hom-tensor-section-natural: proves naturality of the presheaf-to-sheaf tensor section map in two module factors; it does not compare extension along two coefficient ring maps with global sections.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-hom-tensor-summand-localized-ext: is an extensionality criterion for maps into internal Hom out of a single tensor; it states none of the associator, unit or tower comparisons for sections.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-hom-tensor-summand-restriction-ext: detects equality into internal Hom by total-tensor summands; our scalar coefficients lie in degree zero and the conclusion is a sections comparison equation.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-internal-hom-coproduct-fan: sends a coproduct cofan to a limiting internal-Hom fan; it has no scalar extension or global-sections tensor comparison.
lem-weil-sections-scalar-cochain-coherence vs lem-sc-internal-hom-product-fan: preserves a product fan under internal Hom with fixed first variable; there is no internal Hom or product-fan construction in the new theorem.
lem-weil-sections-scalar-cochain-coherence vs def-pd-proetale-section-module-functors: defines internal/external operations for condensed coefficients and their tensor structures; it is not a theorem comparing global sections to an independent coefficient tower.
lem-weil-sections-scalar-cochain-coherence vs def-pd-section-module-operations-data: fixes actual geometric operations and the internal/external section-module equivalence for condensed coefficients; the new claim concerns ordinary global-section modules and ring-tower coherence.
lem-weil-sections-scalar-cochain-coherence vs lem-pd-ringed-direct-image-pairing-lax: constructs a lax monoidal structure for direct image by precomposition between two sites. It does not compare extension over a tower of ordinary rings with sheaf scalar extension through global sections.
lem-weil-sections-scalar-derived-transport vs def-a1-integral-completed-tower-pullback-universes: defines strict derived reduction and tower pullback with specified universal counits; it makes no mixed scalar/sections coherence transport assertion.
lem-weil-sections-scalar-derived-transport vs lem-a1-principal-koszul-strict-replacement: constructs a specific Koszul K-flat replacement of an integral reduction tower; the new lemma assumes exact scalar functors and arbitrary coherent comparison data, with no Koszul complex.
lem-weil-sections-scalar-derived-transport vs lem-per-proetale-scalar-slice-comparison: commutes one scalar extension with exact restriction to a slice and normalizes its derived comparison; it does not give a coefficient tower associator or simultaneous sections/coherence transport.
lem-weil-sections-scalar-derived-transport vs def-pc-derived-tensor-cohomology-vanishes: defines a predicate that one cohomology sheaf of a derived tensor with a degree-zero module vanishes; it is no theorem about counits or natural comparison transformations.
lem-weil-sections-scalar-derived-transport vs def-pc-derived-tensor-complex-cohomology-vanishes: defines cohomology vanishing of a derived tensor of two complexes, with no scalar tower, comparison equation or localization normalization.

## Preserved argument allocation

The following eight paragraphs are the complete old proof text, verbatim, with their old citations retained as task instructions in the report. They are not proof fields of the new unsplit nodes. The cochain task owns 2, 4, 7 and 8 before localization, plus the differential check in 3; the derived task owns the K-flat portion of 3, 5 and 6 and the descent portions of 7 and 8. Paragraph 1 is the point-specific specialization of their hypotheses and remains assembly step 1. This allocation preserves the balance, inverse, differential, normalized descent, roof, unit and four-stage arguments in full.

### Returned step 1

Write $T_{V/U}C=C\otimes_{R_U}R_V$ and $t_{V/U}N=N\otimes_{\mathcal O_U}\mathcal O_V$ on complexes. For each pair in the tower, [lem-weil-point-finite-free-sections-tensor] identifies coefficient sections with their valuation rings compatibly with inclusions and gives the natural chain isomorphism $\theta_{V/U,C}(n\otimes a)=n\otimes a_s$. By [lem-weil-point-derived-sections-tensor-descent], $T$, $t$ and $\Gamma(s,-)$ preserve all quasi-isomorphisms; the localization of $T_{V/U}$ is identified with the stipulated ordinary derived scalar extension by its counit. The localization of this particular $\theta$ is exactly the stipulated $\theta^D$. These statements apply to every complex, including the intermediate $T_{L/E}C$, without a completeness or boundedness assumption.

Cited nodes: lem-weil-point-finite-free-sections-tensor, lem-weil-point-derived-sections-tensor-descent.
Source: literature/stacks-project/sites-cohomology.tex; Tag 06YY, lemma-derived-base-change; specialization through the two cited point-sections comparison statements.

### Returned step 2

For a sheaf $F$, define $u_F: (F\otimes_{R_E}R_L)\otimes_{R_L}R_M\to F\otimes_{R_E}R_M$ by $((x\otimes a)\otimes b)\mapsto x\otimes ab$, using the coefficient inclusions. The inner balance is respected because $(rx)\otimes ab=x\otimes r(ab)$, and the outer balance because $x\otimes(ac)b=x\otimes a(cb)$. Its inverse is $v_F(x\otimes b)=(x\otimes1)\otimes b$: the $R_E$-balance follows from $((rx)\otimes1)\otimes b=(x\otimes r)\otimes b=(x\otimes1)\otimes rb$. These compatible bilinear formulas define sheaf maps by [def-pur-sheaf-tensor-product] and the unique factorization in [def-weil-pbc-sheafification], applied successively to the two tensor factors. They are $R_M$-linear. The composites are the identity, since $(x\otimes1)\otimes ab=(x\otimes a)\otimes b$. Equalities are tested before each sheafification by its uniqueness clause; no assertion that all global sections of a sheaf tensor are pure is needed. Applying the identical balanced formulas to ordinary modules defines $a^{\mathrm{mod}}$ and its inverse. All formulas commute with restrictions and with $f(x)$ for a module-sheaf map $f$.

Cited nodes: def-pur-sheaf-tensor-product, def-weil-pbc-sheafification.
Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product: sheafified tensor and its bilinear universal property; explicit scalar-tower calculation supporting def-weil-finite-coefficient-point, final paragraph.

### Returned step 3

Apply $u$ and $v$ degreewise to any cochain complex $C$. The differential check is $d(x\otimes ab)=dx\otimes ab=u((dx\otimes a)\otimes b)$; the inverse check is the same with $a=1$. Coefficients are in degree zero, so no Koszul signs occur. The maps are natural chain isomorphisms. To compute the derived version, choose $P\to C$ K-flat with flat terms by [lem-pc-kflat-resolution]. Apply [lem-weil-pbc-ringed-topos-kflat-pullback] to the identity morphism of the underlying sheaf topos and the ring map $R_E\to R_L$. The inverse image is the identity (hence preserves finite limits), so its module pullback is precisely $T_{L/E}$. Thus $T_{L/E}P$ is K-flat with flat terms. Take the small-site presentation in the fixed larger module universe used for these sheaf-module categories. By [lem-pur-derived-change-of-rings], both successive derived extensions and direct extension to $R_M$ are consequently computed by these very complexes. Their canonical scalar-composition associator is the class of $u_P$, with inverse the class of $v_P$, as in the K-flat construction of derived pullback composition.

Cited nodes: lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback, lem-pur-derived-change-of-rings.
Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change), and 0D6D (lemma-derived-pullback-composition), specialized to identity underlying topoi.

### Returned step 4

On $((n\otimes a)\otimes b)$ in degree $i$ of $t_{M/L}t_{L/E}\Gamma(s,C)$, the upper route first gives $(n\otimes a_s)\otimes b_s$ and then the section $n\otimes a_sb_s=n\otimes(ab)_s$. The lower route first gives $n\otimes ab$ and then the same section, by [lem-weil-point-finite-free-sections-tensor]. Equality extends to the whole module by additivity and the two tensor balancing relations. The maps commute with differentials by the previous step and by the chain assertion of the cited node. Thus $\Gamma(s,u_C)\theta_{M/L,T_{L/E}C}(\theta_{L/E,C}\otimes1)=\theta_{M/E,C}a^{\mathrm{mod}}$ is an equality of natural chain maps for every $C$, in particular every $P$.

Cited nodes: lem-weil-point-finite-free-sections-tensor.
Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product: sheafified tensor and its bilinear universal property; explicit scalar-tower calculation supporting def-weil-finite-coefficient-point, final paragraph.

### Returned step 5

By [lem-weil-point-derived-sections-tensor-descent], every composite functor occurring in the last equation preserves quasi-isomorphisms before the final localization. Apply [lem-weil-pbc-localization-universal-property] (2) to the natural chain isomorphisms $u,v,\theta$ after composing with target localization. They descend to natural isomorphisms, and (2)-(3) preserve compositions and equality. Conjugate by the counit-fixed comparisons of [lem-weil-point-derived-sections-tensor-descent]. Step 3 identifies the descended $u$ with $\alpha$ on K-flat representatives, and that descent identifies the descended $\theta$ with $\theta^D$ on every representative. The equation of step 4 therefore becomes exactly the displayed derived equation, with its stated source and target.

Cited nodes: lem-weil-point-derived-sections-tensor-descent, lem-weil-pbc-localization-universal-property.
Source: literature/stacks-project/categories.tex; Tag 04VG, lemma-properties-left-localization, together with the fully faithful natural-transformation clause stated in lem-weil-pbc-localization-universal-property; agent calculation after localization.

### Returned step 6

For clarity, the associator's naturality on a roof $C\xleftarrow{q}H\xrightarrow{f}J$ can be checked without choosing a lift between resolutions. Put $F=T_{M/L}T_{L/E}$ and $G=T_{M/E}$, and denote localized chain maps by the same letters. Chain naturality gives $G(f)u_H=u_JF(f)$ and $G(q)u_H=u_CF(q)$. Since $F(q),G(q)$ are invertible by [lem-weil-point-derived-sections-tensor-descent], the latter gives $G(q)^{-1}u_C=u_HF(q)^{-1}$, and substitution yields $G(f)G(q)^{-1}u_C=u_JF(f)F(q)^{-1}$. The same algebra applies to $\theta$ and to the unit maps below. Moreover [lem-weil-pbc-localization-universal-property] makes each descent unique with its representative comparison; thus any K-flat resolution computes this same transformation. Replacing resolutions cannot change either the maps or their equations.

Cited nodes: lem-weil-point-derived-sections-tensor-descent, lem-weil-pbc-localization-universal-property.
Source: literature/stacks-project/categories.tex; Tag 04VG, lemma-properties-left-localization; explicit roof algebra using the cited full natural-transformation statement.

### Returned step 7

For the equal-field case define $m_F:F\otimes_{R_E}R_E\to F$ by $x\otimes r\mapsto rx$; its inverse is $x\mapsto x\otimes1$. Balance and $R_E$-linearity show both composites are identities. The module multiplication map has the identical formula. On a section tensor $n\otimes r$, $\Gamma(s,m_F)\theta_{E/E,F}$ gives $r_sn=rn$, using the coefficient-section identification of [lem-weil-point-finite-free-sections-tensor]. Hence it equals module multiplication, degreewise, naturally in complexes. This is the requested unit equation. Under the descent of step 5 it is the unit equation for $\theta^D$; the representative-normalized comparisons ensure the prescribed multiplication identifications are the ones being used.

Cited nodes: lem-weil-point-finite-free-sections-tensor.
Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product: sheafified tensor and its bilinear universal property; explicit scalar-tower calculation supporting def-weil-finite-coefficient-point, final paragraph.

### Returned step 8

For $E\subset L\subset M\subset H$, apply the already constructed $u$ to a nested sheaf tensor $(((x\otimes a)\otimes b)\otimes c)$. One composition gives $x\otimes(ab)c$, and the other $x\otimes a(bc)$; these are equal by associativity in $R_H$. Repeated uniqueness of the balanced maps of step 2 gives equality as sheaf chain maps. For module tensors the same calculation gives $n\otimes abc$. Repeated use of [lem-weil-point-finite-free-sections-tensor] sends $a,b,c$ to their constant sections, whose product is $(abc)_s$; consequently the iterated sections comparisons give that same section whichever route is chosen. The localization theorem [lem-weil-pbc-localization-universal-property] carries these equalities to derived categories. Step 6 supplies their resolution independence. This includes identity stages and repeated fields, and proves precisely ordinary scalar-tower coherence.

Cited nodes: lem-weil-point-finite-free-sections-tensor, lem-weil-pbc-localization-universal-property.
Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product: sheafified tensor and its bilinear universal property; explicit scalar-tower calculation supporting def-weil-finite-coefficient-point, final paragraph.

## What remains

The two new statement-only nodes await their own proof workers, as expressly requested by the return. The parent assembly and delivery validation are completed by this worker.

## Previous attempt retained (historical)

The previous report is preserved below as an indented record. Its earlier blocker conclusion is superseded by the repair above.

    # Q88: lem-weil-point-derived-tensor-tower-coherence
    
    ## Files written
    
    An unchanged reading copy of dag/nodes/sec-smooth-purity/lem-weil-point-derived-tensor-tower-coherence.json; citations.json containing verbatim statements for the existing eight proof steps; this report. No new nodes and no new Mathlib leaves. The existing mathlib_searches and every other item field are retained verbatim; Q88 does not claim to have performed the historical searches.
    
    ## Attachments
    
    None. Searches in lean/WeilConjectures for the blueprint tag, declaration name and tensor/sections/tower concepts found no declaration giving the complete item. The recorded Sheaf.Paper.PointDerivedTensorTowerCoherence theorem at lines 405-414 still has sorry and is not an attachment under this brief.
    
    ## WANTED
    
    None.
    
    ## Assignment already superseded
    
    The current live item already has status split and a passing independent review by NT-cc-Q140-527d0a86a, group Q140, dated 2026-10-21. It also has a subsequent stage-2 record, which this stage-1 assignment does not authorize changing. coord/brief-stage1.md says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." There was no earlier item copy or report in this sandbox, only dispatcher marker files. Consequently the reading copy preserves the reviewed live split exactly: no invented split_report change or mathematical change has been made merely to produce a delivery diff. The dry run is requested to report whether this stale assignment can be delivered.
    
    ## What could not be finished
    
    A new stage-1 split is superseded by the already reviewed live split. No permission to overwrite that review or reroute the item is inferred.
    
    ## Review by Q88
    
    I read the current item, its chapter sec-smooth-purity and unit sk-thm-sf-compatibility, the full statements of all eight proof dependencies, the final paragraph of main-20261015 def-weil-finite-coefficient-point, and Stacks sites-cohomology.tex at lemma-K-flat-resolution (06YS), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), and lemma-derived-pullback-composition (0D6D). These are the sources of the existing split; no SGA source is used. There are no new nodes to source or review.
    
    Step 1 uses the finite-free node's coefficient-section ring isomorphisms, explicit natural tensor map, and termwise chain assertion. The descent node expressly gives preservation of all quasi-isomorphisms and the representative-normalized comparison, without completeness or boundedness hypotheses, so it applies to the intermediate complex too. Step 2 uses exactly the sheafified tensor definition and sheafification's unique factorization statement; the displayed balancing identities construct the maps and inverse without assuming global sections are generated by pure sheaf tensors. Step 3 uses the K-flat resolution statement, then the ringed-topos pullback statement with identity inverse image (left exact) and the coefficient homomorphism, and then the change-of-rings statement that computes derived extension by K-flat complexes. The small-site presentation is taken in a larger universe as the existing step states.
    
    Step 4 uses the finite-free statement's pure-tensor formula and compatibility of constant sections with coefficient inclusions: both routes give n tensor (ab)_s. Step 5 uses the descent statement's exact scope and the localization statement clauses (2)-(3), which explicitly preserve compositions and detect equality of natural transformations. Step 6 uses the same preservation and uniqueness statements to invert quasi-isomorphisms in the displayed roof calculation; the algebra has the indicated source and target. Step 7 applies the coefficient-section identification at the equal-field stage and computes multiplication in both module and sheaf tensors. Step 8 uses the same coefficient formula and localization equality detection; (ab)c=a(bc) proves the four-field equation before localization. Every citation has a verbatim statement in citations.json. All non-elementary steps are below 2000 characters. The full retained statements were used as quotes to avoid truncating a needed clause of an already reviewed dependency.
    
    I checked the zero complex, a module in degree zero, E=L, L=M, and repeated fields in the four-field calculation. The identities reduce to the indicated multiplication or unit maps. Ramification does not enter the balanced calculation, and no unramifiedness assumption is added. I found no mathematical change necessary for this reading check. The correction needed is administrative: this assignment is stale, because the item's stage-1 split was reviewed before this worker was dispatched.
    
    ## Not duplicates
    
    No new nodes.
    
    ## Dry-run result and conflicting re-split requirements
    
    The single required dry-run invocation exited 1. Its exact diagnostics were:
    
    1. the item's node file is unchanged
    2. re-split (the human, 2026-10-21): the item's proof in words is still 6867 characters; split further until it is at most 3000 characters (each non-elementary argument a new statement-only node the step cites)
    
    After this diagnostic I read coord/repair-notes/lem-weil-point-derived-tensor-tower-coherence.json and tools/preflight_delivery.py lines 355-395. The note explicitly requires at least two new nodes of comparable size and expressly forbids shortening the text alone. This note was not included in the dispatcher brief, and explains why a previously reviewed item was dispatched again. No change has been made to that note or to any tool.
    
    The non-elementary associator/coherence argument already has a general node: lem-sfb-flat-scalar-tower-coherence, whose statement gives the explicit balanced associator, its inverse, the four-ring coherence equation, the action unit, and the termwise-localized derived versions for exact scalar extension. Its ring-object tensor presentation differs in notation, but uniqueness of the relative tensor universal property and the swap of factors identify its maps with the displayed sheaf maps here. It is therefore not legitimate to create a second node for that argument. The existing lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback and lem-pur-derived-change-of-rings already give the K-flat computation. The existing lem-weil-point-derived-sections-tensor-descent and lem-weil-pbc-localization-universal-property explicitly give representative-normalized descent, naturality for roofs, uniqueness, equality detection and resolution independence. The residual sections equation, units and repeated tensor formulas are the elementary calculations written in steps 4, 7 and 8, not legitimate new nodes under the worker's explicit audit rules.
    
    Thus this assignment has a concrete preflight blocker: the recorded re-split requirement asks for new arguments to be allocated as new nodes where the worker rules require reusing the existing general nodes and keeping the residual elementary calculations as steps. I have not fabricated new nodes, weakened the statement, edited the launcher, or pushed a knowingly rejected delivery. The unchanged item and complete diagnostic report are retained in the sandbox for the dispatcher/maintainer to resolve this requirement.

## Validation repairs

The repaired dry run reached the duplicate gate, which requested seventeen additional source-tag comparisons (twelve for the cochain task, five for the derived task). Each listed node was opened and its statement compared, and the distinctions were added under Not duplicates. No new semantic search question arose from spelling out the same four-stage equations. The initial untouched-copy diagnostic was repaired by the two new nodes and the shorter assembly.
