# Repair of lem-tw-ordinary-pullback-stratified-models

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-pullback-stratified-models.json`: statement unchanged, short four-step assembly.
- `dag/nodes/sec-purity-real-sheaves/lem-tw-completed-coefficient-ringed-coherence.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-immersion-chart-comparison.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-purity-real-sheaves/lem-tw-finite-projective-model-pullback.json`: statement, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every proof citation.
- `report.md`: this repair report, source review and preserved argument.

## Attachments

None. The source-tree tag and notion searches under `lean/WeilConjectures/` found no declaration proving the full item. The landed `lean/Sheaf/Paper/OrdinaryPullbackStratifiedModels.lean` contains `sorry` in coefficientMap_comp, modelPullback_existsUnique, perfectModelPullback, derivedSquare_existsUnique, immersionExact, weaklyEtaleExact and ordinaryPullbackStratifiedModels. Its definitions do not constitute finished proofs.

## WANTED

None. All sources used are available locally.

## What was wrong and repaired

The return requests distribution of a 7124-character proof into at least two genuine independent work items, not shorter prose alone. The sandbox initially contained only dispatcher markers, no node, report or search log, so I copied the current returned repository node (no git commands) and retained its statement, metadata, prior Mathlib records and proof. Three new statement-only nodes now carry the separate arguments. They have empty proof and proof_deps, status unsplit, complete hypotheses, source locations and four actually executed search records each. The parent retains the geometry argument; its proof is below 3000 characters. No statement dispute or changed hypothesis. The final self-containedness pass explicitly named the slice restriction functors j_U, j_V, r_U, r_V and the localized morphism g_U, and separated the basis index j from the local coefficient a. The old step-3 source called the ringed-site localization tag 04IF; its precise site-level tag is 04J0. The new coefficient node uses 04J0; the derived sheaf-slice comparison still uses 04IF.

## Argument allocation and preservation

Old step 1 stays verbatim in the item. Old steps 2-3 belong to completed-coefficient-ringed-coherence (composition via finite projections; identify the completed rings and localized structural map on each covering slice). Old steps 4-5 belong to ordinary-immersion-chart-comparison (ordinary derived composition, exact immersion restriction, representable sheaf pullback and ringed slice comparison). Old steps 6-8 belong to finite-projective-model-pullback (retract flatness, K-flat computation, balanced tensors, same idempotents and differential compatibility). Each is a strictly smaller generic theorem, independently usable without a stratification or given charts for K; none restates the full item. The last node can reuse lem-weil-pbc-strict-perfect-ringed-pullback-model for the flatness/K-flat/counit subargument; this does not identify the scalar idempotents or constant-model complex. The original arguments, unchanged, follow as the handoff material for the unsplit workers; they are not proofs entered in the new nodes.

### Original step 1

Apply [lemma-constructible-pullback-stratification] to $f$ and $(i_i)$: the base-changed immersions $j_i$ have pairwise disjoint images $f^{-1}(|S_i|)$ covering $X$. Their images are constructible by [lem-pur-scheme-constructible-preimage], applied to the constructible images of $i_i$. Delete the empty images; this preserves the covering, disjointness and finiteness. Base change each covering family along $f_i$. Its arrows remain weakly etale by [lem-weil-pbc-weakly-etale-composition-base-change] and the family remains fpqc by [lem-galois-fpqc-covering-base-change]. These are precisely the covering conditions in [def-weil-pbc-proetale-site], so the $V_{ia}$ give the asserted covers. No finite-type hypothesis on $f$ is used.

Cited nodes: lemma-constructible-pullback-stratification, lem-pur-scheme-constructible-preimage, lem-weil-pbc-weakly-etale-composition-base-change, lem-galois-fpqc-covering-base-change, def-weil-pbc-proetale-site

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.6.11, base-changing the finite stratification and its local perfect charts; covering base change is Stacks Tags 094U and 022D

### Original step 2

For composable scheme maps $T\xrightarrow h W\xrightarrow k Z$, let $\alpha:(kh)^{-1}\simeq h^{-1}k^{-1}$ be the canonical inverse-image compositor. The finite rings $R/t^n$ of [def-weil-l-adic-coefficient-extension] satisfy [lem-trf-constant-coefficient-composition]. Thus, suppressing $\alpha$ in the notation, the defining projection equations give
$$\pi_{T,n}c_hh^{-1}c_k=c^h_nh^{-1}(\pi_{W,n})h^{-1}c_k=c^h_nh^{-1}(c^k_n)h^{-1}k^{-1}(\pi_{Z,n})=c^{kh}_n(kh)^{-1}(\pi_{Z,n})=\pi_{T,n}c_{kh}.$$
Maps into $B_T$ are determined by all these projections, by [def-pur-sheaf-inverse-limit]. This proves equality of the coefficient structural maps for a composite, and proves their equality at each finite projection at the same time. In particular apply this calculation to $fj_i=i_if_i$. It asserts equality of maps and does not require any of the completed coefficient maps to be invertible.

Cited nodes: def-weil-l-adic-coefficient-extension, lem-trf-constant-coefficient-composition, def-pur-sheaf-inverse-limit

Source: literature/stacks-project/sites.tex; Tag 03CB, lemma-composition-morphisms-sites, and Tag 0H7J, example-constant-sheaf; elementary projection calculation for the inverse limit

### Original step 3

For any chart $u:U_{ia}\to S_i$, [lem-weil-proetale-weakly-etale-localization] identifies $(S_i)_{\mathrm{proet}}/U_{ia}$ with $(U_{ia})_{\mathrm{proet}}$, and identifies the restrictions of every constant ring $R/t^n$ by the identity on constant sections. Limits are sectionwise by [def-pur-sheaf-inverse-limit]; hence the restricted ring $B_{S_i}|_{U_{ia}}$ is $B_{U_{ia}}$, with precisely the restricted finite projections. Do the same on $X_i$ and $V_{ia}$. Apply [lem-weil-pbc-localize-ringed-site-morphism] to the base-change functor defining $f_i$. Its localized coefficient map, under these ring identifications, is $c_{v_{ia}}$: at every finite projection both maps are induced by the same constant-section map, so the preceding projection argument identifies them. Thus this localized ringed morphism is the one used to define $P_{v_{ia}}$.

Cited nodes: lem-weil-proetale-weakly-etale-localization, def-pur-sheaf-inverse-limit, lem-weil-pbc-localize-ringed-site-morphism

Source: literature/stacks-project/sites-modules.tex; Tag 04IF, lemma-localize-morphism-ringed-topoi; proetale.tex Tag 09AE localization convention; sectionwise limit identification

### Original step 4

Use the ordinary unbounded ringed-topos comparison [lem-sfb-ringed-derived-monoidal-comparisons] for $(j_i,f)$ and $(f_i,i_i)$. Step 2 identifies their composite structural maps over the canonical geometric isomorphism associated to $fj_i=i_if_i$, so the specified two-isomorphism transport in that same node identifies $P_{fj_i}$ with $P_{i_if_i}$. The two composition comparisons therefore give $P_{j_i}P_fK\simeq P_{f_i}P_{i_i}K$. Both immersions are locally closed, so [lem-sf-immersion-completed-pullback-comparison] gives ordinary exact $P_{j_i}=j_i^*$ and $P_{i_i}=i_i^*$. This proves the first asserted isomorphism, with no completeness assumption on $K$ or $P_fK$: only the unconditional ordinary-exactness clause of the immersion node is used.

Cited nodes: lem-sfb-ringed-derived-monoidal-comparisons, lem-sf-immersion-completed-pullback-comparison

Source: literature/stacks-project/sites-cohomology.tex; Tag 0D6D, lemma-derived-pullback-composition; K-flat representative normalization; Bhatt--Scholze Remark 6.8.15 for exact immersion restriction

### Original step 5

Apply [lem-sbc-ringed-topos-sheaf-slice-derived-comparison] to the ringed morphism $f_i$ and the sheaf $A=h_{U_{ia}}$, a sheaf by [lem-weil-pbc-proetale-subcanonical]. The base-change functor $u_{f_i}$ preserves finite limits and coverings [def-weil-proetale-inverse-image], and both sites are subcanonical, so [lem-pur-site-representable-algebraic-pullback] gives $f_i^{-1}h_{U_{ia}}\cong h_{u_{f_i}(U_{ia})}=h_{V_{ia}}$. An element of $h_{U_{ia}}(W)$ is an arrow $W\to U_{ia}$, so the element sites of the cited node are the localized sites $(S_i)_{\mathrm{proet}}/U_{ia}$ and $(X_i)_{\mathrm{proet}}/V_{ia}$, with the restricted rings of step 3; the inverse image of $(f_i)_A$, $(H\to A)\mapsto(f_i^{-1}H\to f_i^{-1}A)$, agrees with that of the localized morphism of step 3 by its canonical isomorphism $(f_V)^{-1}j_V^{-1}\cong j_U^{-1}f^{-1}$, and both structural ring maps are $c_{v_{ia}}$ there. The two-isomorphism transport of [lem-sfb-ringed-derived-monoidal-comparisons] therefore identifies $L(f_i)_A^*$ with $P_{v_{ia}}$. The node gives $(P_{f_i}(i_i^*K))|_{V_{ia}}\simeq P_{v_{ia}}((i_i^*K)|_{U_{ia}})$, using the inverse of its displayed $\theta$. Combine this with step 4 and apply the functor $P_{v_{ia}}$ to the given chart isomorphism $(i_i^*K)|_{U_{ia}}\simeq B_{U_{ia}}\otimes_R L_{ia}^\bullet$. This proves the first local comparison in the statement. The cited slice theorem applies to unbounded complexes and arbitrary structural ring maps.

Cited nodes: lem-sbc-ringed-topos-sheaf-slice-derived-comparison, lem-weil-pbc-proetale-subcanonical, def-weil-proetale-inverse-image, lem-pur-site-representable-algebraic-pullback, lem-sfb-ringed-derived-monoidal-comparisons

Source: literature/stacks-project/sites-modules.tex; Tag 04IF, lemma-localize-morphism-ringed-topoi, with its ordinary unbounded derived slice comparison

### Original step 6

Fix one chart and abbreviate $U=U_{ia}$, $V=V_{ia}$, $L=L_{ia}^\bullet$. Put $M^q=B_U\otimes_R L^q$. Choose split maps $L^q\to R^{r_q}\to L^q$ whose composite is the identity, as allowed by finite projectivity. Tensoring these maps exhibits $M^q$ as a retract of $B_U^{r_q}$. For any exact sequence of $B_U$-module sheaves, tensoring with $B_U^{r_q}$ gives its finite direct sum, which is exact componentwise; tensoring with $M^q$ is the direct summand cut out by the displayed splitting, and kernels and images split along the two complementary projections. Thus it too is exact. This verifies flatness directly from [def-pc-flat-sheaf-modules]; no flatness over $R$ of $B_U$ is needed.

Cited nodes: def-pc-flat-sheaf-modules

Source: literature/stacks-project/sites-modules.tex; Tag 03ER, definition-flat, item (3); elementary split-summand argument

### Original step 7

The complex $M^\bullet=B_U\otimes_R L^\bullet$ is bounded, with flat terms by step 6, hence K-flat by [lem-pc-bounded-above-flat-kflat-site]. The computation counit of [lem-weil-pbc-ringed-topoi-derived-pullback] therefore gives the canonical isomorphism $P_v[M^\bullet]\xrightarrow{\sim}[v_B^*M^\bullet]$. This is the specified ordinary derived computation counit, not an isomorphism obtained after completion. Its hypotheses concern the source complex, not flatness of $c_v$.

Cited nodes: lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-ringed-topoi-derived-pullback

Source: literature/stacks-project/sites-cohomology.tex; Tag 06YQ, lemma-bounded-flat-K-flat; Tag 06YY, lemma-derived-base-change

### Original step 8

On a finite free module with basis $e_1,\ldots,e_r$, define the termwise comparison by
$$B_V\otimes_{v^{-1}B_U}v^{-1}(B_U^r)\longrightarrow B_V^r,\qquad b\otimes ae_j\longmapsto b\,c_v(a)e_j.$$
The inverse sends $be_j$ to $b\otimes e_j$; the balanced-tensor relations make the two composites identities. Here inverse image preserves the finite direct sum, as a left adjoint in [def-weil-proetale-inverse-image], and the displayed coefficient maps preserve the constant scalars from $R$ by their constant-section construction and all finite projections. For a finite projective summand represented by an idempotent matrix $e\in M_r(R)$, the same comparison intertwines $v^*(e)$ with $e$ on $B_V^r$, since it sends each constant entry to the same entry. Restrict the comparison and its inverse to this split summand. The formula commutes with every $R$-linear map between summands (apply the formula to its matrix between the chosen free modules), hence with each differential of $L$. Consequently it gives a complex isomorphism $v_B^*(B_U\otimes_R L^\bullet)\simeq B_V\otimes_R L^\bullet$. With step 7 this is the last asserted isomorphism, with exactly the basis and idempotent normalization required. The chart isomorphisms of step 5 now give all displayed conclusions.

Cited nodes: def-weil-proetale-inverse-image

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.6.11, perfect constant local models; Remark 6.8.15, ordinary ringed pullback formula; explicit balanced-tensor calculation

## Mathlib and duplicate searches

Before creating nodes I searched the whole DAG by coefficient composition/localization, derived slice and finite-projective model keywords and by source tags; I ran tools/blueprint_refs.py ancestor on the item, and whole-blueprint searches for completed coefficients, slices, finite projective, coherence and finite-projective. These identify generic tools, not an existing theorem giving each extracted combination with its completed scalar normalization. The nearest imported ancestor is lem-tw-dual-negation, via ordinary-completed-integral-pullback, lisse-rational-realization and dual-stalk-frobenius; each new from.via adds this item, and each from.place specifies the old proof block. same_as is empty.

Every new node has separate leanfinder, loogle, grep and leansearch queries, exactly as logged by msearch.py in searches.jsonl. Each semantic query was followed by a differently phrased query. All services answered. I read the returned signatures and Mathlib sources: PullbackContinuous.lean:167 is underived pullback composition; PullbackFree.lean:118-149 gives free-sheaf generators and naturality; ConstantSheaf.lean concerns constant sheaves and sheaf composition. None proves the completed coefficient slice identification, the ordinary unbounded locally-closed/pro-etale chart comparison, or the whole constant-projective complex/counit normalization. Module.Flat.of_projective is about algebraic modules, not this sheaf-complex conclusion. No Mathlib leaf is claimed.

## Review by Q39

I read Bhatt--Scholze Proposition 6.6.11 (the perfect-values local-model description) and Remark 6.8.15 (ordinary ringed pullback and exact immersion restriction); the coefficient/normalization details remain explicitly agent arguments, not quotations of an unstated published theorem. I read Stacks sites-modules.tex, lemma-localize-morphism-ringed-sites (04J0), including its restricted structural-map formula, and lemma-localize-morphism-ringed-topoi (04IF); sites-cohomology.tex, lemma-derived-pullback-composition (0D6D), lemma-bounded-flat-K-flat (06YQ), and lemma-derived-base-change (06YY). This is the source route of all three extracted nodes; no SGA route is used.

Parent step 1: I opened lemma-constructible-pullback-stratification (base-changed strata), lem-pur-scheme-constructible-preimage (constructibility for arbitrary scheme maps), lem-weil-pbc-weakly-etale-composition-base-change (stability of the chart arrows), lem-galois-fpqc-covering-base-change (stability of the covering family), and def-weil-pbc-proetale-site (weakly etale plus fpqc is precisely the covering condition). These statements have exactly the hypotheses available here. Deleting empty strata preserves finiteness, disjointness and the cover, including X empty.

Parent step 2 uses the full composition and slice clauses of completed-coefficient-ringed-coherence, with all coefficients and projections fixed in that node. I checked the projection equation in old step 2 and the ringed-site identification in old step 3: there is no interchange of a general inverse image with an inverse limit, only a sectionwise slice restriction. This is why arbitrary structural maps cause no gap. At a constant r in R the equations preserve its image at every quotient, which fixes the scalar matrices later.

Parent step 3 uses ordinary-immersion-chart-comparison with the specified fiber products and the arbitrary object K, then only functoriality applied to the chart isomorphism given in the parent hypotheses. I checked the full statements of lem-sfb-ringed-derived-monoidal-comparisons (ordinary composition and transport through geometric 2-isomorphisms), lem-sf-immersion-completed-pullback-comparison (unconditional ordinary exactness clause), lem-sbc-ringed-topos-sheaf-slice-derived-comparison (unbounded complexes and arbitrary structural maps), lem-weil-pbc-proetale-subcanonical, def-weil-proetale-inverse-image (finite-limit and cover preservation), and lem-pur-site-representable-algebraic-pullback (the actual inverse-image representable isomorphism). These supply exactly old steps 4-5; subcanonicality alone is not used as a substitute for representable pullback. The chart theorem requires no chosen local model and proves no model-transport or covering assertion.

Parent step 4 uses finite-projective-model-pullback at each given bounded L. I checked that its degreewise formula is an isomorphism of complexes, not a collection of cohomology identifications: the same scalar matrix idempotent and all scalar maps commute with it. I checked the old retract argument against def-pc-flat-sheaf-modules, the K-flat criterion in lem-pc-bounded-above-flat-kflat-site, and the direction and flat-term hypothesis of epsilon in lem-weil-pbc-ringed-topoi-derived-pullback. The general strict-perfect model theorem supplies that computational part but does not supply the constant-scalar identification. No false assumption of B_U being R-flat is needed.

Small cases: zero L and rank zero yield zero complexes; L=R in one degree gives the tensor unit and the free-basis formula; a nontrivial finite-projective summand eR^r keeps precisely e, not a scalar lift of its reduction; scalar maps between differently ranked summands and nonzero differentials are covered by matrix naturality. Identity scheme maps recover the ordinary identity comparisons. Empty charts and empty base-changed strata impose no model condition. Arbitrary K is allowed because the only K-flat computation imposed on it is through resolution in the generic comparison; boundedness is required solely of the displayed model L. There is no completeness, finite-type, separatedness or base-field condition added anywhere.

I checked delivery-errors B-E: new statements introduce all objects and definitions, proof arrays are empty, searches are real, blueprint ancestry is explicit, every parent citation is quoted verbatim in citations.json, no source tag replaces a proof citation, and no new statement points back to its parent. The three allocations preserve every old argument rather than merely reducing character count. No new parent step exceeds 2000 characters. Existing tool_uses metadata is retained; the parent split_report declares only the off-unit geometric tools it still uses.

## Not duplicates
lem-tw-completed-coefficient-ringed-coherence vs def-sf-open-normalization-data: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Geometric and operation data for open tensor normalization, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs def-weil-pbc-ringed-slice-derived-data: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Derived slice adjunction presentations and coherence squares, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-cbc-completed-finite-scalar-exchange: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Completed-to-finite scalar compatibility of ordinary open exchange, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-cbc-open-localized-counit-comparison: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Open localized finite pullback is the pulled-back extension counit, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-inverse-image-open-free-sheaf: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Inverse image of a represented open free abelian sheaf, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-coefficient-unit-iso: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Invertibility of the open-immersion coefficient unit, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-free-ext-transport: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Open-subscheme Ext transport compatible with scalar maps and base change, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-free-restriction-hom: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Restriction of morphisms from the image-open free sheaf, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-inverse-image-injectives: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Open inverse image preserves injective abelian sheaves, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-restriction-data: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Degree-zero restriction data in the cartesian open-subscheme square, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pc-open-restriction-ext-bijective: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Bijectivity of the constructed open-restriction Ext maps, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pur-integral-object-pullback-line: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Completed inverse image of an integral line with a slice basis, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pur-ringed-site-pullback-dual-free-chart: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Invertibility of a pulled evaluation comparison on a finite-free chart, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pur-ringed-site-pullback-localization-universes: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Module pullback commutes with localization in a containing universe, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-pur-ringed-site-pullback-pairing-transfer: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Extension of module pairings along a ringed site morphism, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-sf-open-operation-models: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Open operation comparisons with fixed tensor models and right square, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-sf-open-pullback-support: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Derived pullback preserves open support, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-sfb-finite-locally-free-ringed-pullback: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Ringed-site pullback preserves finite local bases, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-sfb-identity-open-underived-square-normalization: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Underived adjunction and pullback-square normalization at an identity open locus, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-sfb-normalized-local-module-pullback: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Chosen local module isomorphisms transport uniquely with adjunction-unit normalization, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-localize-ringed-site-morphism: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Localization of a morphism of ringed sites, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-derived-slice-localization: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Derived slice compatibility and pullback of section localizations, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-slice-derived-comparisons: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Normalized derived direct-image slice comparison and invertibility of its mate, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-slice-derived-image-exists: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Existence of normalized total derived module adjunction, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-slice-derived-mate-isIso: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Invertibility of the normalized derived slice comparison mate, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-slice-localization-model: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Ordinary single-complex model for pullback of section localization, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Slice pullback comparison is induced by the ringed localization square, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-slice-commRing-pullback-isIso: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Invertibility of the canonical commutative-ring slice inverse mate, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-slice-module-pullback-isIso: new statement is projection-defined completed coefficient composition AND ringed covering-slice identification with every finite projection; existing statement concerns Invertibility of the canonical module slice inverse mate, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-a1-proper-sections-germ-and-moving-point: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical proper compact rational germs and semilinear moving points, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-pbc-successive-derived-scalar-normalization-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized presentation data for successive derived scalar extensions, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-per-derived-hom-pullback: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical pullback on shifted etale derived Hom, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-pur-cochain-coefficient-arrows: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical scalar-association and transition arrows on cochain sheaves, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-pur-cochain-coefficient-universe-transport: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical common-universe transport of ring and module sheaves, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-pur-cochain-tensor-coherence-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical cochain ringed-pullback and coherence data, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-pur-ringed-coefficient-projection-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized coefficient projection interfaces, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sbc-ringed-sheaf-slice-ordinary-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized ordinary comparison data for sheaf slices, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sf-semilinear-proper-open-comparisons: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-integral-quotient-coefficients: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical integral uniformizer quotient coefficient maps, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-integral-quotient-projection-map: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Integral quotient internal projection arrow, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-internal-derived-scalar-comparisons: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized internal derived scalar comparison interface, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-proetale-composite-coefficients: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composite pro-etale coefficient identification, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-proetale-ordinary-pullback-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Section-normalized ordinary pro-etale pullback composition, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-proetale-projection-exchange-maps: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical projection and exchange maps on internal pro-etale modules, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-ringed-derived-comparison-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Data of normalized derived monoidal comparisons of ringed topoi, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-ringed-projection-coherence-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Recorded data for tensor projection coherence, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sfb-scalar-hom-comparison-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Actual scalar-adjunction and normalized tensor-Hom comparison data, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sp-constant-scalar-pullback-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sp-open-coefficient-adjunction-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Intrinsic open coefficient adjunction data, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-sp-open-scalar-tensor-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Open scalar tensor normalization data, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-trf-integral-comparison-realization-models: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized realization interfaces for integral quotient systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-trf-integral-comparison-sequence-systems: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical pullback and scalar change of whole quotient systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-actual-finite-coefficient-transport: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Actual-ring finite coefficient transport and normalized local restriction, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-derived-direct-image-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition isomorphisms of derived direct images (conjugates of those of inverse images), and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-derived-square-iso: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Square isomorphism on bounded below derived categories, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-normalized-scalar-restriction: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized completed-coefficient scalar and restriction comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-ring-restriction-pullback-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical restriction-of-scalars and identified-coefficient pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-ringed-tensor-square-presentation: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Representative presentation of a commutative ringed tensor square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-strict-tower-operations: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Specified derived operations and mate on strict pro-etale module towers, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-weil-pbc-successive-derived-quotient-data: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized presentations of derived coefficient extension, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-zl-finite-regular-coefficient-comparisons: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Finite regular coefficient comparisons and prescribed pullback compositor, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs def-zl-pbc-finite-raw-scalar-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical comparison of normalized and embedding finite-field scalar extension, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-cbc-strict-tower-direct-image-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Coherence of canonical strict-tower direct image and its square mates, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pe-constant-exchange-encoding: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Constant scalar restriction identifies the ambient ringed exchange, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pe-kflat-scalar-tower-realization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns K-flat realization of the augmented derived scalar-extension tower, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pod-constant-comparison-module-localization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical finite-coefficient derived composition is ordinary module composition localized, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pod-finite-system-pullback-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Coherent composition of finite-coefficient pullback on strict systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pod-integral-pullback-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition isomorphism for integral derived pullbacks, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-canonical-coefficient-system-geometry: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Geometric realization on the literal constant finite coefficient tower, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-cochain-comparison-monoidal-equations: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Monoidal equations for the canonical cochain pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-coefficient-associator-shifts: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Shift compatibility of balanced derived scalar associators, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-coefficient-pullback-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Balanced coherence of canonical coefficient pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-coefficient-pullback-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical inverse-image coefficient comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-coefficient-pullback-shifts: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Shift compatibility of normalized inverse-image coefficient comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-coefficient-scalar-units: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Multiplication units for derived scalar extension, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-factorized-pullback-square-pasting: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Pasting canonical pro-etale derived pullback comparisons for factored endomorphisms, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-geometric-scalar-association-cocycle: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Scalar-association cocycle from normalized inverse-image restriction squares, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-independent-composite-algebraic-image: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Algebraic inverse image and coefficient map for a composite, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-independent-normalized-scalar-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized composition of module scalar extensions, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-module-tensor-coefficient-equations: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Ordinary module tensor equations for coefficient change, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-module-tensor-composition-equation: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Ordinary tensor square for composite module pullback, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-normalized-operation-system-models: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalization and simultaneous models for finite coefficient-system operations, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-pur-normalized-pullback-composition-transport: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Transport of normalized pullback composition through coherent realization, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sbc-pullback-comparison-comp: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition of coefficient pullback and single-complex comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sbc-ringed-sheaf-slice-ordinary-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns The ordinary ringed localization square at an arbitrary sheaf, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sbc-ringed-sheaf-slice-ordinary-square: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns The normalized ordinary ringed square at a sheaf, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sbc-ringed-topos-sheaf-slice-derived-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical unbounded derived adjunction comparisons on arbitrary sheaf slices, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sf-open-exchange-roos-restriction: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Restriction of the strict-limit completed open exchange and its units, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sf-scalar-pullback-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition coherence of normalized scalar/pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sf-semilinear-compositor-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Associative normalized compositors for arbitrary semilinear systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-closed-scalar-hom-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition of the five closed-Hom bijections, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-closed-scalar-hom-transport: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Transport of closed-Hom comparison along adjoint isomorphisms, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-constant-realization-derived-scalar-extension: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Derived constant realization commutes with derived scalar extension, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-etale-proetale-cube-flat-model: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns One flat model computes all six etale/pro-etale scalar cube faces, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-etale-proetale-scalar-pullback-cube: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Etale/pro-etale inverse-image square commutes with derived scalar comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-kflat-scalar-comparison-normalization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Representative and adjunction normalization of scalar pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-quotient-pullback-tensor-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Tensor coherence of the normalized integral quotient pullback square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-comparison-tensor-adjunction: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-derived-composition-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition comparison with normalized representative formulas, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-derived-identity-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Identity comparison with normalized representative formulas, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-derived-monoidal-comparisons: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Monoidal and adjunction normalization of derived ringed-topos comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-projection-pullback-comparisons: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Normalized identity, composition and section pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-projection-tensor-compatibility: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Tensor constraints and compatibility of normalized comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-ringed-projection-tensor-structure: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical tensor structure in arbitrary recorded presentations, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-scalar-hom-tensor-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Tensor coherence of the normalized scalar extension maps, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-scalar-internal-hom-tower-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Coefficient-tower and identity coherence for normalized internal Hom, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-scalar-tensor-tower-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sfb-successive-derived-quotient-normalization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Successive derived scalar extensions agree with direct quotient extension, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-canonical-derived-pullback-normalization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical derived composition is localized normalized ordinary composition, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-canonical-open-scalar-tensor-models: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical scalar tensor models compatible with open inverse image, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-constant-scalar-pullback-cube: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns The canonical constant-ring scalar and geometric pullback cube, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-finite-free-balancing-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Scalar units and associators commute with the canonical balanced pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-finite-free-direct-image-shift: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Shift compatibility of the actual coefficient/direct-image mate, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-intrinsic-open-projection-invertible: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Intrinsic open projection inverse is invertible, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-open-projection-scalar-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Scalar restriction of the normalized open projection, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-open-scalar-coefficient-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Coefficient coherence of scalar pullback, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-proetale-coefficient-tower-normalization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Constant-coefficient tower transport and prescribed scalar-associator normalization, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-scalar-associator-conjugate: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Right conjugate of the normalized scalar associator, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-sp-scalar-tensor-pullback-square: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Scalar tensor comparisons respect arbitrary pullback squares, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-derived-pullback-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Associativity of finite pro-etale derived pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-integral-pullback-comparison-realization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Strict-system realization and composition coherence of integral pullback comparisons, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-point-exact-derived-model: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Exact point models and normalization of derived pullback composition, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-pullback-coefficient-iterate-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Canonical pullback comparisons intertwine coefficient-map iterates, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-quotient-system-mixed-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Mixed geometric and scalar coherence on strict quotient systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-ringed-kflat-word-comparison-descent: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Simultaneous K-flat word models and normalized comparison descent, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-trf-sequence-scalar-generator-interchange: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Ordinary tensor-generator interchange on strict quotient systems, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-completed-reduction-pullback-square: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Completed reduction respects the strict inverse-image square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-derived-inverse-image-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition isomorphisms of derived inverse images and their coherence, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-derived-scalar-extension-local-systems: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Coherent localized derived scalar extension and comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-derived-square-iso-pasting: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Identity and pasting laws of the derived square isomorphism, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-finite-reduction-pullback-coherence: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Finite reduction and the canonical pullback square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-finite-reduction-pullback-square: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Finite reduction respects the inverse-image square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-flat-coefficient-reduction-adjunct: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Finite scalar comparison preserves derived reduction adjuncts, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-frobenius-exchange-restriction: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Finite-level exchange is the restricted ambient exchange, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-proetale-derived-pullback-composition: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Composition of derived pro-etale module pullbacks, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-pulled-reduction-normalization-comparison: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Successive quotient normalizations under the pulled reduction comparison, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-quotient-pullback-compositor-normalization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Quotient module pullbacks respect normalized ordinary and derived composition, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-ring-sheaf-change-adjunction: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Derived adjunctions under compatible changes of ring sheaves, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-ringed-square-localization: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Ambient ringed square is exact localization of its ordinary square, and does not state this combined coefficient/model identification.

lem-tw-ordinary-immersion-chart-comparison vs lem-weil-pbc-ringed-square-tensor-compatibility: new statement is arbitrary completed-integral ordinary derived locally-closed immersion AND representable pro-etale chart comparison; existing statement concerns Tensor compatibility of a ringed square on flat K-flat representatives, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-a1-integral-completed-tower-pullback-universes: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Integral completed strict-tower interfaces at independent universes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-cbc-derived-pair-exchange-normalization: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Representative normalization for abstract derived functor pairs, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-cbc-regular-quotient-cone-basic: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The strict scalar cone and coefficient restriction, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-coef-compact-support-reduction-maps: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical quotient maps and completed-coefficient derived reductions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-coef-compact-support-tensor-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Universal coefficient tensor presentations and canonical compact-support coefficient map, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-coef-ringed-sequence-site: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical ringed sequence site for the coefficient quotient tower, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-coef-semilinear-derived-calculus: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ordinary derived semilinear calculus interfaces, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-coef-semilinear-system-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Generic strict semilinear system constructions and representative normalization, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-fix-proper-etale-origin-scalar-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical scalar, tensor and direct-image comparisons at etale origins, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pbc-successive-derived-scalar-normalization-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized presentation data for successive derived scalar extensions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pe-integral-presentation-encoding: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Specified integral coefficient presentation encoding, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-per-scalar-extension-unit: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical identity scalar-extension unit, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pur-operation-scalar-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Pure-tensor and derived-counit normalized operation scalar transport, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pur-sequence-adjoint-resolution-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Resolution data for the coefficient sequence projection, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pur-strict-quotient-completion-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Strict quotient reduction towers and their canonical completion data, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pur-system-horizontal-reduction-adjoints: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ordinary and cochain horizontal reduction adjoints of semilinear systems, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-pur-vector-purity-scalar-single: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical scalar comparison on degree-zero coefficient sheaves, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-integral-hom-reduction-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical integral internal Hom reduction comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-localized-strict-tensor-comparison-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized cochain computation data for localized strict tensor towers, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-open-normalization-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Geometric and operation data for open tensor normalization, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-open-semilinear-tensor-model-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Simultaneous semilinear open tensor model data, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-ringed-derived-adjoint-lift-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Data of a normalized derived adjoint lift of a ringed-topos morphism, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-strict-tensor-reduction-termwise: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ordinary strict tensor reduction and termwise functors, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sf-unrestricted-reduction-complex-constructions: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Unrestricted reduction complexes and canonical comparison constructions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-adic-residue-lift-comparisons: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The coefficient comparisons and actual finite-reduction Hom tower, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-constant-completion-coefficient-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Constant completion coefficient objects and scalar-extension data, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-derived-change-of-rings-cochain-model: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived change-of-rings cochain presentation, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-integral-quotient-coefficients: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical integral uniformizer quotient coefficient maps, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-integral-quotient-projection-map: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Integral quotient internal projection arrow, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sfb-internal-derived-scalar-comparisons: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized internal derived scalar comparison interface, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-constant-quotient-projection: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The canonical single-quotient reduction projection, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-constant-reduction-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Coupled universal models for strict constant-coefficient reduction, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-constant-scalar-pullback-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-et-proet-coefficient-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Fixed presentation transport of the recorded intrinsic reduction comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-finite-free-direct-image-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized scalar models and canonical coefficient comparison data, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-open-scalar-operations: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Constant-ring pro-etale scalar and open operations and their canonical comparisons, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-sp-proetale-scalar-mate-identifications: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-trf-singleton-site-operations: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Punctual ringed-site operations and normalized comparison predicates, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-trf-split-flat-filtered-sheaf-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Split-flat finite filtered sheaf models and their canonical comparisons, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-integral-derived-reduction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived reduction of integral complexes modulo powers of the uniformizer, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-constant-coefficient-scalar-extension: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Constant coefficient scalar extension on a site, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-derived-normalization-arrows: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical derived coefficient normalization arrows, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-derived-reduction-model-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived reduction model data and normalized complex comparisons, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-koszul-reconstruction-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The fixed Koszul and quotient reconstruction models, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-normalized-origin-scalar-comparisons: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical quotient scalar-extension unit and associator, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-successive-derived-quotient-data: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized presentations of derived coefficient extension, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-weil-pbc-system-scalar-model: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized ordinary and derived scalar model data, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-zl-condensed-scalar-realization: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical derived scalar realization for a commutative condensed ring, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-zl-derived-change-of-rings-model: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical derived change-of-rings cochain model, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs def-zl-ring-derived-scalar-extension: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived restriction and extension of scalars for ordinary modules, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-asd-supported-kummer-scalar-derived-units: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived universal properties of supported scalar maps, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-asd-supported-kummer-scalar-maps: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized supported scalar maps, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-cbc-extension-tensor-comparison-independent: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized scalar-extension tensor comparison in independent universes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-cbc-regular-quotient-cone-chain: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Strict scalar cone augmentation and invariance, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-cbc-regular-quotient-cone-quasi-iso: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Principal quotient cone quasi-isomorphism for every K-flat, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-cbc-regular-quotient-flat-sequence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized principal quotient exact sequence on a flat module, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-coef-etale-tensor-model-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Unique flat-model normalization of the étale scalar tensor comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-coef-exact-sections-reduction-unit: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Exact sections identify principal derived reduction with the actual scalar-extension unit, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-coef-semilinear-operations-existence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Geometric and coefficient operations on a fixed semilinear system calculus, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-coef-semilinear-system-existence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ordinary semilinear system calculus and cartesian internal Hom, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-coef-sequence-projection-derived-adjunction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived adjunction of a ringed sequence projection, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-derived-adjoint-cochain-counit: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The chosen derived-adjunction counit on cochain representatives, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-derived-right-exact-tensor-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized tensor comparison for a right exact strong monoidal functor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-fix-reduction-open-etale-origin: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Bounded etale witnesses for finite reduction and open extension, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-geo-cartier-coeff-extension: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived scalar extension of a closed supported constant sheaf, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-geo-cartier-exponent-independence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Modulus change of the derived quotient and torsion identifications, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pc-bounded-above-flat-tensor-acyclic-degree: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Fixed-degree exactness for bounded-above flat tensor complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-integral-normalized-restriction-squares: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized finite restriction squares for the integral coefficient presentation, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-integral-reduction-transition-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Quotient transitions under normalized integral coefficient comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-kflat-roos-representative-invariance: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat representative invariance of augmented scalar-extension Roos cones, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-kflat-scalar-tower-realization: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat realization of the augmented derived scalar-extension tower, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-restricted-kflat-tensor-identification: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Restricted scalar-first K-flat tensor models identify derived scalar extensions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pe-two-term-reduction-cohomology: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Cohomology and quotient maps of a two-term integral coefficient complex, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-per-proetale-scalar-slice-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized scalar extension comparison on a pro-etale slice, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-derived-reduction-sheaf-resolution-independence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Independence of the sheaf K-flat resolution after exact point sections, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-point-sections-derived-reduction-cone: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Multiplication-cone component, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-point-sections-derived-reduction-homology: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Homology exact-sections component, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-point-sections-derived-reduction-iso: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived point-section comparison component, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-principal-derived-tensor-cone: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived principal quotient tensor is the scalar multiplication cone, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-principal-quotient-quasi-iso: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Principal quotient preserves quasi-isomorphisms on regular complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-principal-reduction-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Descent of exact-sections principal reduction through derived roofs, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-principal-reduction-flat-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Invertibility of the principal reduction comparison on flat models, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pod-scalar-reduction-cochain-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Cochain and homotopy presentations of scalar reduction agree, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-change-of-rings-acyclic-kflat: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Extension of scalars of acyclic K-flat complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-change-of-rings-kflat-quasi-iso: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Termwise change of rings preserves quasi-isomorphisms between K-flat complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-change-of-rings-tensor-acyclic: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Change of rings of a universally tensor-acyclic complex, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-change-of-rings-tensor-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Natural comparison of restricted scalar extension and sheaf tensor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-completed-coefficient-completion-roos-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The normalized completion Roos triangle under completed coefficient transport, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-completed-line-derived: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived finite reductions of a completed coefficient line are ordinary reductions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-constant-field-restriction-representatives: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Restriction preserves flat-term K-flat constant-field representatives, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-constant-two-term-resolution: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Two-term constant-sheaf resolution of Z/ell^N and its tensor augmentation, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-derived-change-of-rings: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-etale-single-functor-monoidal-compatibility: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Canonical flat degree-zero tensor pairings and exact inverse image, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-integral-ambient-operation-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ambient completion presentations for integral pullback and tensor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-integral-object-pullback-line: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Completed inverse image of an integral line with a slice basis, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-ringed-coefficient-change-normalization: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized coefficient changes and their naturality, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-ringed-coefficient-derived-presentation-exists: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Existence of a normalized derived coefficient presentation, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-ringed-derived-pullback-linear: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived ringed-topos pullback preserves compatible central scalars, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-sequence-site-completion-projection: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Constant/limit ringed sequence projection and coherent reduction, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-sheaf-ring-derived-hom-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-system-cochain-tensor-reduction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Cochain scalar-adjoint tensor formula for strict systems, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-pur-system-ordinary-tensor-reduction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Ordinary scalar-adjoint tensor formula for strict systems, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sbc-derived-coefficient-map-descent: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Descent of a termwise coefficient map through a resolving counit, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sbc-derived-scalar-extension-counit-shift: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Counit-compatible shift structure of derived change of rings on a site, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sbc-scalar-extension-counit-properties: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat computation and triangulatedness of a specified scalar-extension counit, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-coefficient-cochain-tensor-curry: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Componentwise coefficient cochain currying, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-coefficient-tensor-curry-normalization: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalization of coefficient tensor currying, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-completion-unit-finite-projection: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Projection of the completion unit is the finite scalar-extension unit, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-derived-complete-legacy-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Intrinsic and K-flat augmented-tower derived completeness agree, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-integral-line-tensor-comparison-representative: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat line tensor models and finite balancing, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-open-operation-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Open operation comparisons with fixed tensor models and right square, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-open-pullback-support: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived pullback preserves open support, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-reduction-pull-finite-evaluation: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Finite evaluation respects the specified reduction/pullback comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sf-scalar-tensor-comparison-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Transport of normalized scalar tensor comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-constant-field-tor-bounds: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Tor bounds over a constant field sheaf, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-derived-section-scalar-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Localization transport of the normalized scalar adjunction, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-divisible-extension-derived-reduction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived reduction of an extension by a divisible sheaf, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-exact-right-adjoint-kflat-representative: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat representative transpose for exact-right derived adjunctions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-finite-flat-constructible-total-tensor: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Bounded flat constructible total tensor on the etale site, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-finite-free-mono-cokernel-kflat: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Finite free sheaf monomorphisms give normalized K-flat cokernel resolutions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-flat-scalar-cyclic-resolution: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Two-term scalar quotient resolutions after flat sheaf extension, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-flat-scalar-tensor-resolution: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Scalar tensor resolutions compute the recorded sheaf derived tensor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-flat-scalar-tensor-units: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Degree-zero ring sheaf is a unit for the recorded derived tensor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-flat-scalar-tor-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Cohomology of flat scalar tensor is scalar Tor, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-ringed-derived-adjoint-lift: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized ordinary and derived adjoint lifts of ringed-topos morphisms, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-ringed-finite-free-resolution-tensor: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Tensor computation from a specified bounded-above finite free sheaf resolution, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-ringed-site-point-kflat-resolution: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat resolution with K-flat stalk, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sfb-standard-sheaf-cotangent-flat-functorial-model: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Flat standard cotangent models for ring sheaves and strict functoriality, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-bounded-flat-coefficient-site-square: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Bounded-flat coefficient/site square with its canonical derived comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-constant-perfect-quotient-projection: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Perfect projection for one constant quotient, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-finite-free-scalar-models: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Existence of normalized actual-restriction scalar models, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-finite-free-scalar-shift: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The normalized scalar counit commutes with shifts and scalar extension is triangulated, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-restricted-scalar-tensor-cohomology-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Underlying cohomology comparison for K-flat scalar extension, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-scalar-associator-conjugate: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Right conjugate of the normalized scalar associator, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-sp-supported-scalar-tor-interval: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Supported scalar tensor interval and reflection to an arbitrary etale origin, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-trf-finite-filtered-flat-resolution: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Flat resolutions for a fixed finite filtration, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-trf-integral-pullback-reduction-counit: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flat reduction-unit counit calculation for integral inverse image, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-trf-ringed-kflat-word-comparison-descent: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Simultaneous K-flat word models and normalized comparison descent, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-derived-scalar-extension-restriction-adjunction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived reduction modulo varpi^n is left adjoint to restriction of scalars, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-cochain-pullback-tensor-shift: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-completed-adic-koszul-kflat: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns K-flatness of the actual completed exterior Koszul complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-constant-coefficient-scalar-equivalence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Bijective constant scalar extension reflects finite lisse cohomology, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-constant-derived-normalization-universal: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Constant derived realization preserves universal coefficient arrows, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-derived-scalar-extension-local-systems: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Coherent localized derived scalar extension and comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-diagram-kflat-replacements: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Objectwise K-flat replacements in strict diagram categories, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-flat-common-quotient-reduction-tower: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived common-quotient reduction as a normalized strict tower, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-flat-scalar-restriction-kflat: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Flat scalar restriction preserves K-flat complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-independent-bounded-flat-kflat: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Bounded-above flat complexes are K-flat at independent universes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived pullback computes K-flat tensor representatives, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalization-compatible evaluation of actual local Isom sheaves, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-normalized-derived-isomorphism-transport: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Universal normalization and evaluation of source-site local Isom sheaves, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-normalized-origin-comparison-coherence: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Comparison reduction respects canonical scalar units and composition, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-pullback-resolving-computation: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived pullback computes on resolving complexes with independent universes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-reduction-pullback-derived-tower: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Normalized derived pullback of a strict coefficient reduction tower, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Common quotient reduction of the geometric scalar comparison, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-ringed-topoi-derived-pullback: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived pullback on ringed topoi computed by K-flat resolutions, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-scalar-extension-unit-triangles: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Scalar-extension maps form morphisms of distinguished triangles, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-site-derived-tensor-descent: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived tensor and K-flat representative descent on a ringed site, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-site-tensor-local-model-comparison: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Tensor cohomology comparison from models of good truncations, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-split-perfect-tensor-kinjective: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Tensoring K-injectives with bounded split-projective complexes, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image, and does not state this combined coefficient/model identification.

lem-tw-finite-projective-model-pullback vs lem-weil-point-derived-sections-tensor-descent: new statement is constant finite-projective scalar complexes with the same scalar idempotents, differential naturality AND ordinary computation-counit normalization; existing statement concerns Derived descent and K-flat normalization of the ordinary point sections-tensor comparison, and does not state this combined coefficient/model identification.

lem-tw-completed-coefficient-ringed-coherence vs lem-weil-pbc-profinite-coefficient-inverse-image: the existing theorem supplies coefficient isomorphisms and composition for finite-ring towers; it does not identify the localized ringed morphism on covering slices with v and its specified structural map. Its composition clause is reused, not a new standalone composition node.

lem-tw-finite-projective-model-pullback vs lem-weil-pbc-strict-perfect-ringed-pullback-model: the existing theorem gives flatness, K-flatness and the ordinary counit for specified sheaf retract packages. It does not identify the pulled constant R-module realization with the same R-module, including scalar matrix idempotents and all differentials; this is the balanced-tensor argument retained in the new node.

lem-tw-finite-projective-model-pullback vs lem-a1-completed-perfect-scalar-pullback: the existing theorem uses strict completed pullback on schemes where ell is invertible; the new theorem specifies the ordinary pre-completion counit and termwise constant-idempotent comparison for any scheme map.

lem-tw-ordinary-immersion-chart-comparison vs lem-a1-integral-stratum-chart-restrictions: the existing theorem is about bounded constructible completed pullback on noetherian finite-dimensional ell-invertible schemes; the new theorem compares ordinary unbounded pullbacks for arbitrary K and an independently given immersion and chart, before completion.

## Unfinished work

Only stage 1 was performed. The three extracted nodes deliberately remain unsplit, to be assigned to parallel workers by the maintainer. Their complete original arguments and candidate reusable generic tools are preserved above.
