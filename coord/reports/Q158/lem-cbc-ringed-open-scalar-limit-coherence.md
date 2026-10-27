## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-ringed-open-scalar-limit-coherence.json`: repaired item, split; statement unchanged; four assembly steps, 2062 characters of proof text.
- `dag/nodes/sec-smooth-purity/lem-cbc-ringed-open-scalar-adjunction.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-cbc-normalized-limit-square-coherence.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: verbatim statements supporting every item-step citation.

## Attachments

None. The search for the exact blueprint tag under `lean/WeilConjectures/` returned no declaration. The related upstream `comapOpenImmersionLowerShriekIso` in `SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:266` is for pulled-back condensed ring objects; it does not state arbitrary ring-sheaf scalar restriction, generator-normalized adjunction identities and strict-limit coherence. The local `Sheaf/Paper/RingedOpenScalarLimitCoherence.lean:442` statement ends in `sorry` at line 596, so is not a finished attachment.

## WANTED

None. Sources needed for this repair are present.

## Returned defect and repair

The return requested a re-split of the eight-step 6806-character proof, preserving its statement and every argument, with at least two comparable statement-only new tasks and an assembly proof at most 3000 characters. The sandbox initially contained only dispatcher brief markers: no node, report, citations or search log survived there. I copied the current repository node, retaining all its metadata, recorded searches and proof in `returned-baseline.json` in the sandbox. The repository text has the eight step sizes given in the return. No Git command was run in the shared repository, and no repository or launcher file was written.

The first new task is about arbitrary small ringed sites, with no pro-etale or quasi-compact-open hypothesis. It carries old Steps 1–3: construction of the identity-induced scalar isomorphism, its explicit generator-normalized units and counits, scalar restriction exactness, and passage to complexes and derived towers. It does not mention products or inverse-limit comparisons.

The second new task is a square of four arbitrary module-sheaf categories and four exact product-preserving functors; no open immersion or scalar functor appears in its hypotheses. It carries old Steps 5–8: product projections, both signed Roos coordinates, passage to the specified normalized derived-limit comparisons, and compatibility of composite augmentation maps. It explicitly states the intermediate product and chain-map equations as well as the resulting derived equation and augmentation identities, so the future worker cannot prove an unspecified isomorphism instead. It is not the whole parent moved under a different name: it does not construct the scalar square, establish its adjunction identities, or verify its exactness and product hypotheses. Conversely the first task does none of this normalized-limit work. Their statements are respectively 2113 and 2697 characters; the original arguments assigned to them are respectively 2578 and 3360 characters, before reusing the existing Roos coherence lemma.

Old Step 4 remains the explicit hypothesis check in assembly Step 2. The two new tasks remain `status: unsplit`, with no proof steps, no proof dependencies, and no proof sketch in their statements. Their future proof arguments are recorded below in the report, not as a completed split of either child. No statement dispute or source correction was required.

## Source and search audit

I read `GOAL.md`, the three levels in `SETUP.md`, the worker brief, stage-1 rules and delivery-errors B–E (including the repeated merged copy). I read the chapter and unit records. The unit's completed-coefficient branch and completed-extension/derived-limit route are retained. The item's nearest blueprint ancestor is `thm-cbc-complete-proetale`, whose proof's first sentence identifies the two-factor completed exchange. I read that proof in the master blueprint and the current `main-20261015` completed-extension-zero-comparison proof, especially its final paragraph applying exactness and derived limits. The blueprint does not itself supply the scalar and signed-normalization calculations; these remain agent-written expansions with that source place, exactly as in the returned item.

For the adjunction task I read `literature/stacks-project/sites-modules.tex`, Tag 03CY (`lemma-sheafification-presheaf-modules`, lines 815 onward), Tag 03DI (`lemma-extension-by-zero`, lines 2058 onward, including both explicit Hom maps), and Tag 03DJ (`lemma-extension-by-zero-exact`, lines 2160 onward). These supply the actual direct-sum presheaf, unique extended action, generator Hom correspondence and exact extension. For the product input I read `proetale.tex`, Tag 09BP (`lemma-j-shriek-limits`, lines 5185 onward): its product argument localizes on the base, so it does not assume a quasi-compact or quasi-separated base.

For the normalized-square task I read the full statements of `lem-cbc-exact-product-functor-strict-limit`, `lem-weil-strict-roos-comparison`, and `lem-pur-roos-comparison-horizontal-coherence`. The last already states the additive-functor product/Roos composition equation, including both product coordinates. Thus I created no third node duplicating old Steps 5–6. Its coordinates `(y,x)` have differential `(-dy-(1-s)x,dx)`; the parent's coordinates `(x,z)` with `z=-y` have differential `(dx,(1-s)x-dz)`. This explicit coordinate change preserves the diagonal product maps, so the existing comparison applies to the new task's signed model. Apply its composition equation to each path of the square and its transformation case to e (or to e and the identity functor). The output is exactly the chain-map square stated in the second child. The remaining theta conjugations and augmentation maps are still obligations of that child, not assumed from the existing lemma.

Before creating the nodes I searched the whole DAG by the source tags and by scalar/open, adjunction, Roos, normalized square and comparison words, and ran `tools/blueprint_refs.py search` for `scalar`, `Roos`, `normalized`, `03DI`, `03CY`, `signed Roos`, `Roos square`, `scalar adjunction`, `normalized limit square`, and `restriction of scalars commutes with open`. Broad hits were refined by reading candidate statements. Neither new statement has a blueprint equivalent; `same_as` is empty. Both new blueprint records use ancestor `thm-cbc-complete-proetale` and via `[lem-cbc-ringed-open-scalar-limit-coherence, lem-cbc-complete-proetale-strict-tower-realization]`.

All Mathlib searches were actually run through msearch.py, using this item and Q158; the exact queries and raw answers are in the sandbox search files, and the script's log is searches.jsonl. Each new node records two different LeanFinder phrasings, a Loogle query, a LeanSearch query and a Mathlib grep. All services answered. For the first child the hits describe module sheafification and scalar restriction, not their slice-extension adjunction compatibility; I read `Sheaf/ChangeOfRings.lean:36` to check the restricted underlying sheaf. For the second the hits give ordinary product/limit comparisons and `Functor.rightDerivedNatIso`; I read `CategoryTheory/Functor/Derived/RightDerived.lean:101–142`. Those facts alone do not identify the specified signed comparison, the four-functor composition square and augmentation normalization, so neither node is a one-line Mathlib specialization. Supplementary logged source greps covered `Algebra/Category/ModuleCat` and `CategoryTheory/Functor/Derived`; they do not change those verdicts. The parent's historical search records were preserved, not rewritten or claimed as new searches.

## Review by Q158

I checked each assembly step against the cited node statements, not their proofs.

Step 1 uses `lem-weil-proetale-weakly-etale-localization` for the actual site equivalence with the slice, which its clause (1) states, and the first new node for e, the exact six functors and the unit/counit identities on derived strict towers. The first child's coefficients are arbitrary ring sheaves on a small site and its slice, so the parent's a, R, S and open object meet every hypothesis; the site's existing universe convention supplies smallness. The child's explicit summand action and unit/counit formulas prevent a different scalar comparison or unspecified adjunction being substituted.

Step 2 uses `lem-weil-pbc-module-sheaves-limits-sectionwise` for sectionwise limits with coordinate action and projections, `lem-cbc-ringed-open-extension-products` for the canonical product comparison of a quasi-compact open, including the empty family and arbitrary base, and `lem-weil-proetale-countable-products-exact` for exact countable products with arbitrary ring sheaves. All three statements explicitly give the needed claims. The scalar product comparison is the elementary identity of the same groups, actions restricted through a, and coordinate projections. Quasi-compactness is used only for the J comparison; it is available for j in the item. No assumption on T was added.

Step 3 uses the second child for its exact derived-square identity and naturality, and `lem-cbc-exact-product-functor-strict-limit` to pin the lambda maps to the signed theta/kappa formula and K-injective resolution normalization. I checked the four domain/codomain categories and F=J_S, G=r_T, H=r_U, K=J_R: both composites start in Mod(S_U) and end in Mod(R_T). The first step supplies the exact square; Step 2 supplies exact countable products and invertible canonical product maps. Thus the formula substitutes to exactly the parent's equation. The child promises derived naturality, so no unproved assertion about roofs is hidden in the assembly.

Step 4 uses the second child's three augmentation assertions: compatibility along GF, compatibility along KH, and identification under e. A quotient augmentation is an instance of a strict augmentation; its termwise maps remain quotients by the exactness already supplied in Step 1. This step does not require scalar restriction to preserve K-injectives. The signed map `(gamma,0)` is included in the child's specified normalization through its cited normalized comparison.

For B–E I checked that each new statement introduces all its rings, sites, categories, functors, transformations and normalization maps; every nonstandard notion points to its defining node. Neither child depends on the parent. The general horizontal Roos lemma is not made a new node. All other facts used by assembly steps are in their cited statements, and citations.json copies verbatim text. Source places are tags plus labels for the Stacks construction and an identified blueprint paragraph for the agent expansion. No SGA route is used. Each new node has only a statement and genuine logged searches. The parent has no proof step over 2000 characters and its assembly is below 3000 characters. I retained its statement verbatim, its existing Lean attachment and maintainer metadata, and historical searches.

I tested the identity coefficient map, the zero ring and zero sheaves, empty U, the identity open, the empty product, constant and zero towers, and zero augmentations. In the empty-product case the module terminal object is zero, so restriction has exactly the same empty comparison. The general square permits identity functors and identity e; the product and chain formulas then reduce to the usual canonical comparison composition, and the signed map has zero shifted component. For an arbitrary nonidentity e, projections give the typed equality e_N GF(pi)=KH(pi)e_P; no equality of chosen representatives is assumed. The sign change above checks both differentials, not only their underlying graded objects. The old argument never used flatness, finite Tor dimension, boundedness or preservation of K-injectives, and neither repair node introduces one.

## Not duplicates

- lem-cbc-ringed-open-scalar-adjunction vs def-sfb-comap-open-immersion-shriek-iso: the latter treats module objects over pulled-back condensed coefficients and states only the ordinary isomorphism; the new node treats arbitrary ring sheaves on any small site and states the specified generator adjunction and derived-tower identities.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sf-open-extension-scalar-restriction-coherence: the latter assumes finite constant coefficients and supplies a coefficient-composition cocycle; the new node treats arbitrary ring sheaves and identifies the chosen slice adjunction units and counits, including strict towers.
- lem-cbc-ringed-open-scalar-adjunction vs lem-weil-pbc-continuous-extension-scalar-change: the latter concerns continuous extension of lattice coefficients, rather than arbitrary module sheaves on a localized ringed site with normalized adjunction maps.
- lem-cbc-normalized-limit-square-coherence vs lem-pur-roos-comparison-horizontal-coherence: the existing lemma is the chain-level product/biproduct calculation and is reused for the new child's proof; it has neither total derived limits, normalized theta comparisons nor the resulting derived-square and composite augmentation identities.
- lem-cbc-normalized-limit-square-coherence vs lem-cbc-exact-product-functor-strict-limit: the latter constructs one functor's normalized comparison, not coherence under a natural isomorphism between two composites of four functors.
- lem-cbc-normalized-limit-square-coherence vs lem-cbc-exact-product-functor-roos-compatibility: the latter states triangle and augmentation identities for one prescribed comparison, not the four-functor coherence equation.

- lem-cbc-ringed-open-scalar-adjunction vs lem-cbc-ringed-open-scalar-limit-coherence: the parent also needs the pro-etale product hypotheses and the normalized limit square; the new task handles arbitrary-site scalar/adjunction construction and localization only, and is independent of the limit-square task.
- lem-cbc-ringed-open-scalar-adjunction vs def-pe-finite-discrete-presentation-encoding: the existing definition supplies continuous-to-constant coefficient encoding data, not a slice-extension scalar adjunction theorem.
- lem-cbc-ringed-open-scalar-adjunction vs def-sfb-constant-module-coefficient-transport: the existing definition transports constant modules across a constant-ring comparison, not arbitrary ring-sheaf extension by zero or its adjunction.
- lem-cbc-ringed-open-scalar-adjunction vs def-sfb-scalar-extension-pure-tensor-section: the existing definition concerns pure tensors for scalar extension; the new result concerns scalar restriction and a slice-extension adjunction.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-hom-tensor-comparison-natural: the existing lemma concerns tensor/sheafification naturality and has no extension-by-zero adjunction.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-exterior-sheaf-comparison: the existing lemma identifies exterior-power sheaves and has no slice extension or scalar adjunction.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-hom-tensor-section-natural: the existing lemma concerns tensor-section maps and has no slice-extension scalar adjunction.
- lem-cbc-ringed-open-scalar-adjunction vs lem-pc-open-localized-module-sheafification: the existing lemma commutes restriction and module sheafification on a topological open site, not scalar restriction and left-adjoint extension on an arbitrary site.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-exterior-dual-pairing-local: the existing lemma constructs the local determinant pairing, not any scalar/open adjunction comparison.
- lem-cbc-ringed-open-scalar-adjunction vs lem-pc-sites-module-sheafification-interface: the existing lemma supplies uniqueness of the sheafified module action, an input construction already reused through the definition node; it does not state the slice adjunction scalar square.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-exterior-sheaf-dual-ext: the existing lemma is extensionality on pure wedges, not extension by zero or scalar restriction.
- lem-cbc-ringed-open-scalar-adjunction vs lem-sc-exterior-dual-pairing-functional: the existing lemma constructs an exterior dual section by a determinant, not a scalar adjunction identity.

## Preservation of every returned argument

The following is the returned proof verbatim, with its new ownership. This retains the complete mathematical work for the next workers; it is not a proof field of either statement-only child. Old Step 4 remains in the parent as the hypothesis check. Old Steps 5–6 are obligations stated in the normalized-square child, with the already-existing horizontal Roos comparison available for their proof.

### Returned Step 1 → lem-cbc-ringed-open-scalar-adjunction

Use the slice-site identification of [lem-weil-proetale-weakly-etale-localization]. For an $S_U$-module sheaf $N$, the two extension presheaves have the same abelian groups and restriction maps: at $V$ they are $\bigoplus_{\varphi:V\to U}N(V,\varphi)$. Their $R(V)$-actions are both $r(s_\varphi)_\varphi=(a_V(r)s_\varphi)_\varphi$, by [def-pc-sheaf-restrict-scalars, def-weil-extension-by-zero-presheaf]. By [def-weil-presheaf-modules-sheafification], their abelian sheafifications coincide and the induced $R$-actions coincide by uniqueness of the extending action. The identity thus induces $e_N:r_TJ_SN\to J_Rr_UN$ and its inverse. A map of $N$ acts on each summand by the same map on either side, so $e$ is natural.

Cited nodes: lem-weil-proetale-weakly-etale-localization, def-pc-sheaf-restrict-scalars, def-weil-extension-by-zero-presheaf, def-weil-presheaf-modules-sheafification.
Source: literature/stacks-project/sites-modules.tex; Tags 03DI (lemma-extension-by-zero), 03CY (lemma-sheafification-presheaf-modules); identity of scalar-restricted presheaves.

### Returned Step 2 → lem-cbc-ringed-open-scalar-adjunction

For the adjunction of [lem-pur-site-restriction-module-adjunction-exact], a map $h:N\to j^*Q$ extends to $J N\to Q$ by sending the generator $s$ in the summand indexed by $\varphi:V\to U$ to $h_{(V,\varphi)}(s)\in Q(V)$, then using sheafification. Conversely restrict such a map and precompose with the summand inclusion; these operations are inverse since all summand generators generate the presheaf and sheafification has unique factorization. Consequently $\eta_N$ sends $s$ to its summand generator followed by sheafification and $\epsilon_Q$ sends each generator to the same section of $Q(V)$. Scalar restriction changes none of these maps. Also $j_R^*r_T=r_Uj_S^*$ objectwise. Thus $j_R^*(e_N)\,r_U(\eta_N^S)=\eta_{r_UN}^R$ and $\epsilon_{r_TQ}^R\,e_{j_S^*Q}=r_T(\epsilon_Q^S)$, with the displayed restriction identification understood.

Cited nodes: lem-pur-site-restriction-module-adjunction-exact, def-weil-extension-by-zero-presheaf, def-weil-presheaf-modules-sheafification, def-pc-sheaf-restrict-scalars.
Source: literature/stacks-project/sites-modules.tex; Tag 03DI (lemma-extension-by-zero), proof: the two explicit Hom maps; Tag 03CY.

### Returned Step 3 → lem-cbc-ringed-open-scalar-adjunction

Scalar restriction preserves kernels because they are sectionwise kernels with the restricted action; it preserves cokernels because sectionwise quotient groups and their abelian sheafification are unchanged, with the unique restricted action. These kernel/cokernel descriptions are [def-weil-sheaf-of-modules-category], and the action is [def-pc-sheaf-restrict-scalars]. Hence $r_U,r_T$ are exact. Both $J$ and both $j^*$ are exact by [lem-pur-site-restriction-module-adjunction-exact]. For strict towers the same conclusions hold levelwise by [lem-weil-tower-category-levelwise-abelian]; the natural transformations of Steps 1–2 satisfy the tower transition equations by their naturality. Apply all functors and transformations in every cochain degree. Exactness permits descent to the unbounded derived categories by [lem-sf-exact-functor-derived-triangulated]. The derived adjunction of [def-weil-exact-derived-adjunction] has the localized original unit and counit, so the identities in Step 2 descend as well.

Cited nodes: def-weil-sheaf-of-modules-category, def-pc-sheaf-restrict-scalars, lem-pur-site-restriction-module-adjunction-exact, lem-weil-tower-category-levelwise-abelian, lem-sf-exact-functor-derived-triangulated, def-weil-exact-derived-adjunction.
Source: literature/stacks-project/sites-modules.tex; Tags 03CY, 03DJ (lemma-extension-by-zero-exact); derived localization uses the specified exact-derived adjunction.

### Returned Step 4 → parent assembly Step 2

By [lem-weil-pbc-module-sheaves-limits-sectionwise], a product is the sectionwise product with coordinate actions. Thus restricting scalars gives exactly the same underlying product and projections, including the empty product, whose underlying group is zero. Invertibility of the canonical product comparisons for $J_R,J_S$ is [lem-cbc-ringed-open-extension-products], applicable since $j$ is quasi-compact; the base need not be quasi-compact or quasi-separated. Countable products are exact in each of the four ringed categories by [lem-weil-proetale-countable-products-exact], for arbitrary ring sheaves. Together with Step 3 this verifies all hypotheses of [lem-cbc-exact-product-functor-strict-limit] for each of $r_T,J_S,J_R,r_U$. Write $\phi_F$ for their canonical product maps and $\kappa_F$ for the maps on the two signed Roos summands specified by that node.

Cited nodes: lem-weil-pbc-module-sheaves-limits-sectionwise, lem-cbc-ringed-open-extension-products, lem-weil-proetale-countable-products-exact, lem-cbc-exact-product-functor-strict-limit.
Source: literature/stacks-project/proetale.tex; Tag 09BP (lemma-j-shriek-limits); the ringed product and normalized exact-product comparison statements cited here.

### Returned Step 5 → lem-cbc-normalized-limit-square-coherence

Hereafter set $A=r_TJ_S$ and $B=J_Rr_U$. For any countable family $(N_n)$ in $\operatorname{Mod}(S_U)$, with $P=\prod_nN_n$, form
$$u=(\prod_ne_{N_n})\,\phi_{r_T,(J_SN_n)}\,r_T(\phi_{J_S,(N_n)}),\qquad v=\phi_{J_R,(r_UN_n)}\,J_R(\phi_{r_U,(N_n)})\,e_P.$$
Both have domain $AP$ and codomain $\prod_nBN_n$. For every projection $\pi_n$ the defining projection equations for $\phi$ give $\pi_nu=e_{N_n}A(\pi_n)$ and $\pi_nv=B(\pi_n)e_P$. These are equal by naturality of $e$ from Step 1, so $u=v$ by the product universal property. This is a calculation with the canonical maps of [lem-cbc-exact-product-functor-strict-limit], rather than a choice of a product isomorphism.

Cited nodes: lem-cbc-exact-product-functor-strict-limit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md; Final paragraph: apply the exact product-preserving functor to defining derived limits; explicit product projection calculation.

### Returned Step 6 → lem-cbc-normalized-limit-square-coherence

For a strict tower complex $M$, let $H_M^q=P_M^q\oplus P_M^{q-1}$ and $d(x,y)=(dx,(1-s)x-dy)$, as fixed in [lem-cbc-exact-product-functor-strict-limit]. Apply Step 5 separately to the families $(M_n^q)_n$ and $(M_n^{q-1})_n$. Naturality of $e$ for the two biproduct projections shows that $e_{H_M}$ is diagonal in these coordinates. Its naturality for the differentials and transitions shows that the resulting equality is an equality of chain maps, with the same minus sign on both sides. In notation
$$K_A=\kappa_{r_T,J_SM}\,r_T(\kappa_{J_S,M}),\qquad K_B=\kappa_{J_R,r_UM}\,J_R(\kappa_{r_U,M}),$$
the equality is
$$H(e_M)K_A=K_Be_{H_M}.$$
All maps are natural for strict tower chain maps. The cited normalized comparison provides their descent to the derived categories.

Cited nodes: lem-cbc-exact-product-functor-strict-limit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md; Final paragraph, canonical derived-limit comparison; explicit calculation on both signed Roos summands.

### Returned Step 7 → lem-cbc-normalized-limit-square-coherence

Let $\theta$ denote the normalized natural isomorphism $L\to H$ of [lem-cbc-exact-product-functor-strict-limit]; its normalization agrees with K-injective resolution, not just with an unspecified Roos triangle. Substitute $\lambda_{F,M}=\theta_{FM}^{-1}\kappa_{F,M}F(\theta_M)$ in the left-hand side of the required equation. The middle factors $r_T(\theta_{J_SM})$ and its inverse cancel. Naturality of the target $\theta$ for $e_M:AM\to BM$ then makes that side
$$\theta_{BM}^{-1}H(e_M)K_A A(\theta_M).$$
Substitute the same formula on the right-hand side and cancel $J_R(\theta_{r_UM})$ with its inverse. Naturality of the derived $e$ for $\theta_M:LM\to H_M$ gives $B(\theta_M)e_{LM}=e_{H_M}A(\theta_M)$, so the right-hand side is
$$\theta_{BM}^{-1}K_Be_{H_M}A(\theta_M).$$
Step 6 proves these expressions equal. The four functor occurrences and the target limit are exactly those in the statement. Naturality of $\lambda$ and $e$ makes the resulting equality natural for every derived strict-tower morphism, including morphisms represented by roofs.

Cited nodes: lem-cbc-exact-product-functor-strict-limit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md; Final paragraph applying the exact-functor/derived-limit comparison; agent-written expansion of its specified normalized formula.

### Returned Step 8 → lem-cbc-normalized-limit-square-coherence

For a strict augmentation $\gamma:\Delta C\to M$, [lem-cbc-exact-product-functor-strict-limit] states that $\lambda_F\,F(u_\gamma)=u_{F\gamma}$. In the signed coordinates this is the equality sending $c$ to $((F\gamma_n)(c),0)$, since $\phi_F$ is characterized by its projections. Apply this assertion successively along $J_S,r_T$ and along $r_U,J_R$. Naturality of $e$ at $\gamma_n$ identifies the resulting augmentations: $e_{M_n}A(\gamma_n)=B(\gamma_n)e_C$. Step 7 therefore identifies their canonical derived maps after either composite. A quotient-tower completion unit is the map of its strict quotient augmentation, so it is included. In particular exactness preserves the quotient maps used in such an augmentation. The argument used neither preservation of K-injectives by scalar restriction nor tensoring along $a$; no flatness or boundedness is needed.

Cited nodes: lem-cbc-exact-product-functor-strict-limit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md; Final paragraph applying the comparison to defining derived limits; augmentation clause of the normalized strict-limit comparison.

## Unfinished work

The two new nodes are deliberately statement-only parallel proof tasks, as requested by the return. Their arguments are assigned and preserved above. No Lean was written or compiled. The required remote checks and dry run precede the push; their final results are recorded below after execution.

## Verification results

Remote `srvcheck.py ... check_dag` exited successfully: no finding introduced by the sandbox or on its nodes. The required `deliver.py Q158 lem-cbc-ringed-open-scalar-limit-coherence --no-push` then exited successfully with `OK (not pushed)` at `6073602c8c8`: full server preflight passed, including the DAG/split, search-log, citation and duplicate checks. The returned statement remains byte-for-byte equal to the repository baseline; the two children remain statement-only and the assembly has 2062 characters. Direct delivery is authorized by the brief; the push reruns preflight with this report addition.
