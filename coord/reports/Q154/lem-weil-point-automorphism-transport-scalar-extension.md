# Q154 repair: lem-weil-point-automorphism-transport-scalar-extension

## Files written

- `dag/nodes/sec-six-functors/lem-weil-point-automorphism-transport-scalar-extension.json`: unchanged statement; four assembly steps, 2214 characters in total.
- `dag/nodes/sec-six-functors/lem-weil-point-restriction-ordinary-tensor-square.json`: statement, unsplit; no Mathlib match. The unbounded ordinary sections/restriction square, its K-flat normalization and coefficient formula.
- `dag/nodes/sec-six-functors/lem-weil-point-inverse-image-coefficient-tower.json`: statement, unsplit; no Mathlib match. Ordinary b coherence, completion-conjugated beta coherence and the induced psi coherence.
- `dag/nodes/sec-six-functors/lem-weil-point-scalar-compatible-transport-transfer.json`: statement, unsplit; no Mathlib match. Conditional transfer through a scalar-compatible family into an arbitrary target functor, its sections towers and fraction-field rationalization.
- `citations.json`: verbatim statement quotations for all 11 step/node citations.
- `report.md`: this report, including the complete returned proof below. The sandbox also retains `returned-proof.json`, the previous report as `prior-report-Q92.md`, and the genuine `searches.jsonl` log.

There are 3 new unsplit nodes and 0 Mathlib leaves. Every new node has empty proof and proof_deps, proof_origin null, its own self-contained hypotheses, source place, blueprint ancestry, creation data and actual searches. No Lean file was written and no compiler, Lake or build command was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, point_automorphism, pointTransport and restriction/tensor concepts. I read `SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/StrictWeilComplex.lean`: it extends strict Weil data with finite coefficient rings and does not state these completed-coefficient sections squares. The recorded `lean/Sheaf/Paper/PointAutomorphismTransportScalarExtension.lean` is a statement file: the main theorem at line 299 ends in sorry at line 320, with the unit and tower theorems also sorried. Its docstring records precisely the seven arguments being repaired. Helpers that select a pinned restriction transformation or name a composite do not prove the item or any new statement.

## WANTED

None. The source context and all supporting statements used here are available.

## Return repaired

The sole return is the human's 2026-10-21 decision, applied 2026-10-22, requiring the 8143-character proof to be spread into at least two comparable independent statement-only nodes and a parent assembly of at most 3000 characters. I created three new nodes, with statements of 2597, 3100 and 3689 characters respectively (lengths include their independently repeated setup). Their arguments have comparable substance: the chain/derived restriction square, the ordinary/completed comparison tower calculation, and comparison transfer plus rationalization. None assumes the item itself. All three are cited by parent proof steps; their proof lists remain empty for future parallel workers. The parent assembly is 2214 characters. I have not removed arguments to meet the bound: the earlier proof is reproduced verbatim below, with this assignment of responsibilities.

| Returned argument | New work item / assembly |
| --- | --- |
| 1: admissibility, chi and phi, ordinary termwise descent | The ordinary-square node states the unbounded representative/descent result with its exact existing inputs; the parent checks constructible endpoints before using completion. |
| 2: flat-term K-flat resolution, evaluation at U,V, coefficient c inverse, pure-tensor equality, localization | Ordinary-square node, including both the representative value and derived equality. |
| 3: naturality of sigma at chi and cancellation of the specified beta | Parent Step 2 is the short assembly of the ordinary-square node with the already existing naturality and beta-definition nodes. The full cancellation is retained verbatim below. |
| 4: specified kappa square and naturality of phi at kappa | Transport-transfer node, for arbitrary scalar-compatible u:G to J; specialize J=P, u=kappa, delta=alpha. |
| 5: ordinary b unit/tower, iterated local tensors and derived representative | Inverse-image coefficient-tower node, first assertion and representative formula. |
| 6: conjugate b by chi, move chi past b, cancel, obtain beta and psi towers | Inverse-image coefficient-tower node, second and third assertions. |
| 6: alpha tower, naturality of phi at alpha, psi-prime tower and unit | Transport-transfer node, zeta tower; zeta specializes to psi-prime. |
| 7: exact rationalization, specified fraction formula, raw categories and mixed towers | Transport-transfer node, rational square and compatibility clauses. |

The previous sandbox contained only dispatcher marker files: there was no retained node, report or search log to dry-run first. I copied the live item and retained the Q92 report from the repository before editing. The live item's seven steps and the return's lengths agree exactly. The parent statement, source, import and Lean metadata, creation record, ancestry and old search history are retained. Delivery rebases the owned split fields on the current server head; no repository git command was run here.

## Statement and source audit

No statement correction is made in this repair. The previous Q92 repair already corrected the explanatory direction of phi to `(Gamma(chi) theta)^(-1)`; I retain that formula exactly. The original explanatory phrase and its type problem remain documented in the retained Q92 report.

For the item and all three extracted nodes I read the current blueprint source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`. Its ordinary and compact-support composites specify the first transport arrows this calculation supports. I read the chapter and unit records, keeping the inherited chapter/unit and route; this repair changes no unit or chapter. I read Deligne, Weil II (1.1.3), printed p.150, and (1.1.7), pp.150-151, using PDF pages 15-16. They give raw coefficient rationalization and point transport by structure, not a theorem on completed pro-etale comparison maps. The new sources explicitly identify these arguments as agent-written extractions of the returned proof. No SGA source is used.

For the tensor construction I also read Stacks Tag 03EK, `sites-modules.tex`, `section-tensor-product`, including its formulas for presheaf tensors, sheafification, associativity and change of rings. This supplies background for the existing definition node `def-pur-sheaf-tensor-product`; I do not attribute the new completed comparison assertions to this tag. All local tensor formulas are conclusions about sheafified generator images, not arbitrary sectionwise tensor identifications.

## Searches and reuse

Before making the new nodes I searched the whole DAG by restriction/tensor, inverse-image scalar, completed conjugation/coherence, point comparison and rational transport concepts, inspected the candidate statements, and searched the whole imported blueprint using `tools/blueprint_refs.py search` with `restriction tensor`, `inverse image scalar`, `transport comparison`, `rationalization`, `tensor comparison`, `scalar associator`, and `point automorphism`. The broad rationalization/tensor searches return framework definitions and unrelated projection/monoidal results, none of which states the three extracted arguments. `tools/blueprint_refs.py ancestor` returns `def-weil-global-geometric-frobenius`. New nodes have that ancestor and the item's complete via chain with the item prepended, and precise first-transport-arrow/returned-step places; same_as is empty.

Each new node has its own actual LeanFinder natural-language query, LeanSearch query, Loogle query and Mathlib grep; a second LeanFinder formulation was tried for each. All 17 commands answered successfully and are recorded verbatim in `searches.jsonl` and the node records. There was no earlier Q154 log to reuse. The item's inherited Q97/Q92 search records and results were read and preserved without repeating the unchanged whole-item question.

I read the most relevant returned Mathlib source:

- `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:45` and its tensorObj_map_tmul lemma at line 79: the tensor restriction construction and generator formula, without the ringed-site inverse-image comparison or derived descent square.
- `Mathlib/CategoryTheory/Sites/GlobalSections.lean:160` and line 168: GammaRes_map and GammaRes_naturality, without coefficient extension or completed coefficient actions.
- `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:1015`: ModuleCat.extendScalars_assoc, an ordinary module scalar functor associator, without b, chi, beta or psi on pro-etale sheaves.
- `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:177` and the following pullback_assoc: conjugateEquiv_pullbackComp_inv and composition of site pullback adjoints, without the ordinary-to-completed coefficient conjugation square.
- `Mathlib/CategoryTheory/Functor/Category.lean:97`: NatTrans.naturality_inv, one algebraic ingredient of the transfer calculation, without its scalar-compatible family, sections tower or fraction-field comparison.

The other semantic hits include structure-sheaf restriction, localization module tensors, dense-site equivalences and right-derived comparison transformations. Their types do not give these assertions or a one-line specialization of them. Accordingly all three new nodes stay unsplit, not Mathlib leaves. Each stored verdict distinguishes the relevant ingredient from the full searched assertion.

## Not duplicates

lem-weil-point-restriction-ordinary-tensor-square vs lem-weil-point-finite-free-sections-tensor: the existing node constructs theta and its basis formula; the new node identifies its restriction square with the specified b and sigma on all unbounded derived objects.

lem-weil-point-restriction-ordinary-tensor-square vs lem-weil-point-derived-sections-tensor-descent: the existing node localizes theta and permits K-flat representative calculations; it has no point-automorphism sigma/b square.

lem-weil-point-restriction-ordinary-tensor-square vs lem-weil-point-automorphism-restriction-natural: naturality of sigma is for a derived morphism at fixed coefficients; the new square compares two coefficient categories and the inverse-image tensor b.

lem-weil-point-restriction-ordinary-tensor-square vs lem-weil-isomorphism-scalar-tensor-kflat-model: the existing node fixes b's local formula and models; it does not identify sections restriction and theta.

lem-weil-point-inverse-image-coefficient-tower vs lem-weil-point-derived-tensor-tower-coherence: ordinary tensor and theta associators are existing inputs; the new conclusion is coherence of b, its chi conjugate beta, and psi, with no sigma transport conclusion.

lem-weil-point-inverse-image-coefficient-tower vs lem-weil-isomorphism-comparison-scalar-extension: that node states the specified kappa square and defines beta; the new node proves its coefficient tower and the induced sections tower.

lem-weil-point-inverse-image-coefficient-tower vs lem-fd-completion-inverse-scalar-coherence: that node compares framework and PBC coefficient extension through the identity functor; the new node compares inverse image G with scalar extension and the sections psi.

lem-weil-point-inverse-image-coefficient-tower vs lem-sfb-coherent-hom-transition-laws: that node assumes coherent functors and proves transitions on common-stage Hom sets; it does not establish b/beta/psi coherence.

lem-weil-point-inverse-image-coefficient-tower vs lem-sp-scalar-associator-conjugate: that node identifies the right-adjoint conjugate of an ordinary scalar associator; it contains no completed inverse-image/sections comparisons.

lem-weil-point-scalar-compatible-transport-transfer vs lem-weil-point-automorphism-transport-scalar-extension: the new node assumes the inverse-image square and a scalar-compatible arbitrary family u:G to J; it proves transfer and its target sections/rational coherence. It neither establishes that assumed square nor constructs/proves coherence of b or beta, and the item follows only after the independent ordinary/completed arguments and the existing specified kappa square.

lem-weil-point-scalar-compatible-transport-transfer vs lem-weil-coefficient-complex-rationalization: the existing node supplies rho, exactness and mixed module associators; the new result concerns transfer of sections transport through a family u and its zeta comparisons, then rho's effect on those squares.

lem-weil-point-scalar-compatible-transport-transfer vs lem-weil-point-sections-scalar-extension: the existing node gives phi and its towers; the new one relates a second functor J and arbitrary scalar-compatible morphisms u to those phi maps.

lem-weil-point-scalar-compatible-transport-transfer vs lem-fd-local-frobenius-coefficient-extension: the latter concerns Weil pairs and local return operators on a finite-type scheme and depends on point transport upstream; it does not provide the conditional integral comparison-transfer argument here.

lem-weil-point-restriction-ordinary-tensor-square vs lem-sc-scalar-sections-iso-transport: the latter is k-linear structure-sheaf pullback on Zariski opens of a scheme isomorphism; it is not the completed-coefficient pro-etale scalar restriction square.

## Review by Q154

I checked the sole return against the actual node files: three independent work items are added, not merely a shorter description of the old proof. Their statements include the precise equations and representative normalizations assigned in the table above. No new node restates the entire item. The parent now performs only admissibility, completion conjugation and specializations. The complete old argument follows this review so the later workers have every generator calculation, cancellation and rationalization computation available; new node files themselves contain no proof sketch.

For new node A, I read the existing statements of `lem-pc-kflat-resolution`, `lem-weil-isomorphism-scalar-tensor-kflat-model`, `lem-weil-point-finite-free-sections-tensor`, `lem-weil-point-derived-sections-tensor-descent` and `lem-weil-point-automorphism-restriction-natural`, together with the sheaf tensor definition. The resolution theorem actually gives flat terms and K-flatness. The tensor-model statement actually gives G_EP K-flat, the local formula for b and identification of its derived class; the descent node explicitly covers unbounded objects and arbitrary roofs. The restriction-natural node actually identifies the coprojection with evaluation at V, fixes sigma on constant coefficients by c inverse, and states derived naturality without constructibility. Thus the representative and derived clauses of A require no bounded-flat-model assumption. In the draft I corrected the shorthand `(G_F P)(U)=P(V)` to `(G_E P)(U) isomorphic to P(V)`, so both the coefficient and the evaluation identification have the right type.

For new node B, I read the ordinary tensor-tower node's precise statement: it supplies the pure-tensor associator on flat-term K-flat models and independence under derived roofs. The tensor-model node supplies b at the intermediate ordinary extension as well as naturality on the entire unbounded derived category. The finite-free completion node gives natural invertible chi on derived-complete objects; the sections scalar-extension node explicitly defines A by conjugating ordinary associativity by chi and gives its module sections equation. This justifies the two stages in B without identifying completed and ordinary associators by an unspecified choice. The beta and psi equations include beta at T_{L/E}H and the right occurrence of G_M A_H. No sigma square or conclusion about t is assumed or proved by B. The old step 6 instruction to move C_{M/L}G_L(chi) past b before cancelling is retained in full below, including its citation for b's naturality.

For new node C, I checked the domains of every displayed map. J_F maps the complete constructible category to itself, so phi can be applied at J_F H and to the morphism u^F_H:G_F H to J_F H. Delta is natural with the explicit A tower equation; u is only a scalar-compatible family, with no unneeded naturality hypothesis. The hypothesis on the sigma square is precisely the parent Step 2 conclusion for all H. The transfer conclusion is obtained by applying sections to delta T(u)=u beta and using phi's naturality at u; the target coherence uses naturality at delta and the stated delta tower. The rational square uses the exact rho from the coefficient-complex rationalization node: that statement includes arbitrary derived morphisms, fraction-valued coefficients, exactness, the unit equation and the mixed integral/field tower. These are sufficient for C's raw rationalized conclusion. I have stated the latter conditional on the integral square and the supplied data, and have not assumed naturality of t to manufacture it.

I read every node cited by every parent step and copied the actual used statements into citations.json. Step 1 uses the isomorphism-derived-pullback statement's explicit constructibility/completeness assertion for G_E K and P_E K, the finite-free chi isomorphism, the exact formula phi=(Gamma(chi)theta)^(-1), and A's ordinary square. Step 2 uses restriction-natural for the actual derived morphism chi_K, including its unrestricted source, and the specified beta formula from isomorphism-comparison-scalar-extension. Multiplication by the invertible eta and beta maps is elementary and gives the displayed first equation in the right direction. Step 3 uses C with J=P, u=kappa, delta=alpha. The existing comparison theorem's statement is exactly alpha T(kappa_E)=kappa_L beta. The integral-operations scalar-extension statement supplies canonical alpha and its identity/successive-extension compatibility. Its composition maps are the tensor/completion comparisons already specified in the item, with A fixed by chi as in the old reviewed proof. Step 4 uses precisely the beta/psi equations of B and the zeta/rational compatibility clauses of C. Thus every non-elementary claim in the parent is either a cited statement or the explicit conclusion of an earlier step. No citation takes a fact from a dependency's proof instead of its statement.

I tested A on H=0, g=id, E=L, and a complex with torsion cohomology, and on an unbounded representative: the statement allows all of these. I tested B on repeated fields E=L or L=M, on zero H, and on a ramified tower: the tensor products multiply the actual coefficient factors and never identify uniformizers or assume unramified extensions. I tested C with J=G, u=id, delta=beta, where it reduces to its assumed square; with u=0, where both transport equations are zero; and with J=P, u=kappa, the application needed here. For torsion module complexes their rationalizations vanish, and fractions multiply by the rho formula independent of their representatives. No node requires g to be over k_0, finite Tor amplitude, a bounded flat representative, or termwise commutation of sections with arbitrary inverse limits.

The extracted arguments follow the existing route of the first Frobenius transport arrows; no geometric/purity route is replaced. The parent retains declarations of its existing generic tool uses for constructible admissibility, finite-free completion, point sections and the canonical alpha. All new nodes inherit the same chapter/unit. The whole DAG and blueprint searches, candidate statement readings, and genuine Mathlib searches were completed before the corresponding new files were written. I checked B1-B9, C1-C6, D1-D5 and E against the files: empty new proofs, self-contained setups, exact maps and directions, no copied false conclusion, and no cycle through the parent. Every parent step is under 2000 characters; no long proof step conceals an additional argument. Parent statement equality against live is checked locally before delivery; the required full server dry run and push follow.

## What remains

This is a one-level stage-1 repair. The three new unsplit nodes deliberately remain work for future workers. No missing part of the parent's assembly is left undocumented. The full server dry run determines whether the delivery is ready to push; the final response records the push result.

## Returned proof retained verbatim

The following seven steps are the pre-repair live proof, including the maintainer's fixes. They are research material for the three statement-only nodes and the short assembly; they are not additional proof steps stored on those nodes.

### Returned step 1

The hypotheses make $G_EK$ and $P_EK$ bounded constructible and derived complete by [lem-weil-isomorphism-derived-pullback]. Thus the completion isomorphisms of [lem-weil-finite-free-completed-scalar-comparison] and the natural sections comparisons of [lem-weil-point-sections-scalar-extension] apply to each of $K,G_EK,P_EK$. Use $\theta_H$ for the ordinary derived sections-tensor map. By [lem-weil-point-derived-sections-tensor-descent], ordinary coefficient extension and sections preserve quasi-isomorphisms, ordinary tensor on representatives computes $C$, and $\theta$ is defined by the termwise sections map even on nonconstructible complexes. In particular no bounded flat representative is needed. Put $\eta_H=\Gamma(s,\chi_H)\theta_H=\varphi_H^{-1}$ for the three complete objects above.

Uses: lem-weil-isomorphism-derived-pullback, lem-weil-finite-free-completed-scalar-comparison, lem-weil-point-sections-scalar-extension, lem-weil-point-derived-sections-tensor-descent.

### Returned step 2

First compare ordinary tensors, before completion. Choose a flat-term K-flat resolution $P\to K$ by [lem-pc-kflat-resolution], and do the following termwise calculation on $P$. Put $U=(s,\mathrm{id})$ and $V=(s,g)$. Under the evaluation identification in [lem-weil-point-automorphism-restriction-natural], $\sigma^g$ is restriction from $U$ to $V$. In each degree test the maps from $\Gamma(s,P)\otimes_{\mathcal O_E}\mathcal O_L$ on $x\otimes a$. By [lem-weil-point-finite-free-sections-tensor], $\theta_P$ sends it to the sheafification image of $x\otimes a_s$. The tensor restriction formula in [def-pur-sheaf-tensor-product] sends this to the image of $x|_V\otimes a_s|_V$. The other route first gives $\sigma^{g,E}_P(x)\otimes a$; the local formula for $b$ in [lem-weil-isomorphism-scalar-tensor-kflat-model] gives precisely the same section under evaluation at $V$. Here the constant coefficient is unchanged: [lem-weil-point-automorphism-restriction-natural] gives $\sigma^g_{R_L}(a_s)=c_L^{-1}(a_s)$, exactly the transported action used by $b$. Pure tensors generate the source module, so the maps agree, degree by degree, and commute with differentials. The tensor-model lemma makes $G_EP$ K-flat and identifies $b_P$ with $b_K$ after localization. Naturality of $\sigma$ for $P\to K$ and the exact descent of [lem-weil-point-derived-sections-tensor-descent] and the representative identification of $b$ in the tensor-model lemma give
$$\Gamma(s,b_K)\theta_{G_EK}(\sigma^{g,E}_K\otimes1)=\sigma^{g,L}_{CK}\theta_K.$$
This uses images of presheaf pure tensors only, and does not assume that arbitrary sheaf tensor sections are sectionwise tensors.

Uses: lem-weil-point-automorphism-restriction-natural, lem-weil-point-finite-free-sections-tensor, def-pur-sheaf-tensor-product, lem-weil-isomorphism-scalar-tensor-kflat-model, lem-weil-point-derived-sections-tensor-descent, lem-pc-kflat-resolution.

### Returned step 3

Apply the derived naturality assertion of [lem-weil-point-automorphism-restriction-natural] at coefficient field $L$ to $\chi_K:CK\to TK$. It gives
$$\Gamma(s,G_L\chi_K)\sigma^{g,L}_{CK}=\sigma^{g,L}_{TK}\Gamma(s,\chi_K).$$
Its domain is allowed: that assertion applies to every derived morphism, without constructibility assumptions. By the specified definition of $\beta$ in [lem-weil-isomorphism-comparison-scalar-extension], Step 2 therefore implies
$$\begin{aligned}
\Gamma(s,\beta_K)\eta_{G_EK}(\sigma^{g,E}_K\otimes1)
&=\Gamma(s,G_L\chi_K)\Gamma(s,b_K)\theta_{G_EK}(\sigma^{g,E}_K\otimes1)\\
&=\sigma^{g,L}_{TK}\Gamma(s,\chi_K)\theta_K
=\sigma^{g,L}_{TK}\eta_K.
\end{aligned}$$
Cancel the invertible maps and use $\eta_H^{-1}=\varphi_H$ from [lem-weil-point-sections-scalar-extension]. This gives exactly $\varphi_{G_EK}\Gamma(s,\beta_K)^{-1}\sigma^{g,L}_{TK}=(\sigma^{g,E}_K\otimes1)\varphi_K$, the first asserted equation.

Uses: lem-weil-point-automorphism-restriction-natural, lem-weil-isomorphism-comparison-scalar-extension, lem-weil-point-sections-scalar-extension.

### Returned step 4

The specified-comparison equation of [lem-weil-isomorphism-comparison-scalar-extension] is $\alpha_K T(\kappa^{E}_K)=\kappa^{L}_{TK}\beta_K$. Since $\alpha_K$ and $\beta_K$ are invertible, applying sections gives
$$\Gamma(s,\alpha_K)^{-1}\Gamma(s,\kappa^{L}_{TK})=\Gamma(s,T(\kappa^{E}_K))\Gamma(s,\beta_K)^{-1}.$$
The map $\kappa^E_K:G_EK\to P_EK$ is the derived morphism specified by [def-weil-inverse-image-pullback-comparison]; both endpoints satisfy the hypotheses from Step 1. Naturality of $\varphi$ in [lem-weil-point-sections-scalar-extension], applied to this morphism, now gives
$$\begin{aligned}
\varphi_{P_EK}\Gamma(s,\alpha_K)^{-1}t^L_{TK}
&=(\Gamma(s,\kappa^E_K)\otimes1)\varphi_{G_EK}\Gamma(s,\beta_K)^{-1}\sigma^{g,L}_{TK}\\
&=(\Gamma(s,\kappa^E_K)\otimes1)(\sigma^{g,E}_K\otimes1)\varphi_K
=(t^E_K\otimes1)\varphi_K.
\end{aligned}$$
The middle equality is Step 3. Naturality of $t$ is not used.

Uses: lem-weil-isomorphism-comparison-scalar-extension, def-weil-inverse-image-pullback-comparison, lem-weil-point-sections-scalar-extension.

### Returned step 5

For identity and successive extensions, first check the ordinary $b$ maps. Write $C_{L/E}$ for ordinary derived change of coefficients and $a^C$ for its associator. For $E\subset L\subset M$ the local formula of [lem-weil-isomorphism-scalar-tensor-kflat-model] and the pure-tensor associator of [lem-weil-point-derived-tensor-tower-coherence] give
$$b_{M/E,K}a^C_{G_EK}=G_M(a^C_K)b_{M/L,C_{L/E}K}C_{M/L}(b_{L/E,K}).$$
On a flat-term K-flat model as in Step 2, both routes on the local tensor $((y\otimes a)\otimes b)$ with $y=g^{-1}x$, $a=c_L(g^{-1}a_0)$, $b=c_M(g^{-1}b_0)$, give $g^{-1}(x\otimes a_0b_0)$. Tensor bilinearity and sheafification extend this equality to all sections; the tensor-model lemma identifies these representatives with the derived maps. For $L=E$ the same formula reduces to multiplication, giving the unit equation. There is no completed-tower comparison hidden in this calculation.

Uses: lem-weil-isomorphism-scalar-tensor-kflat-model, lem-weil-point-derived-tensor-tower-coherence, def-pur-sheaf-tensor-product.

### Returned step 6

Let $A_H:T_{M/L}T_{L/E}H\to T_{M/E}H$ be the integral associator specified in [lem-weil-point-sections-scalar-extension], namely the ordinary associator conjugated by $\chi$. Substitute $\beta=G(\chi)b\chi_G^{-1}$ from [lem-weil-isomorphism-comparison-scalar-extension] into Step 5. Naturality and invertibility of $\chi$ from [lem-weil-finite-free-completed-scalar-comparison] cancel the adjacent $\chi^{-1}\chi$ factors, after moving $C_{M/L}G_L(\chi_{L/E,K})$ past $b_{M/L}$ by the naturality of $b$ in [lem-weil-isomorphism-scalar-tensor-kflat-model], and give
$$\beta_{M/E,K}A_{G_EK}=G_M(A_K)\beta_{M/L,T_{L/E}K}T_{M/L}(\beta_{L/E,K}).$$
The same cancellation gives the unit equation. Using this equation and the naturality and associator equation for $\varphi$ in [lem-weil-point-sections-scalar-extension] in the formula $\psi=\varphi_G\Gamma(\beta)^{-1}$ gives
$$\psi_{M/E,K}\Gamma(s,G_M A_K)=a^{\mathrm{mod}}(\psi_{L/E,K}\otimes1)\psi_{M/L,T_{L/E}K}.$$
In this substitution naturality of $\varphi_{M/L}$ is applied to $\beta_{L/E,K}$; thus the middle $T_{M/L}(\beta_{L/E,K})$ cancels as well. This proves the identity and successive-extension compatibility of the first equation. For the second equation, run the same computation with $\alpha$ in place of $\beta$: put $\psi'_K=\varphi_{P_EK}\Gamma(s,\alpha_K)^{-1}$. The composition compatibility of $\alpha$ in [lem-pur-integral-operations-scalar-extension], for the integral associator $A$ above, reads $\alpha_{M/E,K}A_{P_EK}=P_M(A_K)\alpha_{M/L,T_{L/E}K}T_{M/L}(\alpha_{L/E,K})$; with the associator equation of $\varphi$ and naturality of $\varphi_{M/L}$ applied to $\alpha_{L/E,K}$ (Step 1), it gives $\psi'_{M/E,K}\Gamma(s,P_MA_K)=a^{\mathrm{mod}}(\psi'_{L/E,K}\otimes1)\psi'_{M/L,T_{L/E}K}$, and $\psi'=\mathrm{id}$ for $L=E$ by the identity clauses of $\alpha$ and $\varphi$. This is the compatibility of the second equation, whose left side is $\psi'_Kt^L_{TK}$. Module associators: $((x\otimes a)\otimes b)\mapsto x\otimes ab$.

Uses: lem-weil-point-sections-scalar-extension, lem-weil-isomorphism-comparison-scalar-extension, lem-weil-finite-free-completed-scalar-comparison, lem-pur-integral-operations-scalar-extension, lem-weil-isomorphism-scalar-tensor-kflat-model.

### Returned step 7

Apply the functor $-\otimes_{\mathcal O_L}L$ to Step 4. The exactness and derived naturality in [lem-weil-coefficient-complex-rationalization] identify each extended source or target by the specified map $((n\otimes a)\otimes b)\mapsto(n\otimes1)\otimes ab$. Hence the right side becomes $(t^{E,\mathrm{rat}}_K\otimes_E1_L)$ composed with the rational sections comparison of [lem-weil-point-sections-scalar-extension], and the left side uses the rationalization of the same $\alpha_K$. These are the raw rationalized functors of [def-weil-rationalization-karoubi], which keep the integral objects and tensor their morphisms with the fraction field. This is the requested rational equation. The unit and mixed integral/field tower equation of the rationalization lemma carry the identity and successive-extension equations of Step 6 to the rational ones, including fractions; no idempotent completion or new choice of comparison is involved.

Uses: lem-weil-coefficient-complex-rationalization, lem-weil-point-sections-scalar-extension, def-weil-rationalization-karoubi.
