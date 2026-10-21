# Stage-1 repair: lem-trf-integral-point-transport-tower-realization

1. Files written:
   - dag/nodes/sec-trace-formula/lem-trf-integral-point-transport-tower-realization.json: statement unchanged; split into three assembly steps.
   - dag/nodes/sec-trace-formula/lem-trf-point-transport-strict-quotient.json: statement, unsplit; no Mathlib match.
   - dag/nodes/sec-trace-formula/lem-trf-point-sections-completion-cone.json: statement, unsplit; no Mathlib match.
   - dag/nodes/sec-trace-formula/lem-trf-point-transport-cone-comparison-descent.json: statement, unsplit; no Mathlib match.
2. Attachments: none. The project-wide notion/tag search found the recorded Sheaf.Paper.IntegralPointTransportTowerRealization theorem, whose proof at line 204 is still `sorry`; the source search in WeilConjectures found no exact finished declaration. Existing helper definitions do not prove any new lemma. No Lean file was written or compiled.
3. WANTED: none. All sources needed for the retained route are present locally.
4. Fault repaired: the human returned the 6214-character proof for lack of distributed work. It is now assigned to three independent unsplit statement-only nodes; no new node is the whole theorem. The original statement, Lean binding and historical provenance fields are retained. The sandbox initially contained only dispatcher .brief files, no prior report, node files or search log, so the current read-clone item supplied the returned argument. The report below preserves every word of that argument. This is a substantive re-split, not an unchanged re-push.
5. Unfinished: the three new proofs are deliberately left to future parallel workers, as the return requires. Each new JSON has empty proof and proof_deps, null proof_origin, and status unsplit. The parent proof is complete relative to these statements.

## Distribution of the retained argument

The strict-quotient lemma owns old steps 1-2 and the quotient-map naturality and localization of the tower map from old step 6. Its output includes both strict identities, including the augmentation identity; it does not use completeness or identify the integral transport.

The sections/completion lemma owns old steps 3-4 and the descent/naturality of alpha and beta from old step 6. It states the product-diagonal cone functor, its specified sectionwise comparison, the normalized source unit and the completed-pullback target comparison. It does not mention a transport map or assert their realization equality.

The cone-comparison/descent lemma owns old step 5 and the cancellation/naturality/roof argument for the specified integral map from old step 6. Its strict tower and augmentation identity are hypotheses, not a re-construction of the first lemma. It proves a chain-level comparison and its localization for arbitrary integral inputs; it does not require completeness and does not prove that alpha is an isomorphism. This leaves three separate tasks of comparable scope. They have no dependencies on one another, so workers can begin them independently.

The parent combines these outputs on one K-flat resolution, identifies the two already-specified source/target comparisons, and cancels Gamma(q). Its proof text is 1801 characters, below 3000; no step exceeds 2000. There are three new nodes, not a renamed replacement for the parent.

## Original argument retained verbatim

The following paragraphs are the previous proof, retained as a handoff to the workers. They are not proof steps in the new statement-only JSON files. Ownership refers to the three tasks above.

### Original step 1 — strict quotient

Write $R=\widehat{\mathcal O}_{E,s}$ and $g=g_s$. Choose one flat-term K-flat resolution $q:P\to N$ by [lem-pc-kflat-resolution]. Put $P_n=P\otimes_R(A_n)_s$, $r_n:P\to P_n$, $r_n(x)=x\otimes1$, and $t_n=1\otimes(A_{n+1}\to A_n)$. These strict quotient maps represent $\mathcal R(N)$ by [def-weil-pbc-adic-coefficient-datum]. Put $C_n=\operatorname{Res}_n g_n^*P_n$, with the strict coefficient-induced transition $v_n:C_{n+1}\to C_n$ of [def-weil-inverse-image-pullback-comparison](b). At finite level $g_n^*P_n$ represents $Lg_n^*N_n$ by part (a) of that definition. Set $D_n=\Gamma(s,P_n)$, $B_n=\Gamma(s,C_n)$, and
$$u_n=\Gamma(s,\kappa_{P_n})\sigma_{P_n}:D_n\longrightarrow B_n.$$
The finite-level formula in [def-weil-frobenius-point-transport] says precisely that $[u_n]=\iota_{N_n}$. All towers and arrows here are complexes of $\mathcal O_E$-modules after restriction of scalars; no limit of categories with changing coefficient rings is being taken.

Cited statements: lem-pc-kflat-resolution, def-weil-pbc-adic-coefficient-datum, def-weil-inverse-image-pullback-comparison, def-weil-frobenius-point-transport.

### Original step 2 — strict quotient

The maps $u_n$ commute strictly with the transitions. Indeed restriction along $g$ commutes with every morphism of sheaves. The inverse-image colimit insertion and its sheafification are natural in the sheaf, so applying a quotient before or after the two operations defining $\sigma$ gives the same section. Finally the tensor insertion sends $x$ to $x\otimes1$, and reducing this section sends it to $\bar x\otimes1$ whether reduction precedes or follows insertion. Linearity across coefficients uses the projection square $\pi_n c_{\mathcal O_E}=c_{A_n}g^{-1}(\pi_n)$ in [def-weil-inverse-image-pullback-comparison]. Thus
$$\Gamma(s,v_n)u_{n+1}=u_n\Gamma(s,t_n).$$
The same section calculation with $r_n$ gives
$$\Gamma(s,\theta_n)\sigma_P=u_n\Gamma(s,r_n),\qquad
\theta_n=\kappa_{P_n}g^{-1}(r_n).$$
Consequently $u_\bullet:D_\bullet\to B_\bullet$ is a strict map of tower complexes before localization. In particular it supplies a morphism in the derived category of towers, with the required evaluations.

Cited statements: def-weil-frobenius-point-transport, def-weil-inverse-image-pullback-comparison, def-weil-pbc-adic-coefficient-datum.

### Original step 3 — sections/completion

Use $H(X_\bullet)=\operatorname{Cone}(1-s_X)[-1]$ with the convention in [lem-pur-integral-operations-well-defined]:
$$H(X)^i=(\prod_nX_n^{i-1})\oplus(\prod_nX_n^i),\qquad d(b,a)=(-db-(1-s_X)a,da).$$
The strict equality in step 2 implies $(1-s_B)\prod u_n=(\prod u_n)(1-s_D)$. Hence $H(u)(b,a)=((\prod u_n)b,(\prod u_n)a)$ is a chain map. Countable sheaf-module products are exact and sectionwise by [lem-weil-proetale-countable-products-exact]; exact products give the derived products by [lem-weil-derived-limit-existence](2). Thus these are derived-limit models. Sections at $s$ preserve quasi-isomorphisms by [lem-weil-point-proetale-sections-exact]. Moreover the sectionwise product equality and the displayed two-summand differential identify $\Gamma(s,H(X_\bullet))$ with $H(\Gamma(s,X_\bullet))$, including its arrows, by the identity on the two product components. This proves the required preservation here by an explicit model, without selecting a comparison between unspecified Roos triangles.

Cited statements: lem-pur-integral-operations-well-defined, lem-weil-proetale-countable-products-exact, lem-weil-derived-limit-existence, lem-weil-point-proetale-sections-exact.

### Original step 4 — sections/completion

Let $\chi_N:N\to H(P_\bullet)$ be the specified completion map of [lem-weil-finite-free-completed-scalar-comparison] for the identity extension $E=E$. Its representative on $P$ is $z\mapsto(0,(r_nz)_n)$, and it is an isomorphism, natural in $N$, since $N$ is derived complete. Applying exact sections and step 3 gives the canonical identification
$$\alpha_N:\Gamma(s,N)\xrightarrow{\sim}H(D_\bullet).$$
For the target, the definition of completed pullback in [def-weil-derived-pullback-tensor-hom] and its well-definedness [lem-pur-integral-operations-well-defined] compute $Lg^*N$ as $H(C_\bullet)$. Step 3 therefore gives
$$\beta_N:\Gamma(s,Lg^*N)\xrightarrow{\sim}H(B_\bullet).$$
Here $B_n$ represents exactly $\Gamma(s,Lg_n^*N_n)$ by step 1. These give the two identifications asserted in the statement. In particular the first identification uses the specified completion map, not an arbitrary isomorphism supplied by the existence of a distinguished triangle.

Cited statements: lem-weil-finite-free-completed-scalar-comparison, lem-weil-point-proetale-sections-exact, def-weil-derived-pullback-tensor-hom, lem-pur-integral-operations-well-defined.

### Original step 5 — cone comparison/descent

We compare the maps on $\Gamma(s,P)$, which maps quasi-isomorphically to $\Gamma(s,N)$ by [lem-weil-point-proetale-sections-exact]. By step 4,
$$H(u)\alpha_N\Gamma(s,q)(z)=(0,(u_n\Gamma(s,r_n)z)_n).$$
Part (b) of [def-weil-inverse-image-pullback-comparison] defines the integral $\kappa_N$ from the map $g^{-1}P\to H(C_\bullet)$ sending $w\mapsto(0,(\theta_nw)_n)$, followed by the inverse of $g^{-1}q$. The restriction and insertion formula for $\sigma$ in [def-weil-frobenius-point-transport] commutes with $q$, so $\sigma_N\Gamma(s,q)=\Gamma(s,g^{-1}q)\sigma_P$. The factor $g^{-1}q$ and its inverse cancel in $\iota_N=\Gamma(s,\kappa_N)\sigma_N$. Thus
$$\beta_N\iota_N\Gamma(s,q)(z)=(0,(\Gamma(s,\theta_n)\sigma_Pz)_n).$$
Step 2 equates these two expressions, including their zero shifted-product components. Inverting $\Gamma(s,q)$ gives
$$\beta_N\iota_N=H(u)\alpha_N.$$
This proves the equality with the specified integral transport as a derived morphism; the calculation does not infer equality from the individual reductions.

Cited statements: lem-weil-point-proetale-sections-exact, def-weil-inverse-image-pullback-comparison, def-weil-frobenius-point-transport.

### Original step 6 — all three: tower naturality / comparison naturality / specified-map roof descent

For a chain map $f:P\to P'$ of flat-term K-flat complexes, the quotient maps give a map of strict towers by [def-weil-pbc-adic-coefficient-datum]. Restriction, colimit insertion, sheafification and $x\mapsto x\otimes1$ commute with $f$, as their section formulas show. Hence $u'_{n}\Gamma(s,f_n)=\Gamma(s,g_n^*f_n)u_n$, and the product and two-component cone formulas in step 3 commute with $f$ too. The source comparison is natural and independent of the K-flat resolution by [lem-weil-finite-free-completed-scalar-comparison], while the target completed pullback has the same descent and independence by [lem-pur-integral-operations-well-defined]. Exact sections preserve their quasi-isomorphisms by [lem-weil-point-proetale-sections-exact]. The chain-map equalities therefore hold after localization: for a roof $P\xleftarrow{a}Q\xrightarrow{b}P'$ between K-flat representatives, they hold for $a,b$ and hence for $[b][a]^{-1}$. The resolving-class construction of the reduction functor in [def-weil-pbc-adic-coefficient-datum] computes derived morphisms this way. This proves naturality of the tower morphism, the identifications and the equality of step 5 for arbitrary derived morphisms, as well as independence of the common resolution.

Cited statements: def-weil-pbc-adic-coefficient-datum, lem-weil-finite-free-completed-scalar-comparison, lem-pur-integral-operations-well-defined, lem-weil-point-proetale-sections-exact.

## Not duplicates

lem-trf-point-transport-strict-quotient vs lem-trf-integral-point-transport-tower-realization: the new statement concerns raw quotient complexes, strict transition and augmentation identities and tower descent; it asserts no completion comparison or integral realization equality.
lem-trf-point-sections-completion-cone vs lem-trf-integral-point-transport-tower-realization: the new statement compares sections and cones and specifies alpha/beta without constructing or identifying any point transport.
lem-trf-point-transport-cone-comparison-descent vs lem-trf-integral-point-transport-tower-realization: the new statement assumes the strict transport/augmentation square and proves its specified cone identity and descent without completeness or invertibility of the source unit.
lem-trf-point-transport-strict-quotient vs lem-weil-frobenius-point-transport-natural: the existing theorem treats naturality at a fixed coefficient ring; the new statement needs strict cross-coefficient transitions and augmentation to a simultaneous quotient tower.
lem-trf-point-transport-strict-quotient vs lem-trf-integral-point-transport-tower-powers: the downstream powers theorem treats whole semilinear systems and powers; it does not state the strict augmentation identity Gamma(theta_n) sigma_P = u_n Gamma(r_n) for the common integral representative. It uses the present realization item, so routing the parent through it would also be circular.
lem-trf-point-sections-completion-cone vs lem-weil-strict-roos-comparison: the latter compares sheaf Roos realization with total derived limit, not the specified sectionwise map on both components together with the source completion unit and completed Frobenius pullback identifications.
lem-trf-point-sections-completion-cone vs lem-cbc-exact-functor-rlim: the latter explicitly asserts existence, not a canonical choice, of an object-level Roos-triangle comparison. The new statement fixes the chain comparison and both completion components.
lem-trf-point-sections-completion-cone vs lem-pe-roos-cone-calculus: the latter gives cone/shift calculus within sheaves, not point sections, specified completion alpha and completed-pullback beta or their representative independence.
lem-trf-point-sections-completion-cone vs lem-pod-point-completed-evaluation: the latter is a duality/evaluation identity on bounded finite-projective models. The new lemma concerns arbitrary derived-complete constructible inputs and their quotient/pullback cones.
lem-trf-point-sections-completion-cone vs lem-trf-point-sections-finite-reduction: finite derived reduction is not inverse-limit realization or normalized completeness; it has a different comparison map.
lem-trf-point-transport-cone-comparison-descent vs lem-weil-frobenius-point-transport-natural: the existing naturality theorem does not compare the specified integral cone map to the diagonal realization, including its zero shifted component.
lem-trf-point-transport-cone-comparison-descent vs lem-trf-integral-pullback-comparison-realization: the latter constructs pullback composition and scalar comparisons, not the point restriction/insertion map or its equality with the zero-homotopy integral comparison.

The whole DAG was searched by point transport, strict quotient, sections/Roos, point/completion and the proposed ids; candidate statements above were opened. Blueprint searches were run with blueprint_refs.py over the whole imported blueprint: point transport, Roos, strict quotient transport, sections Roos, point cone, quotient transport, sections completion, comparison descent. The three point-transport blueprint hits (local Frobenius trace, Karoubi independence, finite coefficient map) concern traces/scalar continuation, not these chain-level lemmas. The generic Roos and reduction hits above are not duplicates. The sole comparison-descent search hit is a torsor-comparison statement. The nearest ancestor is prop-trf-rational-frobenius-integral-model; new via lists begin with the present created item and all from.place fields identify clause (3). No new Stacks fact is introduced or attributed to a section number; these are refinements of the blueprint's specified-map route, not claims that a Stacks tag states a Frobenius normalization.

## Mathlib searches

Each new node has two differently phrased LeanFinder searches, a Loogle name-pattern search, a Mathlib grep, and a LeanSearch query, run through the authorized msearch.py and read from the saved results. All services answered on this run. The nodes record the exact tool/query strings, hit names, dates and no-match verdicts. Each also records a focused grep used to inspect a plausible candidate. The focused grep on a single file prints its line number as the file field (106/118 and 405); the actual source locations were checked directly, not treated as a match. The shared append-only searches.jsonl records all 18 runs. No query was invented or copied from another worker's log.

The strict transport candidates are ordinary pullback/sheafification presentations (PullbackContinuous.lean:106,118), fixed-coefficient restriction transformations, and adic module quotient functoriality. None contains the specified point formula, cross-coefficient augmentation and derived tower descent. For the completion lemma evaluationPreservesLimits (FunctorCategory/Basic.lean:405) is ordinary diagram evaluation, not exact point sections and the normalized derived completion map. Generic mappingCone.mapHomologicalComplexIso and mappingCocone.lift (MappingCocone.lean:282,296,302) give usable ingredients for the third lemma; the prescribed kappa, sigma and comparison-map descent still require the separate argument retained above. Hence there are zero Mathlib leaves.

## Review by Q91

I read the main-20261015 rational-Frobenius integral-model proof, clause (3) and its neighboring reduction discussion, the trace-formula chapter and sk-d-weil unit records, and the current Sheaf.Paper.IntegralPointTransportTowerRealization statement and six-step docstring. The new statements stay on that simultaneous finite-coefficient/strict-cone route. For the strict quotient lemma I checked the definitions of the adic coefficient datum, inverse-image/pullback comparison (a) and (b), and Frobenius point transport. They specify r_n, the actual coefficient-induced transitions, the structure-map projection square, restriction and insertion, and the finite formula. The existing point-transport naturality statement gives fixed-ring sigma linearity and chain naturality, not by itself the new cross-coefficient identity. The retained generator calculation is the separate argument assigned to the new lemma.

For the cone/completion lemma I read integral-operations well-definedness, pro-etale countable-products exactness, derived-limit existence (2), exact point sections, and finite-free completed scalar comparison. The product lemma says sectionwise AND exact, the derived-limit lemma supplies termwise derived products under exactness, and exact sections applies because k is algebraically closed. The completion theorem at E=L gives precisely the specified quotient-map component and zero shifted-product component and its natural invertibility for a derived-complete input. Completed pullback is the strict cone of the finite pullback quotient tower by the operation definition and its well-definedness theorem. These statements supply the hypotheses and comparisons required by old steps 3-4; the newly stated lemma owns their combined sectionwise identification, not an arbitrary triangulated comparison. I also read the K-flat and flat-module definitions to avoid replacing the completed coefficient sheaf by a constant coefficient ring.

For the cone-comparison/descent lemma I read comparison (b) in full: it specifies tilde-theta with zero shifted coordinate and kappa=[tilde-theta][g^{-1}q]^{-1}. Together with the section formula for sigma, this is exactly the representative whose equality old step 5 checks. The strict augmentation equality is an explicit hypothesis of this lemma, supplied by the first one. Applying the diagonal H(u) to the normalized source unit gives the same two components. Exact sections makes Gamma(q) invertible. The operation well-definedness theorem and the adic datum give descent and independence on the resolving class; applying natural chain identities to both legs of a roof yields the derived naturality. The report preserves that entire original roof argument; it has not been replaced by a bare assertion of equality of reductions.

Parent step 1 cites the K-flat resolution theorem, which supplies a quasi-isomorphism with flat K-flat source, and the strict quotient lemma, whose statement explicitly gives u, both strict equations, evaluations and natural descent. Parent step 2 cites the section/completion lemma: its statement explicitly gives H(u), the canonical alpha/beta, both normalization components and naturality. Parent step 3 cites the cone-comparison/descent lemma, whose statement contains the displayed b_q iota_N Gamma(q) identity and invertibility of Gamma(q). The alpha and beta used in step 3 are the same ones from step 2: alpha has zero shifted coordinate and r_n product coordinate, and beta is the identity sectionwise product comparison. Thus cancellation uses equality of specified maps; there is no C4 use of a proof-only construction. citations.json contains a verbatim statement quote for every parent step/node pair.

I checked B-E of delivery-errors: new nodes are self-contained propositions with no proof arrays/sketches, all symbols and coefficient actions are introduced, the parent statement is unchanged, no new nontrivial assertion is left outside a cited node, and the new lemmas have smaller and separate claims. No SGA route is used. The new dependencies do not point back to the item. The new statements introduce no finite Tor-amplitude assumption, do not impose termwise constructibility on P, and keep all levels after restriction in one integral module category. The only completeness hypothesis is where alpha must be invertible; the conditional map-identity lemma intentionally requires none.

For small cases I checked P=0, zero chain maps, the first level n=1, and identity coefficient changes. All maps then have the displayed zero/quotient components, v_n theta_{n+1}=theta_n remains meaningful at n=1, and the sectionwise cone differential is exactly (-db-(1-s)a,da). For a constant tower the shift endomorphism gives the same diagonal H(u); no equality is inferred only from projections. E=Q_l has the same projection square and identity-extension completion comparison. An incomplete input is allowed in the third lemma only as a map identity with a possibly noninvertible source unit, so that edge case does not falsely assert completeness. Naturality is for roofs between resolving-class representatives, not a claimed strict functor on chosen derived representatives. I found no statement dispute or source error. I corrected the coarseness by creating all three tasks, rather than shortening the argument in place.

## Validation

The required server review_split check and final deliver.py --no-push are run on this repaired sandbox. The first dry run requested a longer verbatim quote for parent step 3 (minimum 40 characters); I replaced the short formula substring with the complete displayed pair of equalities. The split itself was unchanged. The repaired dry run exited successfully: OK (not pushed), commit e5349044b74, preflight passed. This includes the server DAG and split checks. A final dry run follows this validation-note edit before the authorized direct push.
