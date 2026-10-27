# Stage-1 repair: lem-sfb-continuous-algcl-proper-scalar-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-proper-scalar-comparison.json`: statement unchanged; five-step assembly, 2803 characters of proof text, preserving coefficient factorization, explicit inverse construction and the exact coefficient cocycle.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-algcl-comparison-domains.json`: new statement, status unsplit, no Mathlib match. Intermediate finite-subextension comparison and all-continuous constructible/finite-Tor endpoint domains; returned steps 2--3.
- `dag/nodes/sec-six-functors-basics/lem-sfb-algcl-topology-mate-hom-bijection.json`: new statement, status unsplit, no Mathlib match. Identifies the actual normalized counit mate's Hom action as the chain of bijections, for arbitrary f with constructible C-pushforward; returned step 4.
- `citations.json`: one verbatim full statement per parent-step citation. `searches.jsonl` is the actual msearch log. Local work scripts and the baseline node are under `work/` and are not delivered as project files.

Two new nodes, zero Mathlib leaves. New nodes have no proof steps or proof dependencies. No Lean written, no compiler or Lake run; no repository or launcher edits or direct git commands.

## Attachments

None. Exact-tag and notion searches under live `lean/WeilConjectures/` found no closed declaration giving the assigned theorem or the proposed new lemmas. The live `lean/Sheaf/Paper/ContinuousAlgClProperScalarComparison.lean` states the assigned assertion, but its theorem at line 92 has `sorry`; its docstring retains exactly the six arguments being redistributed. FiniteCoefficient/Derived/ExtendScalars/LowerStar concerns finite discrete coefficient rings, not these condensed coefficient topologies.

## WANTED

WANTED: an exact proof/reference for the already existing `lem-sfb-constructible-algcl-topology-comparison`, the equivalence of ordinary bounded constructible internal-module derived categories for finite-subextension-valued versus ALL norm-continuous algebraic-closure coefficients. Its current statement and source explicitly retain this obligation; this repair does not claim that it is proved or identify the rings. Both new nodes are agent-extracted obligations from the returned proof and cite its actual blueprint place, not an invented Stacks theorem. The existing missing topology reference remains inherited work, not a reason to erase the original argument.

## What was wrong and what was repaired

The single return requires spreading the 4493-character proof into at least two independently claimable nodes of comparable size, delivered unsplit, with a parent assembly of at most 3000 characters. The sandbox initially contained only dispatcher marker files, with no previous node, report or searches to resume. I used the current live node and its stage-2 Lean docstring as the returned proof baseline. The earlier NA report in the repository was read for the topology warning and historical searches; its searches were not relabelled as Q54 searches. The existing mathematical statement and every maintained field are retained. The new nodes each introduce all their objects, coefficient conventions and domains.

The domain lemma groups the genuine geometric argument of old steps 2 and 3: two distinct proper-image inputs, the topology-equivalence input, the Noetherian hypothesis and finite Tor amplitude. It does not assert the original E-to-B mate is invertible. The Hom lemma groups old step 4: pullback constructibility, full-faithful Hom comparisons, two adjunctions, and normalization/naturality identifying their composite with the specified map. It neither requires f proper nor asserts the proper scalar comparison, and it makes no claim that Q is constructible. The parent still proves invertibility by essential surjectivity and the explicit two-sided inverse, then composes through C by the coefficient cocycle. This is the requested subdivision, not the transfer of the whole item into one node.

## Not duplicates

lem-sfb-proper-algcl-comparison-domains vs det-thm-sfb-proper-base-change-rational: the existing theorem gives the E-to-C comparison and C-proper finiteness, but not constructibility or finite Tor of J_Z L, J_T P and Rf_{*,B}J_Z L for the distinct all-continuous coefficient B. The new node groups old steps 2--3 as required by the human return.

lem-sfb-proper-algcl-comparison-domains vs det-sf-comp-proper-continuous-algcl: the existing theorem is B-proper preservation conditional on bounded constructible finite-Tor input; it does not establish that input for the C-to-B scalar extension, the two endpoints, or invertibility of the intermediate E-to-C comparison.

lem-sfb-proper-algcl-comparison-domains vs lem-sfb-constructible-algcl-topology-comparison: the existing theorem concerns J on one scheme and has no proper image or intermediate E-to-C comparison; the new node verifies the domains and geometric input for the right-adjoint comparison.

lem-sfb-algcl-topology-mate-hom-bijection vs lem-sfb-constructible-algcl-topology-comparison: full faithfulness of J alone does not identify a direct-image counit mate. The new assertion has geometric adjunctions and fixes the actual Hom function through sigma and the counit.

lem-sfb-algcl-topology-mate-hom-bijection vs lem-sfb-norm-algcl-internal-hom-base-change: that node asserts an internal derived Hom scalar comparison for finite E inputs on a single scheme and explicitly asserts no global Hom comparison or full faithfulness. Here Hom denotes ambient derived-category morphism sets, with two geometric adjunctions and the C-to-B map.

lem-sfb-algcl-topology-mate-hom-bijection vs lem-pd-monoidal-adjunction-equivalence-transport: that node assumes a direct-image comparison isomorphism already identifying adjunctions, and transports monoidal structures. This node establishes the normalized Hom action of a direct-image comparison without assuming it is an isomorphism.

lem-sfb-proper-algcl-comparison-domains vs lem-sfb-qcqs-proper-constructible-closed-base-change: that node is a geometric closed-base-change exchange, not coefficient extension or the domains of its mate.

Neither new statement is imported elsewhere in the whole blueprint: blueprint_refs searches for 'fully faithful mate', 'proper coefficient constructible', 'adjunction equivalence', 'scalar bridge', 'constructible finite subextension', 'topology comparison', and 'proper scalar comparison' found none. The 'counit mate' search found fix-lem-exchanges and lem-weil-pbc-transport-identifies-exchange, both geometric finite-coefficient exchange comparisons, not either new assertion. Whole-DAG keyword searches and direct candidate-statement readings are described above. No Stacks tag is claimed in either new source, so there is no new same-tag pair.

## Review by Q54

I read the worker brief, stage-1 contract, human settings including all three blueprint levels, GOAL, chapter record, unit record, and delivery-errors B--E in both copies of that file. The authoritative current source is main-20261015 paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md. I read that paragraph, the rational proper-image statement, the proper-base-change unit's Dctf=Dbc clause, the proper-localizing proof paragraph, and the scalar-six pullback proof. These motivate the route, but do not supply a new proof of the distinct coefficient-topology comparison. The inherited unit record uses the older sec-six-functors placement; neither that unit nor any chapter is changed. The current main source and the returned six-step expansion control this repair.

For the domain node I read the statements of extend-to-qlbar-constructible, rational proper-base-change, constructible-algcl-topology-comparison, finite-type-over-noetherian, continuous-algcl-constructible-tor, and proper-continuous-algcl. E is finite and K bounded, hence bounded below; the old canonical E-to-C comparison and proper preservation apply only to C. The equivalence J gives J_Z L and J_T P constructible. Finite type over the field gives Noetherian schemes (the field is Noetherian since its ideals are 0 and the whole field). Thus the Tor theorem applies to J_Z L, and the B-proper preservation theorem applies with its finite-Tor hypothesis verified. It supplies Q constructible. This entire argument is retained verbatim below for the future worker, not hidden by an assumption that the E-to-B comparison holds. I read Stacks morphisms.tex at lemma-finite-type-noetherian (01T6) as the named geometric input, rather than treating a section number as a citation.

For the Hom node I read upper-star-preserves, module-derived-pushpull, the topology equivalence, and kflat-scalar-comparison-normalization. The first makes f_C^*M constructible. Full faithfulness of J is used only on M,P and on f_C^*M,L, all verified in the allowed subcategories. The adjunctions are the specified derived module adjunctions. Sigma uses the forward pullback/tensor comparison, the inverse of the normalized scalar-adjunction mate of the K-flat normalization node; no flatness of c is inferred. Starting with J_Tu, the Hom chain gives J_Z(epsilon_L composed with f_C^*u) composed with sigma_M. Naturality rewrites this as J_Z epsilon_L composed with sigma_P composed with f_B^*J_Tu; its adjunct is chi_L composed with J_Tu. This is the required actual-map identification. The full calculation is preserved below. I inspected Stacks sites-cohomology.tex at the named pullback-K-flat and derived-pullback-composition labels for the scope of the normalization input; the new Hom assertion is an agent extraction, not attributed wholesale to those tags.

For parent step 1 I re-read qlbar-condensed, alpha-iso, module-ringed-topos-derived-comparison and ringed-coefficient-projection-cocycle. The first defines C with finite-subextension sections; alpha applies to any condensed ring, including B. The internal/section equivalence identifies tensors, adjunctions and counits; the coefficient cocycle defines chi for arbitrary composable ring maps without flatness. Thus its associator and maps are available in exactly the category used in the parent. These arguments are unchanged. For parent step 2 the new domain statement explicitly supplies every listed endpoint and intermediate isomorphism. For parent step 3 the new Hom statement supplies the exact postcomposition bijection, not just existence of some bijection. In parent step 4 the existing topology-comparison statement supplies essential surjectivity; both endpoints were checked in step 2, so testing with Q gives v with chi v=1 and testing with J_TP gives v chi=1. Fullness puts this inverse in the ambient category. This is written out and elementary from the cited statement and preceding steps. Parent step 5 uses the exact displayed cocycle identity, including tau at source and target. I checked Stacks sites-cohomology.tex remark-compose-base-change-horizontal (0E47) and derived-pushforward-composition (0D6E) for the source of that existing node. The coefficient composite is the original E inclusion in Omega, and the normalized counit adjunct is beta. No endpoint-only isomorphism replaces beta.

The parent citations.json quotes each statement verbatim. No proof of a cited node is used as an extra theorem. The new statements list every definition needed to introduce their notions; they have empty proofs and proof_deps, null proof_origin, and actual msearch records. Every recorded query was run and its output read. For the first node the two semantic phrasings returned proper-scheme and constructible-subset results; neither gives derived constructibility for the two different rings. For the second, Mathlib Adjunction/Restrict.lean:30--80 requires both comparison isomorphisms comm1 and comm2, so using it to establish the unknown direct-image mate would be circular without additional work. Adjunction/Mates.lean:392 gives isomorphism of conjugates on the same categories, while its mateEquiv documentation explicitly warns that a general square's invertibility is not preserved. Neither candidate is a one-line specialization giving the new geometric normalized Hom calculation. These files were read. The new nodes remain unsplit, not incorrectly classified as Mathlib leaves.

Small cases checked: K=0 gives zero endpoints; empty schemes give zero morphism sets and the unique invertible zero comparison; f=id makes the mates identities under the coefficient cocycle's unit normalization. Taking E=Q_ell changes no finiteness hypothesis. The Hom node permits any f only with P constructible, so it does not smuggle in arbitrary nonproper constructible preservation. It does not infer an equivalence of ambient derived categories. Noetherian and finite Tor conditions for proper B preservation are derived in the domain argument. C and B are distinct even though they agree at a point: on a convergent profinite sequence, ell^n zeta_(ell^n) tends to 0 but lies in no one finite subextension. This prevents accidentally replacing the coefficient inclusion by an isomorphism. The existing topology theorem remains WANTED; these tests do not purport to prove it. I found no new counterexample or statement dispute in the assigned assertion.

The new nodes do not depend on the parent, and their definitions do not reach back to it. The parent still uses genuine same-unit inputs plus the already recorded generic coefficient tools; no trace-formula, duality, SGA 4 or SGA 4-half route is introduced. Existing maintained tool_uses are preserved, and split_report keeps the existing generic-tool explanations. All parent proof steps are below 2000 characters, with total 2803; every argument removed from parent text is carried by the two independent new statements and is reproduced below as the future workers' argument. No theorem was silently weakened, no proof gap replaced by an elementary label, and no new node merely restates the original E-to-B proper comparison.

## Preservation of every returned argument

These are the original six proof steps, copied verbatim from the live baseline, with their new allocations. They are proof material in this report only; the new nodes remain statement-only as required.

### Returned step 1 → Parent step 1

Distinguish the two algebraic-closure coefficient rings: let $C$ be the finite-subextension-valued ring of [sk-def-sfb-qlbar-condensed], and retain $B$ from the item. The inclusions give $A_E\xrightarrow a C\xrightarrow c B$. Write $S_W=C_W\otimes^L_{A_{E,W}}-$ and $J_W=B_W\otimes^L_{C_W}-$. The canonical balanced associator identifies $J_WS_W$ with $T_W$. All three rings are pulled back from the point, so [lem-sfb-alpha-iso] identifies their geometric inverse images with their source coefficients. Work through the exact monoidal internal/section-module equivalence [lem-pd-module-ringed-topos-derived-comparison]. Then the associators and the normalized scalar push comparisons are those of [lem-pur-ringed-coefficient-projection-cocycle]; they apply to $a,c$ without a flatness hypothesis. Denote the three counit-mate push comparisons by $\chi_a,\chi_c,\chi_{ca}$.

Cited statements: sk-def-sfb-qlbar-condensed, lem-sfb-alpha-iso, lem-pd-module-ringed-topos-derived-comparison, lem-pur-ringed-coefficient-projection-cocycle.

### Returned step 2 → Domain node (first part)

Put $L=S_ZK$. It is bounded constructible by [lem-sfb-extend-to-qlbar-constructible]. Since $f$ is proper between the standing schemes, clause (2) of [det-thm-sfb-proper-base-change-rational], used with coefficient $C$, gives $P=Rf_{*,C}L\in D^b_c(T,C)$. Clause (1) of the same node, applied to the bounded-below $A_E$-complex $K$, says that the canonical map $\chi_{a,K}:S_TRf_{*,A_E}K\to Rf_{*,C}L$ is invertible. This invocation is solely about $C$, not $B$.

Cited statements: lem-sfb-extend-to-qlbar-constructible, det-thm-sfb-proper-base-change-rational.

### Returned step 3 → Domain node (second part)

Apply [lem-sfb-constructible-algcl-topology-comparison] at $Z$ and $T$. Thus $J_ZL$ and $J_TP$ are bounded constructible. The schemes are Noetherian because they are finite type over a field [lem-weil-pbc-finite-type-over-noetherian]; the field is Noetherian since its only ideals are zero and itself. Hence [det-sf-comp-continuous-algcl-constructible-tor] gives finite Tor amplitude for $J_ZL$. The bounded-constructible finite-Tor preservation assertion of [det-sf-comp-proper-continuous-algcl], for the actual all-continuous $B$ and the given proper $f$, gives $Q=Rf_{*,B}J_ZL\in D^b_c(T,B)$. This verifies membership of both endpoints of $\chi_{c,L}:J_TP\to Q$ in the full constructible subcategory.

Cited statements: lem-sfb-constructible-algcl-topology-comparison, lem-weil-pbc-finite-type-over-noetherian, det-sf-comp-continuous-algcl-constructible-tor, det-sf-comp-proper-continuous-algcl.

### Returned step 4 → Hom-bijection node

For $M\in D^b_c(T,C)$, pullback preserves bounded constructibility by [lem-sfb-dc-upper-star-preserves]. Write $\sigma_M:f_B^*J_TM\xrightarrow{\sim}J_Zf_C^*M$ for the canonical tensor comparison, normalized by [lem-sfb-kflat-scalar-comparison-normalization]. The adjunctions of [sk-def-sfb-module-derived-pushpull] and full faithfulness of $J_T,J_Z$ in [lem-sfb-constructible-algcl-topology-comparison] give bijections
$$\operatorname{Hom}_B(J_TM,J_TP)\cong\operatorname{Hom}_C(M,P)\cong\operatorname{Hom}_C(f_C^*M,L)\cong\operatorname{Hom}_B(J_Zf_C^*M,J_ZL)\cong\operatorname{Hom}_B(J_TM,Q).$$
This composite is precisely postcomposition with $\chi_{c,L}$. Indeed the first bijection writes an arrow as $J_Tu$. Its image under the middle two bijections is $J_Z(\varepsilon_L\circ f_C^*u)$. After precomposition with $\sigma_M$ it is $J_Z\varepsilon_L\circ\sigma_P\circ f_B^*J_Tu$, by naturality of $\sigma$. The adjunct of $J_Z\varepsilon_L\circ\sigma_P$ is the specified $\chi_{c,L}$, so naturality of adjunction gives $\chi_{c,L}\circ J_Tu$. This checks the actual counit mate, rather than a freely chosen isomorphism of its endpoints.

Cited statements: lem-sfb-dc-upper-star-preserves, lem-sfb-kflat-scalar-comparison-normalization, sk-def-sfb-module-derived-pushpull, lem-sfb-constructible-algcl-topology-comparison.

### Returned step 5 → Parent step 4

Essential surjectivity of $J_T$ from [lem-sfb-constructible-algcl-topology-comparison] and step 4 imply that postcomposition with $\chi_{c,L}$ is bijective on $\operatorname{Hom}_B(N,-)$ for every bounded constructible $N$. Both endpoints are in that class by step 3. Taking $N=Q$, surjectivity supplies $v:Q\to J_TP$ with $\chi_{c,L}v=1_Q$. Taking $N=J_TP$, injectivity and $\chi_{c,L}(v\chi_{c,L})=\chi_{c,L}1_{J_TP}$ give $v\chi_{c,L}=1_{J_TP}$. Thus $\chi_{c,L}$ is invertible in the ambient category, whose constructible subcategory is full.

Cited statements: lem-sfb-constructible-algcl-topology-comparison.

### Returned step 6 → Parent step 5

The coefficient cocycle of [lem-pur-ringed-coefficient-projection-cocycle] gives
$$\chi_{ca,K}\circ\tau_T=Rf_{*,B}(\tau_Z)\circ\chi_{c,S_ZK}\circ J_T(\chi_{a,K}),$$
where $\tau_W:J_WS_W\xrightarrow{\sim}T_W$ is the balanced associator, evaluated at the required complex. Step 2 proves invertibility of $\chi_{a,K}$ and steps 3--5 prove invertibility of $\chi_{c,S_ZK}$. Functors preserve inverses, so every factor on the right, and $\tau_T$, is invertible. Thus $\chi_{ca,K}$ is invertible. Its coefficient map is exactly the original $E\hookrightarrow\Omega$ map, and its adjunct is exactly the pullback/tensor comparison followed by $T_Z\varepsilon$ in the item, by the cocycle's definition of $\chi_{ca}$ and step 1's normalization. Therefore $\chi_{ca,K}=\beta_{f,K}$.

Cited statements: lem-pur-ringed-coefficient-projection-cocycle.

## What remains

This is a one-level stage-1 split only. Both new nodes await independent proofs. The old topology-comparison node remains the explicit inherited mathematical obligation. The required dry run and push follow after this signed review; no Lean proof is claimed.
