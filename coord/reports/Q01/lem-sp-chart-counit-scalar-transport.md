# Stage-1 repair: lem-sp-chart-counit-scalar-transport

## Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-chart-counit-scalar-transport.json`: unchanged statement, four-step assembly, 2038 characters in its proof texts, status split.
- `dag/nodes/sec-smooth-purity/lem-sp-raw-chart-scalar-counit-pasting.json`: new statement, unsplit, no Mathlib match; canonical right-map factorization, finite-Tor domains and the raw sum-then-affine scalar-counit equation.
- `dag/nodes/sec-smooth-purity/lem-sp-site-scalar-counit-pair-conjugacy.json`: new statement, unsplit, no Mathlib match; simultaneous conjugacy of the two evaluation/scalar maps under specified site and coefficient squares, including extension to arbitrary inputs.
- `dag/nodes/sec-smooth-purity/lem-sp-left-comparison-scalar-counit-pair.json`: new statement, unsplit, no Mathlib match; simultaneous conjugacy of both scalar-counit maps under a compatible left comparison, including inverse and composite comparisons.
- `citations.json`: verbatim quotes for every citation of each assembly step. Sandbox scripts and `returned-node.json` are working records, not delivery files.

## Attachments

None. I searched the project Lean under `lean/WeilConjectures` for the blueprint tag, scalar/counit terms, chart terms, comparison, conjugacy and pasting. There is no project declaration giving the item. The existing `EquivalenceRightAdjointCounitTransport` and `CounitComparisonComposition` files concern a single right-adjoint comparison or resolving counits and do not give the two-coefficient formulas here. No compiler or Lake command was run.

## WANTED

None. The available main-20261015 Charts paragraph and the retained seven-step proof provide the route and argument being decomposed. The additional categorical formulas are agent-written expansions of that route, not quotations of an unavailable textbook and not attributed to Stacks or to SGA.

## Fault and repair

The human return requires at least two comparable statement-only nodes and an assembly of at most 3000 characters in place of the 5088-character proof. The sandbox initially contained only dispatcher `.brief*` files, with no node, report or searches log. I copied the current read-only repository node; its seven steps have exactly the character counts in the return. Its statement, sources, historical searches, blueprint fields, original creation attribution, Lean audit and maintainer-owned fields were retained. I did not run git in the shared repository. There was no older sandbox proof to discard or rebase. The delivery tool handles current-server rebasing.

Three new work items divide the existing proof's work. They have empty proof/proof_deps and null proof_origin; their statements introduce every object and comparison. The proof material for their future workers is preserved verbatim below, rather than deleted or shortened into an unproved phrase. The two categorical nodes are stated as identities of two individually specified maps, even before either counit equation is known. This avoids delegating either entire site clause of the item to a renamed assertion of that same clause. None assumes invertibility of an exceptional coefficient comparison or chooses an orientation. The parent uses these nodes as genuine intermediate calculations and still checks the geometric hypotheses.

## Distribution of the returned argument

1. Old Step 1 (823 characters): raw chart node, including the definitions E,h,P,G, the composite counit, finite-Tor domain checks and the K-flat/Tate factorization of a_g. The generator calculation x tensor b and (z tensor a) tensor b is preserved in the appendix. New assembly Step 1 uses this result.
2. Old Step 2 (383): raw chart node's proof obligation uses the already existing affine and etale-sum scalar equations, at the respective allowed inputs K and G_AK. These are statement dependencies of that node; they are not duplicated as new leaves. The complete original equations are in the appendix.
3. Old Step 3 (684): raw chart node's actual scalar-counit equation; its worker must perform the same two naturality substitutions and the affine/sum equation replacements. The appendix retains the full displayed calculation, rather than replacing the work by an assertion that mates compose.
4. Old Step 4 (686): left-comparison node, with lambda:P E -> F_g, q=s, q'=beta_g and epsilon=w. Its separate D and E formulas are precisely the precomposition/cancellation argument. New assembly Step 2 supplies the actual geometric lambda square from the existing normalization node.
5. Old Step 5 (812): site-conjugacy node's counit and two comparison-square hypotheses, with r_R recording the actual right-functor identification that the old coordinates suppressed. New assembly Step 3 supplies those hypotheses from the same three existing geometric nodes. Neither the coefficient/site square nor the right-functor coherence has been replaced by an unnamed choice.
6. Old Step 6 (784): site-conjugacy node's two explicit formulas with Z_L; its worker must perform the same c_B inverse cancellation, coefficient-square substitution and delta naturality. The appendix retains those cancellations. The statement is stronger than an implication between counit equations: D and E are transported separately without assuming D=E.
7. Old Step 7 (916): the site-conjugacy node handles essential surjectivity and naturality at an arbitrary pro-etale K. The left-comparison node handles the remaining refinement and common-refinement calculation, using lambda=phi and the same specified q square. Its composite/inverse clause covers canonical comparison through any common refinement. New assembly Step 4 supplies the geometric refinement square. Nothing from the old refinement argument is omitted.

## Mathlib and duplicate searches

For each new node I ran two semantic phrasings with leanfinder, Loogle, grep via the required msearch.py command, and LeanSearch. All queries and the recorded answer digests are in searches.jsonl and copied into the appropriate mathlib_searches fields. The two initially unavailable LeanSearch calls returned the actual rate-limit message, not an empty search. In this repair both queries were rerun successfully; their genuine successful records are appended to searches.jsonl and to the respective node mathlib_searches. The site query returned conjugateEquiv_counit variants and equivalence counit naturality; the left-comparison query returned ModuleCat change-of-rings counits and conjugateEquiv_counit. I read Mathlib/CategoryTheory/Adjunction/Mates.lean and Basic.lean and the ModuleCat ChangeOfRings source: these concern mates or a single counit, rather than the two independent D/E comparison formulas for arbitrary natural evaluations. One Loogle pattern used the unknown identifier CategoryTheory.NatIso; it is recorded as an unsuccessful pattern and was repaired by the valid query `CategoryTheory.Adjunction.counit, CategoryTheory.Equivalence`.

The raw-chart searches returned AffineSpace morphism and formally-etale algebra facts, unrelated to the chart counit. `CategoryTheory.Adjunction.comp_counit_app` (Mathlib/CategoryTheory/Adjunction/Basic.lean:580) expands a composite counit but does not prove its coefficient equation or canonical Tate factorization. The site searches returned counit-cancellation identities for an equivalence and `Equivalence.toAdjunction_counit`, not the four comparison-functor/evaluation formulas. The left-comparison searches returned `Adjunction.ofNatIsoLeft` (Basic.lean:497, counit at 499), `conjugateEquiv_counit`, and leftAdjointUniq counit lemmas; these identify one transported counit and do not give the simultaneous two-coefficient pair and its coefficient square. None is an exact match or a one-line specialization for a new node's complete statement.

I searched the entire DAG for counit/pasting/conjugacy/transport/equivalence/refinement and scalar/coefficient terms, then read the relevant candidate statements. Whole-blueprint searches were made with blueprint_refs.py for `counit`, `counit transport`, `composite counit`, `counit scalar`, `sum-then`, `counit-preserving`, `counit conjugacy`, `coefficient-counit`, `scalar-counit`, `counit pair`, `left comparison` and `etale chart`. No blueprint statement supplies a new node's full assertion. The ancestor command returns det-sp-reduction-exceptional; each new from.via is [lem-sp-chart-counit-scalar-transport]. The new source places name the specific Charts argument and old proof steps they distribute. No new node cites a Stacks tag, so there is no same-tag pair omitted from the following comparison.

## Not duplicates

lem-sp-raw-chart-scalar-counit-pasting vs lem-sp-chart-counit-scalar-transport: the new node proves the canonical right-map factorization and scalar equation for the raw functor P_R E_R on the ordinary site; it does not identify that functor with the specified compactification functor, transport across sites, or handle refinements.

lem-sp-raw-chart-scalar-counit-pasting vs lem-sp-affine-counit-scalar: the existing assertion treats P_R alone; the new one combines it with etale sum extension and a nontrivial right-map factorization.

lem-sp-raw-chart-scalar-counit-pasting vs lem-sp-etale-sum-counit-scalar: the existing assertion treats E_R alone; it does not paste the affine scalar map and counit or compare the composite Tate/shift map.

lem-sp-raw-chart-scalar-counit-pasting vs det-sp-composition-comparisons: the existing node uses exceptional right adjoints, with scalar comparisons supplied by det-sp-reduction-exceptional, and is therefore not a way to prove the present canonical chart identity without circularity; it has no raw etale sum/Tate factorization assertion.

lem-sp-raw-chart-scalar-counit-pasting vs lem-pur-composite-integration-counit: the latter factors the value of a composite counit using projection maps for a single coefficient stage and chosen dualizing objects; it has no two-ring canonical scalar equation.

lem-sp-raw-chart-scalar-counit-pasting vs lem-pc-adjunction-square-composition: the latter assumes scalar adjunctions and invertible right-route comparisons and asserts composition of their mates, not the canonical raw geometric chart formula and its finite-Tor/Tate identification.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-sp-et-proet-coefficient-compatibility: the existing node supplies geometric compact-support coefficient squares and the consequence for a counit identity. The new assertion is a categorical normal-form identity for each of two separate arbitrary natural evaluation maps, without assuming any counit identity or even adjunction axioms; it exposes the actual cancellation and the general right comparisons r_R. It does not reconstruct any compact-support coefficient map.

lem-sp-site-scalar-counit-pair-conjugacy vs det-sp-et-proet-adjunction-transfer: the latter constructs a transported adjunction for one coefficient ring; it does not state either scalar/evaluation normal-form identity.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-cat-equivalence-right-adjoint-counit-transport: the existing node constructs a right-adjoint comparison for one left equivalence and one target; there are no two scalar functors or two comparison squares.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-coef-fully-faithful-counit-descent: the latter recovers an isomorphism and its counit equation from full faithfulness and a supplied primed equation. The new one needs no full faithfulness and transports both maps forward, without assuming either equation; neither is a specialization of that existence statement.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-sfb-equivalence-square-inverse-mate-coherence: that statement transports inverse mates across equivalences and assumes normalized adjunction comparisons; the new assertion is about arbitrary evaluations and separate normal-form equalities, requiring only essential surjectivity of one functor for its final implication.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-sfb-etale-proetale-scalar-counit-transposes: that node treats inverse-image/direct-image mates for a scheme morphism on the unbounded module categories; its common normal form is not the compact-support/chart comparison calculation, nor the arbitrary-evaluation categorical assertion.

lem-sp-site-scalar-counit-pair-conjugacy vs lem-pur-adjoint-equivalence-conjugation-calculus: that node gives the counit and transpose formulas for one adjunction conjugated by adjoint equivalences; it does not state the two independent scalar-evaluation formulas or their coefficient-square hypotheses.

lem-sp-left-comparison-scalar-counit-pair vs lem-sfb-adjunction-transport-left-iso: the existing statement constructs a single transported adjunction. The new one assumes the transported evaluation and computes both two-coefficient scalar-counit maps, with the specified compatibility square and inverse/composite comparisons.

lem-sp-left-comparison-scalar-counit-pair vs lem-sp-chart-left-scalar-normalization: the existing statement constructs and normalizes the specific geometric lambda square. The new assertion is the general two-morphism calculation that uses such a square, applicable to arbitrary natural evaluations and arbitrary compatible left comparisons, not just the graph comparison.

lem-sp-left-comparison-scalar-counit-pair vs lem-pur-refinement-coefficient-mate: that node transposes one commuting square under scalar adjunctions; it gives neither of the two explicit evaluation/scalar conjugacy formulas.

lem-sp-left-comparison-scalar-counit-pair vs lem-pc-counit-comparison-composition: the latter concerns resolving/derived-functor counits and their model-composition laws, as checked in its project Lean file; it does not assert either scalar-counit pair formula.

## Review by Q01

I read the current main-20261015 sk-lem-sp-reduction-exceptional.proof.md, especially the entire Charts paragraph, the sk-lem-sp-reduction unit and sec-smooth-purity chapter records, the original seven-step item, and the full statements of all nodes cited by the new assembly. The source's route is sum over the etale fibres followed by ordered projective/affine integration and coefficient comparison. This repair changes no geometric route, coefficient category, hypothesis, conclusion or normalization; it only distributes the previously reviewed naturality calculations. All new nodes are statement-only, with real source places and recorded searches. The categorical pair nodes are explicit extracted subarguments under the human's re-split instruction; they are not new geometric prerequisites or restated site clauses.

For Step 1 I checked the new raw-chart statement says both a_g=h_B(a_d)a_e(G_AK) and exactly the displayed w_B P_B E_B(a_g) s = T_Y(w_A) equation. It also states the domain checks. Its hypotheses are the same finite rings, arbitrary non-flat coefficient homomorphism, etale e, d>=0, chosen order and finite-Tor K as the parent. Its two input counit equations are precisely those of lem-sp-affine-counit-scalar and lem-sp-etale-sum-counit-scalar, not claims about an unrelated normalization. The raw canonical factorization is a derived isomorphism/natural map statement, never a per-degree substitute.

For Step 2 I opened lem-sp-chart-left-scalar-normalization and used its displayed beta_g T(lambda_A)=lambda_B T s square, its statement that lambda retains the actual composite counit, and no hidden construction from its proof. In the new pair node use F=P E, F'=F_g, H=hG and epsilon=w. Its two independent formulas show that both target maps precomposed with T(lambda_A(H_AK)) equal the raw maps; the latter is invertible because lambda is a natural isomorphism. The direction epsilon'=epsilon lambda(H)^(-1) agrees with the fixed counit, not its inverse. There is no assumption that a coefficient mate for an exceptional adjoint is invertible.

For Step 3 I opened all three cited geometric statements. The coefficient-compatibility node's exact displayed square has F_B(delta_U) b T(c_A) on its left and c_B C(beta) delta_Y on its right; solving it for F_B(delta_U)b uses precisely T(c_A)^(-1), as in the retained calculation. The chart-adjunction statement supplies epsilon'_C(L)=C(epsilon_L)c(HL)^(-1) under its specified right-functor identifications and says C is an equivalence of finite-Tor categories. The chart-domain statement says the canonical tensor comparisons intertwine coefficient extension, pullback, Tate tensor powers and shifts. Applying that to H=e^*p_d^*(-)(d)[2d] gives the new node's right square with the actual r_R. Thus all hypotheses of the new site pair statement hold: c,r,delta are natural isomorphisms and C_Y,A is essentially surjective. The new result transports D and E separately through the explicitly typed Z_L, then extends equality by naturality to all objects. No fullness, faithfulness, compactness of a resolution, or equality of a chosen comparison with an identity is smuggled in.

For Step 4 I reread the refinement and common-refinement clauses of lem-sp-et-proet-coefficient-compatibility. Its formula q^{c'} T(phi_A)=phi_B T q^c is exactly the coefficient-square hypothesis of the left-comparison pair node. Counits are understood under the stipulated canonical adjunction identification, so their transport is epsilon^{c'}=epsilon^c phi(H)^(-1), as in the old proof. The pair node includes inverse and composite comparisons, hence applies to the canonical common-refinement comparison. This computation uses the actual fixed-compactification q, not an isomorphism merely having the same endpoints.

I type-checked the new categorical statements in words, source and target of every factor. In the site node, Z_L starts at T'_Y F'_A H'_A C_Y,A L and ends at C_Y,B T_Y F_A H_A L. Thus both equations have the same target C_Y,B T_Y L after postcomposing by delta_Y,L. Including r_R explicitly was a useful correction to the old coordinate-suppressed presentation. In the left-comparison node, T_Y(lambda_A(H_AK)) goes from T_Y F_A H_AK to T_Y F'_A H_AK, which is exactly the common invertible precomposition. Neither pair node assumes the equality it concludes; both retain separate formulas before any equality assumption.

I also redid the algebra rather than merely checking strings. For the site D formula, naturality of epsilon'_B at delta_Y,L combines with the right square; naturality of q' at r_A moves T'_X(r_A) left of q'. Substitution of the coefficient square and naturality of c_B at a_L cancels c_B and leaves C_Y,B(D_L) Z_L. The E formula uses delta_Y naturality at epsilon_A and the specified epsilon'_A formula. Equality on arbitrary K follows by choosing an isomorphism C_Y,A L -> K and cancelling it in the naturality squares. For the left-comparison D formula, substitute the coefficient square and move lambda_B through F_B(a_K) by naturality; epsilon'_B lambda_B=epsilon_B cancels it. For E, functoriality cancels lambda_A(H_AK)^(-1) lambda_A(H_AK). Inverse comparisons satisfy the reversed coefficient square, and composition of two squares gives the square for mu lambda. These are the exact arguments delegated for parallel work, with the old versions retained below.

I checked delivery-errors B--E: all objects, finite rings and coefficient maps are introduced; new proofs are empty; no unsupported Stacks tag, missing definition, silent hypothesis, per-degree identification or circular parent citation appears. The new statement dependencies never reach this item. The categorical statements require only categories and explicitly specified functors/natural maps, not any geometric assumption from their eventual application. Their overlap with existing mate theorems was checked by reading those statements, not by treating titles as evidence.

Small cases: for d=0, P=G=id and the raw formula is the sum equation; for e=id it is the affine equation. Empty U gives the zero raw functor and the same counit calculation; zero categories or empty categories cause no existence assumption in either pair statement (essential surjectivity handles the empty target correctly). With A=B and all comparisons identities both pair formulas reduce to the same two maps separately. With nonidentity lambda, the displayed inverse direction is required and gives the proper conjugacy. The non-flat map Z/l^2 -> Z/l adds no finite projective-dimension hypothesis. N=1 can only annihilate the zero coefficient rings; their categories are trivial and no chosen Tate generator is used. The shift is [2d], so the tensor/pullback factorization retains the original even-shift sign convention. Refinement identities and two different chains with the same canonical composite obey the same pair formula.

No old proof step exceeds 2000 characters and no new assembly step does. The assembly is 2038 characters in total; each new node carries a comparable original argument (Steps 1--3, Steps 5--6 plus the first part of 7, and Step 4 plus the refinement part of 7). This repairs the human return by distributing the work, not by shortening its mathematical content. The exact old proof is retained below. The required server dry run passed the maintainer preflight, including the graph and split checks; the repair is ready for direct delivery.

## Retained returned proof, verbatim

### Returned Step 1

Put $V=\mathbf A^d_Y$, $E_R=De_{\Sigma!,R}$, $h_R=e_R^*$, $P_R=F_{d,R}$ and $G_R=p_{d,R}^*(-)(d)[2d]$. Write $u_R$ and $v_R$ for the affine and sum counits. The chart adjunction has right functor $h_RG_R$ and composite counit $w_R=u_R\circ P_R(v_R G_R)$ before its left comparison. The cited domain statement puts $G_AK$, $h_AG_AK$, all compact-support values and their scalar extensions in the required finite-Tor categories. The canonical chart tensor map is
$$a_g=h_B(a_d)\circ a_e(G_AK).$$
Indeed the pullback/tensor maps on a K-flat representative carry $x\otimes b$ to the pullback of $x$ tensored with $b$; the Tate factor on either path carries $(z\otimes a)\otimes b$ to $z\otimes\varphi(a)b$. The shift is even, so no interchange sign occurs. The domain statement also identifies this map through site comparison.

Cited nodes: lem-sp-chart-finite-ring-adjunction, lem-sp-etale-ctf-chart-domain, lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Elementary: False.

### Returned Step 2

Apply the two scalar-counit statements with base $Y$ for $p_d$ and with input $G_AK$ for $e$. They give
$$u_{B,T_YK}P_B(a_d)\beta_d(G_AK)=T_Y(u_{A,K}),$$
$$v_{B,T_VG_AK}E_B(a_e(G_AK))\sigma_e(h_AG_AK)=T_V(v_{A,G_AK}).$$
Both use the specified coefficient maps; the second input is allowed by Step 1. These statements require neither flatness nor finite projective dimension of $B/A$.

Cited nodes: lem-sp-affine-counit-scalar, lem-sp-etale-sum-counit-scalar. Elementary: False.

### Returned Step 3

For an object $M$ on $U$ set $s_M=P_B(\sigma_e(M))\beta_d(E_AM)$. Suppress object subscripts when their type determines them. Expanding $w_B$ and $a_g$, naturality of $v_B$ at $a_d:T_VG_AK\to G_BT_YK$ gives
$$w_BP_BE_B(a_g)s_{h_AG_AK}
=u_BP_B\bigl(a_d\,v_{B,T_VG_AK}E_B(a_e(G_AK))\sigma_e(h_AG_AK)\bigr)\beta_d(E_Ah_AG_AK).$$
The sum equation of Step 2 replaces the three middle factors by $T_V(v_{A,G_AK})$. Naturality of $\beta_d$ at $v_{A,G_AK}$ then gives
$$u_BP_B(a_d)\beta_d(G_AK)\,T_Y(P_A(v_{A,G_AK}))=T_Y(u_A)T_Y(P_A(v_AG_A))=T_Y(w_A),$$
where the affine equation of Step 2 was used. This is a direct substitution and naturality calculation, not an extra geometric comparison.

Cited nodes: . Elementary: True.

### Returned Step 4

Let $\lambda_R:P_RE_R\xrightarrow{\sim}F^{et}_{g,R}$ be the cited graph-normalized comparison. Its statement gives both $\epsilon^{et}_{g,R}=w_R\lambda_R(h_RG_R)^{-1}$ and
$$\beta_g\,T_Y(\lambda_A)=\lambda_BT_U\,s.$$
Precompose the desired etale equality with the isomorphism $T_Y(\lambda_A(h_AG_AK))$. The left side becomes, by this square and naturality of $\lambda_B$ at $a_g$,
$$\epsilon^{et}_{g,B}F^{et}_{g,B}(a_g)\lambda_B(T_Uh_AG_AK)s=w_BP_BE_B(a_g)s.$$
Step 3 makes this $T_Y(w_A)$, which equals $T_Y(\epsilon^{et}_{g,A})T_Y(\lambda_A(h_AG_AK))$. Cancel the common invertible precomposition. This proves the asserted equation for the actual etale counit and the named $\beta_g$.

Cited nodes: lem-sp-chart-left-scalar-normalization. Elementary: False.

### Returned Step 5

For an etale object $L$ on $Y$, abbreviate site comparison by $C_{T,R}$, its tensor comparison by $\delta_T$, and the fixed compact-support comparison by $c_R=c_{g,R}$. Put $M=H^{et}_{g,A}L$ and $M'=H^{et}_{g,B}T_YL$. The chart-adjunction statement gives $\widetilde\epsilon_R=C_{Y,R}(\epsilon^{et}_R)c_R^{-1}$ on comparison objects. The coefficient/site square gives, at $M$,
$$F^{pro}_{g,B}(\delta_{U,M})b_g(C_{U,A}M)=c_B(T_UM)C_{Y,B}(\beta_g(M))\delta_{Y,F^{et}_{g,A}M}\,T_Y(c_A(M))^{-1}.$$
The domain statement intertwines the geometric right functors and their tensor comparisons. Thus after identifying $H^{pro}_{g,A}C_{Y,A}L$ with $C_{U,A}M$, the map $H^{pro}_{g,B}(\delta_{Y,L})a^{pro}_g$ is $C_{U,B}(a^{et}_g)\delta_{U,M}$. These are the specified comparisons, not a choice of right-adjoint orientation.

Cited nodes: lem-sp-chart-finite-ring-adjunction, lem-sp-et-proet-coefficient-compatibility, lem-sp-etale-ctf-chart-domain. Elementary: False.

### Returned Step 6

Postcompose the proposed pro-etale equation at $C_{Y,A}L$ with $\delta_{Y,L}$. Naturality of the B-counit first replaces its target by $C_{Y,B}T_YL$ and inserts $F^{pro}_{g,B}(H^{pro}_{g,B}(\delta_{Y,L}))$. Substitute the formulas of Step 5. Naturality of $c_B^{-1}$ at $a_g^{et}:T_UM\to M'$ cancels $c_B(T_UM)$, leaving
$$C_{Y,B}\bigl(\epsilon^{et}_{g,B}F^{et}_{g,B}(a_g^{et})\beta_g(M)\bigr)\delta_{Y,F^{et}_{g,A}M}\,T_Y(c_A(M))^{-1}.$$
Step 4 replaces the parenthesized factor by $T_Y(\epsilon^{et}_{g,A})$. Naturality of $\delta_Y$ turns the result into
$$\delta_{Y,L}\,T_Y\bigl(C_{Y,A}(\epsilon^{et}_{g,A})c_A(M)^{-1}\bigr)=\delta_{Y,L}\,T_Y(\widetilde\epsilon_{g,A}).$$
Cancel $\delta_{Y,L}$. This proves precisely the equation with the named $b_g$ on every etale-origin object.

Cited nodes: . Elementary: True.

### Returned Step 7

Every pro-etale $K$ in the stated category is isomorphic to $C_{Y,A}L$ by the comparison equivalence in the chart-adjunction statement. All factors of the equation are natural transformations (the canonical tensor comparisons, coefficient maps and counits). Applying their naturality to this isomorphism and cancelling it proves the equation at $K$. For refinement $c\to c'$, write $\phi_R:F^c_{g,R}\xrightarrow{\sim}F^{c'}_{g,R}$. The refinement clause gives $q^{c'}T_Y(\phi_A)=\phi_BT_U q^c$, with $q=\beta$ or $b$. Under the canonical adjunction identification the counit is $\epsilon^{c'}=\epsilon^c\phi_R(H_R)^{-1}$. Substitution, naturality of $\phi_B$ at $a_g$ and cancellation of $\phi_B$ show that the equation for $c'$ is the equation for $c$ precomposed with $T_Y(\phi_A(H_A))^{-1}$. Common-refinement comparisons obey the same clause, so the assertions hold after their canonical identifications as well.

Cited nodes: lem-sp-chart-finite-ring-adjunction, lem-sp-et-proet-coefficient-compatibility, lem-sp-chart-left-scalar-normalization. Elementary: False.

## Completion

All mathematical repair obligations are complete. The first dry run refused two citation quotes shorter than 40 characters, before any push. I expanded both to the complete pair formulas and inverse/composite clause, and made the reused coefficient-compatibility quotes specific to the site square (Step 3) and refinement square (Step 4). The server dry run exited 0 with OK (not pushed) at a1c7330eedd after the citation repair. The report is finalized before the final receipt and authorized direct push.


## Second reading by Q01

Repair of immutable stage-2 return cf86bf836e3b, read on 2026-10-22.
The retained full packet is in the S1 sandbox. The S2 sandbox contained only
dispatcher markers. The return explicitly requires deliver.py on the S1 lane:
all four JSON files and this report form the S1 delivery. There is no Lean
module or lean record for this statement-only re-split; stage 2 follows its
S1 landing, and no compile is appropriate for this S1 packet.

H1 / missing files: I opened lem-sp-raw-chart-scalar-counit-pasting,
lem-sp-site-scalar-counit-pair-conjugacy and
lem-sp-left-comparison-scalar-counit-pair in the S1 sandbox. All three files
are present and will be included. Each is self-contained, unsplit, with empty
proof and proof_deps, null proof_origin, its creation/source/blueprint records,
and all three search kinds. I appended successful retries for the two
rate-limited LeanSearch queries, preserving their original unavailable
records and the genuine successful search receipts.

H2 / wrong stage: against current read-only main, the item differs only in
proof, proof_deps and split_report, which are S1 split fields. The statement
and stmt_deps are identical. The released human S1 repair note of 2026-10-22
postdates NS's review of 2026-10-21, so this re-split is not superseded. Its
four-step assembly has 2038 characters and proof_deps exactly the union of
step uses. The complete original seven steps are retained verbatim above.
The S1 wrapper rebases the packet onto the current server branch.

H11 / actual second reading: I reread the main-20261015 exceptional-comparison
proof, its entire Charts paragraph, the unit and chapter, the four assembly
steps, all new statements and the cited geometric statements. This S1
correction has no Lean to match; I checked the delegated assertions and every
application instead:

1. The raw node retains the standing field, finite rings, arbitrary unital
coefficient map, common N, finite-Tor categories, etale e, d >= 0 and affine
order. Its a_K and h_B(a_d) a_e(G_A K) both go from T_U h_A G_A K to
h_B G_B T_Y K. At M=h_A G_A K, s_M goes from T_Y P_A E_A M to P_B E_B T_U M;
thus w_B P_B E_B(a_K) s_M and T_Y(w_A) are parallel. The affine equation
applies with base Y; the sum equation applies at G_A K by chart-domain.
Naturality of v_B at a_d and beta_d at v_A gives their displayed pasted
identity. This carries old Steps 1--3 including the K-flat/Tate normalization
and even shift; it excludes the later graph comparison as intended.

2. In the left-comparison node, lambda_R(H_R K)^(-1) goes from F'_R H_R K to
F_R H_R K, so its epsilon' formula has the correct direction. Substitute
q' T(lambda_A)=lambda_B T_X q, then use naturality of lambda_B at a_K and
cancel lambda_B with its inverse: D' T(lambda_A)=D. Functoriality and inverse
cancellation give the E formula. The precomposition is invertible, hence the
equivalence of equations. Reversed and composed coefficient squares give
inverse and composite comparisons with order mu lambda. Assembly Step 2
gets this square and the actual counit from chart-left-scalar-normalization.
Step 4 gets the specified refinement square for beta or b from coefficient
compatibility. These carry old Step 4 and the refinement portion of Step 7.

3. In the site node r_R has source H'_R C_Y,R and target C_X,R H_R. The
transported counit composes F'_R(r_R), c_R(H_R)^(-1), C_Y,R(epsilon_R) in that
order. Both comparison squares are parallel. Z_L goes from
T'_Y F'_A H'_A C_Y,A L to C_Y,B T_Y F_A H_A L. Naturality of epsilon'_B at
delta_Y, the right square, naturality of q' at r_A and the coefficient square
give delta_Y D'=C_Y,B(D) Z. The transported epsilon'_A formula and naturality
of delta_Y give delta_Y E'=C_Y,B(E) Z separately, without assuming D=E.
Essential surjectivity and naturality then extend equality to every primed
object; no full faithfulness is needed. Assembly Step 3 supplies these exact
hypotheses from the specified chart adjunction, domains and coefficient/site
square, using the actual c, beta and b. This carries old Steps 5--6 and the
arbitrary-input portion of Step 7, rather than reasserting the pro-etale
clause without its calculation.

I checked d=0 (sum equation), e=id (affine equation), empty U (zero functor),
A=B and identity comparisons, nonidentity comparisons (inverse directions),
non-flat Z/ell^2 -> Z/ell (no new projective-dimension assumption), and N=1
(zero coefficient rings). Empty categorical targets introduce no extra
hypothesis; essential surjectivity is used only for the arbitrary-input
conclusion. No exceptional coefficient comparison is assumed invertible,
no orientation chosen, and no new node depends on the parent. No unit
statement or route changes. The old seven arguments are distributed among
three comparable work items, with no missing refinement or domain work.

This repair changes the delivery lane, includes all three previously missing
statement-node files, adds successful recorded searches, and supplies this
substantive second reading. The S1 wrapper dry run and direct push follow.
