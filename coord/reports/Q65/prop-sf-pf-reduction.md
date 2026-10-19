# Q65 repair: prop-sf-pf-reduction

## Files written
- dag/nodes/sec-smooth-purity/prop-sf-pf-reduction.json: item repaired and marked split; statement and Lean record unchanged.
- citations.json: literal statements for every step citation.
- report.md: review and retained original long argument.
No new nodes; no Mathlib leaves. Scratch repair script and original searches.jsonl are sandbox-only supporting files.

## Attachments
None. Exchange.lean:177-195 in the read-only slopmaster2 source states reduction comparisons, not the complete commutative-square assertion, and both comparison declarations have sorry bodies. They cannot attach this item.

## WANTED
None. The current main-20261015 blueprint proof, existing DAG theorem statements, and local Stacks source are available.

## Fault and repair
The returned step 3 was 3971 characters and hid three independently reusable facts. I kept its compactification/mate/open-factor route and all other original proof steps verbatim. Instead of creating duplicates, I cited lem-trf-open-ctf for the intermediate domain, lem-weil-pbc-ringed-exchange-tensor-coherence for the proper-factor calculation, and lem-sf-open-tensor-normalization for the open-factor calculation. Five replacement steps state the necessary specializations and compose the two identities. The proposition statement is unchanged byte for byte as requested; no Lean record is changed. The first dry run was run before repair and stopped because the preserved sandbox had only searches.jsonl and lacked report.md. The returned full proof was therefore copied from the read-only shared node and repaired in the sandbox.

## Not duplicates
No new node is created. The proposed extension-domain lemma would duplicate lem-trf-open-ctf; the proper projection/coefficient compatibility is the ringed coefficient-square case of lem-weil-pbc-ringed-exchange-tensor-coherence. The open map argument uses the fully faithful, unit-normalized comparisons of lem-sf-open-tensor-normalization. det-sp-reduction-direct-image pins the proper/open factorization rather than asserting the item's square. lem-sp-direct-image-change-ring-transpose and lem-pur-etale-scalar-mate-projection identify a single coefficient-object projection map, not the two-variable compatibility; neither is substituted for that compatibility. The general exchange lemma explicitly permits non-Cartesian ringed squares, which is essential here.

## Review by Q65
I read coord/delivery-errors.md B-E in full, the returned node, its unit sk-prop-sf-pf-reduction and chapter sec-smooth-purity, and the current main-20261015 prop-sf-pf-reduction proof and unit paragraph. The proof requests equality of the specified maps via their counit-tensor construction, followed by invertibility from the finite projection theorem; the repair retains both requests. I also read every cited node's statement, not just its title or proof. For the imported node there is no new statement correction. The previously repaired standalone statement supplies 1 <= m <= n and the separated finite-type field-base setting through def-sf-datum.

Step 1 is retained verbatim: constructible-origin (ii) supplies bounded etale representatives, comparison-Tor (ii) supplies their Tor amplitude, and flat-model's Noetherian constructible variant supplies bounded flat constructible models. Finite-type k-schemes are Noetherian. The written termwise tensor check is over B, not a claim that B is flat over A. Comparison-Tor (i) returns the witnessed objects to the pro-etale site. Step 2 is retained verbatim: operation-reduction supplies tensor/pullback comparisons and compact-support-coefficient-change supplies c_f on bounded constructible finite-Tor inputs, exactly the displayed u,v.

Step 3 now cites the actual preservation theorem lem-trf-open-ctf, whose statement includes both constructibility and unchanged Tor interval. Nagata gives the compactification over the qcqs target. The existing open projection theorem identifies M tensor p*L with j_!(K tensor f*L), so applying preservation to the latter input (checked in step 1) gives both proper-factor domains without silently applying a tensor closure statement. Constructible-origin gives their witnesses. This replaces the first hidden argument.

Step 4 opens def-exchange-projection: its statement explicitly defines pi as the counit-tensor mate and PF as Rp_*(gamma) after pi. def-sf-pf supplies precisely this concrete interpretation. compact-support-direct-image-detailed gives the factorization and the proper compactification (id,p). det-sp-reduction-direct-image explicitly describes the B-linear proper adjoint transpose followed by extension-by-zero tensor comparison; this pins the map used in step 2. I checked that both rings are finite ell-primary, p is proper, j is open and all schemes are separated of finite type over k. No smoothness assumption is imported from the unit in which that general tool happens to occur.

Step 5 uses the statement of ringed-exchange-tensor-coherence: its two displayed composites are precisely the two routes with E=M,Q=L. Its ringed topoi have A and B on identical underlying small pro-etale topoi; the two horizontal morphisms use the ring map A -> B. Their pullback is derived scalar extension, and the commuting ring maps give the required commutation isomorphism. The lemma expressly assumes neither a Cartesian square nor flat B. This existing theorem now carries the second hidden argument, including the counit calculation, rather than treating a several-line mate computation as elementary.

Step 6 uses the statement of open-tensor-normalization with the identity scheme map but different coefficient rings. It supplies beta for scalar extension, gamma for open tensor, invertible units, and full faithfulness. Thus restriction is faithful on the essential image of j_!, and the source is in that image via beta and gamma; both restricted routes are identity maps under the cited specified identifications. The only remaining comparisons are tensor/pullback rebracketings whose coherence is expressly in operation-reduction. This gives the third hidden argument without detecting equality merely at geometric stalks. Its source records Stacks 0GL1 lemma-j-shriek-and-tensor and 0E8I lemma-j-shriek-and-tensor with the normalized refinement stated separately; no SGA route is used.

Step 7 only pastes the two established identities, using naturality and the pinned proper/open factorization. Step 8 is the original final step verbatim: it correctly distinguishes invertibility of rho(PF_A) from invertibility of PF_A; thm-sf-pf-finite at both coefficient levels and the witnessed pro-etale clause of lem-weil-finite-compact-projection-formula supply the latter. No assertion that arbitrary finite reduction is conservative is added.

I tested the specializations at m=n (identity coefficient change), j=id (only the proper square remains), p=id (only the open square remains), K=0 or L=0, and an empty open. The displayed identities reduce to identity or zero composites. For m<n, e.g. A=Z/ell^2, B=Z/ell, nothing assumes B is flat or of finite projective dimension over A. I traversed statement and proof dependencies of each added existing citation and found no path back to the item. All replacement steps are below 2000 characters; no original remaining step exceeds the bound. The new nodes initially contemplated were not written because the DAG contains the stronger results. Mathlib searches are retained as actually logged; mateEquiv_counit (Mates.lean:123) and map_mu_comp_counit_app_tensor (Monoidal/Functor.lean:1036, Unicode mu) are only ingredients, not one-line statements of the whole item. No compiler, Lake, Lean write, repository git command, or live-project write was run.

## Unfinished
None in this one-level repair; the existing cited nodes retain their own stage states.

## Original returned step 3 (retained for provenance)
The scheme $Y$ is finite type over $k$, hence quasi-compact and quasi-separated, so [thm-nagata-compactification] supplies a compactification $f=pj$. Put $M=j_!K$. Before applying coefficient comparison to $p$, check its input domain: by exactness of $j_!$ in [lem-cbc-proetale-extension-zero], $M$ is bounded, and extending a finite constructible stratification of $K$ by the closed complement, on which extension by zero is zero, shows that $M$ is constructible. For a sheaf $N$ of $A$-modules on $\overline X$, [lem-cbc-extension-zero-projection-formula] gives $M\otimes_A^L N\cong j_!(K\otimes_A^L j^{-1}N)$; exactness of $j_!$ therefore gives the same Tor interval as $K$. The tensor argument of step 1 gives the finite-Tor domain for $M\otimes_A^L Lp_A^*L$ as well. By [lem-sf-proetale-constructible-origin], these bounded constructible objects admit the required étale-origin witnesses. Thus the proper-factor coefficient comparisons below are applied on their stated domains. The definition [def-exchange-projection], with the notation [def-sf-pf], writes $\operatorname{PF}_{A}=Rp_{*,A}(\gamma_A)\circ\pi_A$, where $\gamma_A:j_!K\otimes_A^L Lp_A^*L\to j_!(K\otimes_A^L Lf_A^*L)$ is the specified open-immersion tensor isomorphism and $\pi_A$ is the transpose of $(\varepsilon_A\otimes1)\circ\mu_A$. To check the proper direct-image part, write $F_A=Lp_A^*$, $G_A=Rp_{*,A}$, and likewise at $B$, and orient the pullback comparison as $t:F_B\rho\xrightarrow{\sim}\rho F_A$. Write $c_M:\rho G_A M\to G_B\rho M$ for the coefficient comparison; for proper $p$, use the compactification $(\operatorname{id},p)$ in [def-compact-support-direct-image-detailed], so this is the compact-support comparison. Its counit compatibility in [lem-fix-compact-support-coefficient-change] and [lem-fix-operation-reduction] is the typed identity
$$
\varepsilon_{B,\rho M}\circ F_B(c_M)=\rho(\varepsilon_{A,M})\circ t_{G_AM}.
$$
After identifying the tensor and pullback targets, the transpose under $F_B\dashv G_B$ of each route in the direct-image comparison square is the following single composite:
$$
\begin{aligned}
F_B\rho(G_AM\otimes_A^L L)
&\xrightarrow{t}\rho F_A(G_AM\otimes_A^L L)
\xrightarrow{\rho\mu_A}\rho(F_AG_AM\otimes_A^L F_AL)\\
&\xrightarrow{\rho(\varepsilon_A\otimes1)}\rho(M\otimes_A^L F_AL)
\xrightarrow{s}\rho M\otimes_B^L\rho F_AL
\xrightarrow{1\otimes t_L^{-1}}\rho M\otimes_B^L F_B\rho L.
\end{aligned}
$$
For the route through $\rho\pi_A$, this follows by its defining transpose and the displayed counit identity for the target comparison. For the route through $\pi_B$, substitute the displayed identity for $\varepsilon_B\circ F_Bc_M$; coherence of $s,t,\mu$ gives exactly the written composite. The required coherence and preservation of the units and counits are explicit clauses of [lem-fix-operation-reduction]. Adjunction therefore equates these two routes. For the open-immersion factor, write $d_H:\rho j_{!,A}H\xrightarrow{\sim}j_{!,B}\rho H$, the compact-support comparison for $j$ (its compactification is $(j,\operatorname{id})$). Reduction of the specified open tensor map satisfies
$$
d_{K\otimes Lf_A^*L}\circ\rho\gamma_A
=\gamma_B\circ(d_K\otimes1)
$$
after inserting $s,t$ on the source and target. Indeed $\gamma$ is the open tensor identification of [def-exchange-projection], built from the tensor comparison and the extension-by-zero adjunction; reducing each tensor, unit and counit arrow gives the corresponding $B$-arrow by [lem-fix-operation-reduction], in the same order. Thus the two sides are the same composite, including the pullback-composition identification $Lj^*Lp^*=Lf^*$. Composing this identity with the direct-image identity proves $v\circ\rho(\operatorname{PF}_A)=\operatorname{PF}_B\circ u$, as required. As required by the warning in [lem-sf-generating-class-determination], this equality of natural transformations has been checked from the constructions; no equality is inferred merely from values on generators.
