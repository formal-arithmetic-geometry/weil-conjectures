# Worker report — NY

## Files written

- `dag/nodes/sec-trace-formula/prop-trf-rational-frobenius-integral-model.json`: repaired split; eight proof steps, unchanged statement, Lean record, audit, import flags and blueprint metadata.
- `dag/nodes/sec-trace-formula/lem-trf-frobenius-coefficient-reduction-coherence.json`: statement, unsplit; no Mathlib match. Isolates compatibility of the specified Frobenius pullback comparisons with the quotient tower and its pullback-composition comparisons.
- `dag/nodes/sec-trace-formula/lem-trf-integral-point-transport-tower-realization.json`: statement, unsplit; no Mathlib match. Isolates equality of the actual integral point transport with the realization of a coherent finite-level transport map.
- `dag/nodes/sec-trace-formula/lem-trf-completed-stalk-frobenius-reduction.json`: statement, unsplit; no Mathlib match. Isolates the completed-stalk reduction and compatibility of the normalized transport, with no coefficient endomorphism supplied.
- `citations.json`: verbatim statement excerpts for every citation of each of the eight steps.

## Attachments

None. The item's slopmaster2 audit is `none`. Searching all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id and integral-model/Frobenius terminology found no declaration stating this item or the extracted transport comparisons. The hit in EtaleCohomology/Purity/RealSheaves/LocalSystems.lean is contextual prose about stable lattices, not this arbitrary, possibly noninvertible morphism theorem. Upstream master is reference only.

## WANTED

None: the blueprint statement and proof, and the definitions of the specified maps, are available locally. This is an agent-written expansion of the main-20261015 blueprint, not a claim that a Stacks tag states these project-specific Frobenius comparisons. No SGA source is used.

## Returned fault and repair

The human return singled out original steps 2 (3473 characters), 3 (4369), and 4 (3892): they carried non-elementary inline arguments. I retained their route and extracted the three supporting lemmas listed above. The original step 1 is unchanged. The new steps (2a),(2b) retain construction of psi and the naturality induction; (3a),(3b),(3c) retain the graph evaluation, realization and scalar calculation; (4a),(4b) retain composition with the local transport, scalar calculation and the explicit lattice obstruction. Lengths are 765, 705, 788, 405, 1504, 672, 926, 1055 characters. No non-elementary step exceeds 2000 characters.

The extracted lemmas are strictly smaller than the item. None introduces a rational Frobenius morphism, a denominator N, u, psi, or its graph endomorphism, and none concludes one of the item's numbered operator assertions. The item still proves the naturality induction, applies the graph theorem, composes the actual maps, and calculates the power varpi^{-Nm}. It does not merely apply new names for its four clauses.

I continued the retained sandbox rather than discarding it. Its statement agrees byte for byte with both the returned-head copy retained at the sandbox root and the current shared repository. The current repository still has the returned four-step proof. Its Lean and audit records agree with the repaired copy. The existing Mathlib search log and searches in the node files are retained; the successful search signatures and top results were read, including second phrasings, and no unrun query was invented. Earlier unavailable/invalid attempts remain distinguished in the retained log.

Two precision corrections already made in this retained repair are preserved: the recursion for arbitrary u is taken from the displayed formula in the item rather than applying an isomorphism-only Weil-map definition; the reduction tower of Ra_!K is compared with the compact-support output tower by lem-fix-operation-reduction before applying the point-transport lemma. The stalk lemma now says explicitly that finite-level pullback is along the same geometric point.

## Not duplicates

lem-trf-frobenius-coefficient-reduction-coherence vs prop-trf-scheme-galois-comparison: the latter supplies the natural multiplicative comparison separately for each finite coefficient ring, but does not assert its coherence across coefficient quotients or the completed-to-finite comparison.
lem-trf-frobenius-coefficient-reduction-coherence vs lem-pur-integral-operations-preserve-constructible: that statement supplies individual integral pullback reductions, not quotient coherence of the specified Frobenius trivialization and its powers.
lem-trf-frobenius-coefficient-reduction-coherence vs lem-fix-operation-reduction: that statement supplies operation comparisons and compatibility with evaluations, units and counits, not compatibility of the specific site-induced absolute-Frobenius trivialization kappa across coefficients.
lem-trf-frobenius-coefficient-reduction-coherence vs thm-trf-finite-coefficient-map: that theorem supplies finite-ring operation changes and equivariance of operators for an invertible strict Weil structure; the new lemma supplies the coefficient-free comparison kappa and completed-to-finite pullback coherence without a Weil structure.
lem-trf-integral-point-transport-tower-realization vs def-weil-frobenius-point-transport: the definition specifies the maps; it explicitly leaves assertions about their properties to theorems, and does not identify the integral map with realization of a map between coherent quotient towers.
lem-trf-integral-point-transport-tower-realization vs lem-weil-frobenius-point-transport-natural: naturality at each coefficient stage does not supply equality with the realized tower morphism across those stages.
lem-trf-integral-point-transport-tower-realization vs def-weil-inverse-image-pullback-comparison: part (b) specifies a cone map for completed pullback; it does not identify point sections of that map with realization of the finite point transports on the reduction tower.
lem-trf-completed-stalk-frobenius-reduction vs lem-pod-point-sections-derived-reduction: that theorem supplies the natural comparison of point sections with a single integral quotient; it says nothing about the normalized Frobenius transport.
lem-trf-completed-stalk-frobenius-reduction vs lem-trf-point-sections-finite-reduction: that theorem concerns finite-to-finite quotients; it does not compare the completed integral fiber or the normalized transport.
lem-trf-completed-stalk-frobenius-reduction vs prop-trf-adic-coefficient-morphism-systems: the latter assumes compatible coefficient morphisms and discusses endomorphism lifts, traces and operator compatibility. It uses this item as its rational-integral example and normalization. The new statement concerns the underlying stalk transport without a coefficient morphism; using the adic-systems proposition here would introduce a backward dependency.
lem-trf-completed-stalk-frobenius-reduction vs def-trf-frobenius-operators: the definition specifies the finite transport via fixed-point pullback and kappa; it does not prove its completed-to-finite reduction compatibility.

The whole-DAG and whole-blueprint searches used point transport, coefficient reduction, completed stalk, pullback reduction, Frobenius comparison and point sections. The search hits above were opened, not treated as matches from their names. No new node has a Stacks tag shared with another node: their source is an extracted argument in the blueprint proof. All three have the item's blueprint ancestor and empty via/same_as; no blueprint statement was found that states the same supporting comparison.

## Tool uses

The retained accepted tool_uses are unchanged. The split_report declares the actually used generic rational transport, scheme/Galois comparison, Frobenius factorization, coherent compact-support tower lift and operation-reduction comparison. The tower lift supplies an actual morphism in the derived category of towers, not an arbitrary inverse sequence of classes. The operation-reduction comparison identifies the input tower needed by the point-transport lemma. These do not replace the unit's Frobenius/graph route.

## Review by NY

I read the main-20261015 sk-d-weil unit and the item statement and proof, especially clauses (2), (3), (4), as well as the unchanged returned proof. The chapter and unit route remain scheme Frobenius, comparison with geometric Galois Frobenius, graph correspondence, then global and stalk operators. The coefficients stay modules over the completed integral sheaf at the integral stage, finite constant coefficients at A_n, and the raw scalar localization at E. No Karoubi completion or constant/completed integral category identification is introduced. I compared the eight steps with the statements of all 18 distinct cited nodes.

Step 1 uses the literal Hom tensor E formula in def-weil-rationalization-karoubi and the extension of the supplied integral pullback in prop-weil-pbc-rational-transport. The finite-sum denominator calculation is written in the step; it uses neither torsion-freeness nor a stable invertible lattice. The empty sum takes N=0.

Step 2 uses the equality Fr_X^{(q)}=g_sigma Phi in prop-trf-frobenius-factorization and the convention gamma=sigma^{-1} in def-trf-scheme-frobenius to obtain the correct comparison orientation. prop-trf-scheme-galois-comparison applies because A_n is finite and ell-primary, with ell different from p. def-weil-pbc-adic-coefficient-datum supplies the functorial quotient tower on completed coefficients, including maps. The new coherence lemma supplies the exact compatibility across quotients which these individual finite comparisons do not state. The output is an arbitrary map L Phi^*K_n -> K_n, precisely the notion in def-trf-frobenius-coefficient-morphism. Its finite-Tor hypothesis is the item's assumption on K_n. Here the adic datum is specialized to A=O_E, I=(varpi); its quotients are finite and perfect over O_E.

Step 3 uses the recursion in def-trf-frobenius-coefficient-morphism, naturality and multiplicativity in prop-trf-scheme-galois-comparison, and pullback-composition coherence in the extracted lemma. I checked the source and target at u_n^{[m-1]}; naturality moves it through kappa, and multiplicativity combines the remaining comparison factors. The base m=1 and the induction step are explicit. The integral iterate is defined in the item's displayed composite, so no invertible Weil structure is assumed.

Step 4 uses the definition of F_{c,m} and the arbitrary-v clause of prop-trf-graph-frobenius-operator. I opened that clause: it explicitly allows no Weil structure and a noninvertible v. This is important for u_n. Substituting the identity from step 3 gives the finite formula, with K_n in D^b_ctf as required.

Step 5 uses the exact linear tower functor, including its statement about transitions and morphisms, in lem-weil-compact-support-reduction-tower-functor. Its hypothesis is satisfied by a_X:X -> Spec k, a separated finite-type morphism with ell invertible. One compactification is fixed over k_0 and used at every level. def-weil-integral-rational-qbar-compact-support supplies realization and bounded integral constructibility. def-weil-frobenius-square-exchange (2) specifies the integral exchange as realization of the particular system mate, rather than merely a map with matching individual evaluations. lem-fix-operation-reduction supplies the input/output reduction comparisons and their compatibility with the exchange transformations. The new point-transport realization lemma identifies the other factor for N=Ra_!K. This N is derived-complete bounded constructible by the compact-support statement; the point lemma does not require that N_n be given an invertible Weil structure. def-weil-frobenius-cohomology-transport specifies the two factors, and def-trf-frobenius-operators specifies the m-fold composite. Its transport formula is coefficient-independent and makes no use of the Weil isomorphism; the operator input u is supplied only afterward. The new coherence lemma supplies the remaining pullback comparisons. Functoriality of realization then preserves this finite composite. Thus the long hidden comparison is now a cited lemma, and the argument remaining in the item assembles specified system maps. I do not infer equality of derived maps from equality of their individual reductions.

Step 6 uses E-linearity in prop-weil-pbc-rational-transport, bilinear composition in the raw localization of def-weil-rationalization-karoubi, and the rational compact-support object in def-weil-integral-rational-qbar-compact-support. There are exactly m factors, each with scalar varpi^{-N}; their product is varpi^{-Nm}. All transports and composition maps are the rationalizations specified in the item's hypotheses. No assertion of constructibility for an arbitrary morphism is deduced from the generic rational transport theorem.

Step 7 first substitutes the already proved iterate into the stalk normalization in the item's hypotheses. The new stalk lemma identifies the completed point fiber's reductions and the reduction of the specified normalized transport, naturally in K. It applies to the rational point lift fixed by Phi^m and to the integral object of the item, whose finite reductions have the required finite Tor amplitude. The remaining composition with u is elementary functoriality. def-weil-finite-coefficient-point (3) explicitly makes the E fiber the tensor extension of the integral fiber on objects and morphisms. prop-weil-pbc-rational-transport supplies linearity of completed pullback. The scalar formula follows from the same m-factor calculation as step 6.

Step 8 uses only linearity from prop-weil-pbc-rational-transport plus the explicit coordinate argument that is written out. The bounds varpi^b O_E^2 subset L subset varpi^{-b} O_E^2 follow by bounding generators and clearing two sets of coordinates of a basis of E^2 drawn from L. Bijectivity makes every positive and negative iterate preserve L. Applied to the two basis lines, the resulting valuation inequalities force v(c)=v(c ell)=0, impossible since v(ell)>0. This remains valid for ramified E; there is no imported characteristic-polynomial or eigenvalue-integrality theorem hidden in the step.

For lem-trf-frobenius-coefficient-reduction-coherence I read blueprint clause (2) and the statements of def-weil-pbc-adic-coefficient-datum, def-weil-derived-pullback-tensor-hom, lem-pur-integral-operations-preserve-constructible, prop-trf-scheme-galois-comparison, lem-trf-absolute-frobenius-site and prop-trf-frobenius-factorization. The lemma isolates the site's specified comparison, not an arbitrary natural isomorphism allowed to vary by scalar at each n. Its hypotheses introduce X, the coefficient ring, the integral object and each reduction. Equality for b=a is the identity comparison; for b>a the coherence question is genuinely additional to individual reduction isomorphisms. The standard route is balancing the quotient tensor maps and applying the fixed site-induced trivialization; that proof is left to the new node's future split, not embedded in its statement.

For lem-trf-integral-point-transport-tower-realization I read blueprint clause (3), def-weil-frobenius-point-transport and the full integral cone construction in def-weil-inverse-image-pullback-comparison (b). The finite map is restriction of sections followed by x -> x tensor 1. The integral definition is the particular cone lift z -> (0,theta(z)), after the chosen K-flat resolution. Its equality with the realized tower map is a substantive assertion, not uniqueness from reductions. The statement supplies this equality and naturality while introducing s, g_s, N and N_n independently of X or u. A future proof follows the products/cone model for completeness and termwise exact point evaluation; the proof remains outside the unsplit statement.

For lem-trf-completed-stalk-frobenius-reduction I read blueprint clause (4), the fixed-point formulas in def-trf-frobenius-operators, lem-pur-integral-operations-preserve-constructible and lem-pod-point-sections-derived-reduction. The last theorem is the already existing integral-to-finite point sections comparison; I did not create another node for it. The new assertion is reduction of the normalized transport, not merely reduction of the underlying fiber. Its hypotheses include the actual fixed point and completed pullback. The future argument compares pullback to the point, applies the point-sections reduction, and then the fixed site-induced kappa and pullback-composition comparison on the same coherent tower. Again only the statement is delivered for that future split.

All three new nodes have proof=[], proof_deps=[], proof_origin=null and status unsplit. Their statements use named definition interfaces for coefficients, completed categories, pullbacks and point fibers; the theorem interfaces are used only to name specified canonical comparisons. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files. No source claim is silently weakened; no invented Stacks tag or unavailable-service no-match is recorded. The Mathlib signatures are generic module pullbacks, naturality, mapping-cone lifts, limit preservation, Zariski stalks or Witt-vector Frobenius, rather than these completed coefficient comparisons. The searches have genuine logged query/tool pairs and second phrasings. There is no new Mathlib leaf.

Small cases checked: K=0 and N=0 give zero maps with coherent reductions; u=0 and m=1 are covered without invertibility; n=1 and b=a give the identity quotient comparison; empty X gives the zero compact-support tower and no local-point assertion; X_0=Spec F_q with a constant free complex reduces the new comparisons to the ordinary coefficient quotient maps. These cases do not contradict any new statement. The new lemmas contain no denominator, so the choice N=0 for the rational zero morphism causes no special transport case. The unit and target statements are unchanged.

## Unfinished work

No repair point is intentionally left open. The three new lemmas are statement-only stage-1 children for later splitting and stage 2, as required. Server dry-run and delivery outcomes are recorded below when available.

## Retained returned proof

The original four-step proof is retained here verbatim so the extracted arguments and route remain available to the maintainer and later workers.

### Original step 1

*(1).* By [def-weil-rationalization-karoubi] the morphisms of
$D^b_c(X,E)$ are
$\operatorname{Hom}_{D^b_c(X,\mathcal O_E)}(Lg_\gamma^*K_{\mathcal O},K_{\mathcal O})\otimes_{\mathcal O_E}E$,
the rationalized pullback being that of the integral one
([prop-weil-pbc-rational-transport]). Since $E=\mathcal O_E[1/\varpi]$,
every element of $H\otimes_{\mathcal O_E}E=H[1/\varpi]$, for an
$\mathcal O_E$-module $H$, has the form $u\otimes\varpi^{-N}$ with
$u\in H$ and $N\geq0$. Explicitly, write a tensor element as a finite sum $\sum_j h_j\otimes(a_j/\varpi^{e_j})$, choose $N=\max_j e_j$ (take $N=0$ for an empty sum), and put $u=\sum_j a_j\varpi^{N-e_j}h_j$. Balancing gives $\sum_j h_j\otimes(a_j/\varpi^{e_j})=u\otimes\varpi^{-N}$. This is $\varphi_E=\varpi^{-N}u$.

Uses: def-weil-rationalization-karoubi, prop-weil-pbc-rational-transport

### Original step 2

*(2).* Use the current construction of [def-trf-scheme-frobenius]: on a base-changed affine chart the model Frobenius is $a\otimes b\mapsto a^q\otimes b$, while $g_\gamma$ acts on the scalar factor through $\gamma=\sigma^{-1}$. The factorization statement [prop-trf-frobenius-factorization], with $m=1$, gives $F_X^{(q)}=g_\sigma\circ\Phi$; composing on the left with $g_\gamma=g_\sigma^{-1}$ gives $\Phi=g_\gamma\circ F_X^{(q)}$. This fixes the orientation of the comparison used below. Each finite ring $A_n$ is annihilated by a power of $\ell$, invertible in $k$ because $\ell\neq p$, so the finite-coefficient hypothesis of [prop-trf-scheme-galois-comparison] holds at every level.

The reduction $u_n$ is the $n$-th evaluation of the morphism of
towers attached to $u$ by the functorial reduction tower of
[def-weil-pbc-adic-coefficient-datum], using
$(Lg_\gamma^*K_{\mathcal O})\otimes^L A_n\cong Lg_\gamma^*K_n$: the displayed reduction comparison is the canonical comparison in clause (1) of [lem-pur-integral-operations-preserve-constructible], applied to $g_\gamma$ and $K_{\mathcal O}$. The finite pullback is the exact termwise inverse image described in [def-weil-derived-pullback-tensor-hom]. For a coefficient quotient $A_b\to A_a$, its tensor normalization sends $(x\otimes r)\otimes s$ to $x\otimes q_{b,a}(r)s$; inverse image carries this formula to the identical formula on the pulled-back coefficients. Thus the canonical comparisons commute with transitions and normalization. Hence the $u_n$ are compatible with
the transitions. The isomorphism $\kappa$ of
[prop-trf-scheme-galois-comparison] is composed of the functoriality of
pullback for $\Phi=g_\gamma F_X^{(q)}$ and the trivialization of
absolute-Frobenius pullback of [lem-trf-absolute-frobenius-site], which is
induced on the pro-etale site itself; the first is a composition comparison, while the second is the canonical site-level trivialization of the cited lemma. Applying any coefficient quotient before or after restriction along this same site isomorphism gives the same map on sections: the quotient changes only coefficients and the site isomorphism changes only the site argument. The balancing formula just given then shows that these maps commute with derived coefficient reduction. Hence the comparison $\kappa$ is compatible with the reduction transitions, without requiring a Weil structure.
Therefore $\psi_n=u_n\circ\kappa_{K_n}$ is a morphism
$L\Phi^*K_n\to K_n$, i.e. a Frobenius coefficient morphism, and the
$\psi_n$ are compatible with the transitions.

For the iterates argue by induction on $m$, the case $m=1$ being the
definition. Suppressing the composition isomorphisms of pullback (they
are part of both recursive definitions), the recursion of
[def-trf-frobenius-coefficient-morphism] and the induction hypothesis
give

$$
\psi_{n,m}=\psi_n\circ L\Phi^*\psi_{n,m-1}
=u_n\circ\kappa_{K_n}\circ L\Phi^*\bigl(u_n^{[m-1]}\bigr)\circ
L\Phi^*\bigl(\kappa^{(m-1)}_{K_n}\bigr).
$$

Naturality of $\kappa$ applied to
$u_n^{[m-1]}:Lg_\gamma^{(m-1)*}K_n\to K_n$ gives
$\kappa_{K_n}\circ L\Phi^*(u_n^{[m-1]})
=Lg_\gamma^*(u_n^{[m-1]})\circ\kappa_{Lg_\gamma^{(m-1)*}K_n}$, and the
multiplicativity of the iterates in [prop-trf-scheme-galois-comparison],
for $m=1+(m-1)$, gives
$\kappa_{Lg_\gamma^{(m-1)*}K_n}\circ L\Phi^*(\kappa^{(m-1)}_{K_n})
=\kappa^{(m)}_{K_n}$. Hence
$\psi_{n,m}=u_n\circ Lg_\gamma^*(u_n^{[m-1]})\circ\kappa^{(m)}_{K_n}
=u_n^{[m]}\circ\kappa^{(m)}_{K_n}$.

Uses: def-trf-scheme-frobenius, prop-trf-frobenius-factorization, def-weil-pbc-adic-coefficient-datum, def-weil-derived-pullback-tensor-hom, prop-trf-scheme-galois-comparison, lem-trf-absolute-frobenius-site, def-trf-frobenius-coefficient-morphism, lem-pur-integral-operations-preserve-constructible

### Original step 3

*(3).* The first equality is the definition of $F_{c,m}(\psi_n)$ in
[def-trf-frobenius-coefficient-morphism]. By (2),
$\psi_{n,m}=v\circ\kappa^{(m)}_{K_n}$ with $v=u_n^{[m]}$, and the general
clause of [prop-trf-graph-frobenius-operator], which allows an arbitrary,
not necessarily invertible $v$ and no Weil structure on $K_n$, gives
$T_{c_m}(\psi_{n,m})=R\Gamma_c(X,u_n^{[m]})\circ g_{\gamma,c}^{m,*}$.

By [def-weil-integral-rational-qbar-compact-support],
$R\Gamma_c(X,-)$ on $D^b_c(X,\mathcal O_E)$ is the derived limit of the
levelwise compact-support cohomology of the reduction tower of
[def-weil-pbc-adic-coefficient-datum]; on morphisms this uses the exact linear tower lift of [lem-weil-compact-support-reduction-tower-functor], whose evaluations are the levelwise compact-support maps and whose transition comparisons compose compatibly. Thus the derived limit is applied to a morphism of the tower, not to an arbitrary collection of morphisms in separate derived categories. The integral morphism $u^{[m]}$ (formed from
$u$ by the integral pullbacks) has reductions $u_n^{[m]}$, because
$Lg_\gamma^{i*}$ commutes with the reductions as in (2); and the integral base-change map is the limit of a specified system map: item (2) of [def-weil-frobenius-square-exchange] defines the integral compact-support exchange as $\beta_!\circ\mathcal L_Y(e_f^c)\circ\alpha_!$, using the same compactification at every level. Apply it to $f_0=a_{X_0}$; this is a separated finite-type morphism, although the horizontal automorphisms are semilinear. The compact-support transport of [def-weil-frobenius-cohomology-transport] composes that exchange with the point transport of [def-weil-frobenius-point-transport]. For its integral comparison with completed pullback, use part (b) of [def-weil-inverse-image-pullback-comparison]: on a K-flat representative $P$ the map into $\operatorname{Cone}(1-s)[-1]$ is $z\mapsto(0,(\theta_n(z))_n)$, where $\theta_n$ is reduction followed by the finite coefficient comparison and $t_n\theta_{n+1}=\theta_n$. The restriction map defining the point transport sends a section to its restriction along $g_s$ and then to the inverse-image colimit; reduction of its coefficient before this restriction or afterwards gives the same section. Consequently, after the canonical completeness identification, this map into the cone is induced by the finite point transports on the single quotient tower, including its transitions. The point fiber is exact termwise evaluation at the final object by [def-weil-finite-coefficient-point]. Evaluation preserves products, since sheaf products are computed sectionwise, and preserves finite sums and differentials; it therefore sends the displayed shifted cone of $1-s$ to the shifted cone of the evaluated $1-s$. Thus the integral point transport is the derived limit of these levelwise maps on coefficient complexes. Finally [def-trf-frobenius-operators] defines $g_{\gamma,c}^{m,*}$ as the composite of $m$ such transports and the pullback-composition comparison. A functor preserves this finite composite. Thus the integral $g_{\gamma,c}^{m,*}$ is the derived limit of the levelwise ones, the pullback $Lg_\gamma^{m*}$ carrying the reduction tower of $K_{\mathcal O}$ to that of $Lg_\gamma^{m*}K_{\mathcal O}$. Hence
$U_m$ is the derived limit of the levelwise composites
$R\Gamma_c(X,u_n^{[m]})\circ g_{\gamma,c}^{m,*}=F_{c,m}(\psi_n)$.

At the stage $E$, $R\Gamma_c(X,K_E)=R\Gamma_c(X,K_{\mathcal O})\otimes_{\mathcal O_E}E$
([def-weil-integral-rational-qbar-compact-support]), and every
rationalized functor or natural transformation acts on
$\operatorname{Hom}\otimes_{\mathcal O_E}E$ by $f\otimes\lambda\mapsto
F(f)\otimes\lambda$ ([prop-weil-pbc-rational-transport]); composition in
$D^b_c(X,E)$ is $E$-bilinear. Hence
$L(g_\gamma^{i})^*\varphi_E=\varpi^{-N}\,L(g_\gamma^{i})^*u$ for each $i$,
the composition isomorphisms are those of the integral pullbacks, and

$$
\varphi_E^{[m]}=\prod_{i=0}^{m-1}\varpi^{-N}\cdot
\bigl(u\circ Lg_\gamma^*u\circ\cdots\circ L(g_\gamma^{m-1})^*u\bigr)
=\varpi^{-Nm}u^{[m]}.
$$

Applying the $E$-linear map induced by the rationalized $R\Gamma_c(X,-)$
and composing with the rationalization of the integral
$g_{\gamma,c}^{m,*}$ gives
$F_{c,K_E}^{\,m}=\varpi^{-Nm}\bigl(R\Gamma_c(X,u^{[m]})\circ g_{\gamma,c}^{m,*}\bigr)\otimes E
=\varpi^{-Nm}(U_m\otimes E)$.

Uses: def-trf-frobenius-coefficient-morphism, prop-trf-graph-frobenius-operator, def-weil-integral-rational-qbar-compact-support, def-weil-pbc-adic-coefficient-datum, prop-weil-pbc-rational-transport, lem-weil-compact-support-reduction-tower-functor, def-weil-frobenius-square-exchange, def-weil-frobenius-cohomology-transport, def-weil-frobenius-point-transport, def-trf-frobenius-operators, def-weil-inverse-image-pullback-comparison, def-weil-finite-coefficient-point

### Original step 4

*(4).* By the stalk normalization and (2),
$\psi_{n,m,\bar y}=(u_n^{[m]})_{\bar y}\circ(\kappa^{(m)}_{K_n})_{\bar y}\circ\iota_{K_n}
=u^{[m]}_{n,\bar y}\circ\tau_{y,m}$. Here the integral stalk coefficient complex is $\operatorname{Fib}_s(L\bar y^*K_{\mathcal O})$, with completed pullback as in [def-weil-derived-pullback-tensor-hom] and exact point evaluation as in [def-weil-finite-coefficient-point]. Clause (1) of [lem-pur-integral-operations-preserve-constructible], with $f=\bar y$, identifies the reductions of this completed pullback with $L\bar y_n^*K_n$. Point evaluation commutes with reduction: the coefficient sheaf $\widehat{\mathcal O}_{E,s}=\varprojlim_r(A_r)_s$ has no $\varpi$-torsion, since $\varpi a=0$ makes the component $a_{r+1}$ divisible by $\varpi^r$, hence $a_r=0$ for every $r$. The projection to $(A_n)_s$ is locally surjective by constant lifts; its kernel is $\varpi^n\widehat{\mathcal O}_{E,s}$, by dividing the compatible residues $a_{r+n}$ by $\varpi^n$. Thus the two-term free uniformizer resolution computes reduction as the cone of $\varpi^n$; exact termwise evaluation preserves that cone and multiplication by $\varpi^n$. Thus the reductions of the integral stalk coefficient complex are the finite stalk coefficient complexes. This uses the completed pullback construction, without interchanging an ordinary sheaf stalk with an arbitrary inverse limit.

For the transport, the fixed-point identification $\Phi^m\bar y=\bar y$ is an equality of scheme maps independent of the coefficient ring, so its induced pullback-composition identification $\iota$ commutes with every coefficient quotient. The comparison $\kappa^{(m)}$ is the finite composite of the comparisons in (2), each of which commutes with the quotients by the section-balancing calculation there. The two factors in $\tau_{y,m}=(\kappa^{(m)})_{\bar y}\circ\iota$ therefore commute with those quotients, and the integral transport is their specified derived limit in the statement's stalk normalization. Reduction is a functor, so reduction of $u^{[m]}_{\bar y}\circ\tau_{y,m}$ is $(u_n^{[m]})_{\bar y}\circ\tau_{y,m}=\psi_{n,m,\bar y}$. This proves the assertion about $U_{y,m}$.

At the stage $E$ the point fiber is $\Gamma(s,-)\otimes_{\mathcal O_E}E$, with morphisms extended linearly by [def-weil-finite-coefficient-point]; the completed pullback extends linearly by [prop-weil-pbc-rational-transport]. The identity already proved in (3), $\varphi_E^{[m]}=\varpi^{-Nm}u^{[m]}$, consequently gives $\varphi^{[m]}_{E,\bar y}=\varpi^{-Nm}(u^{[m]}_{\bar y}\otimes E)$. The rational transport is $\tau^{\mathrm{int}}_{y,m}\otimes E$ by the stipulated normalization. Bilinearity of composition now gives
$$
F_{y,m}=\bigl(\varpi^{-Nm}(u^{[m]}_{\bar y}\otimes E)\bigr)\circ(\tau^{\mathrm{int}}_{y,m}\otimes E)
=\varpi^{-Nm}\bigl((u^{[m]}_{\bar y}\circ\tau^{\mathrm{int}}_{y,m})\otimes E\bigr)
=\varpi^{-Nm}(U_{y,m}\otimes E).
$$

The remark on $(N+1,\varpi u)$ is $(\varpi u)^{[m]}=\varpi^mu^{[m]}$, by
$\mathcal O_E$-linearity of the pullbacks. In the example, take the constant free integral object on $X=\Spec k$ with point fiber $\mathcal O_E^2$ and coefficient map $u=\operatorname{diag}(1,\ell)$. If $T=c\,\varphi_E$ preserved a lattice $L$ bijectively, choose $b\geq0$ such that $\varpi^b\mathcal O_E^2\subset L\subset\varpi^{-b}\mathcal O_E^2$: the upper inclusion follows by bounding the coordinates of finitely many lattice generators, and the lower by expressing the standard basis in an $E$-basis chosen from $L$ and clearing its finitely many denominators. For every integer $j$, $T^j(\varpi^be_1)=\varpi^bc^je_1$ and $T^j(\varpi^be_2)=\varpi^b(c\ell)^je_2$ belong to $L$. Thus $b+jv(c)\geq-b$ and $b+jv(c\ell)\geq-b$ for all $j\in\mathbf Z$, forcing $v(c)=v(c\ell)=0$. This contradicts $v(\ell)>0$. This works for every finite $E/\mathbf Q_\ell$, including ramified extensions.

Uses: def-weil-derived-pullback-tensor-hom, lem-pur-integral-operations-preserve-constructible, prop-weil-pbc-rational-transport, def-weil-finite-coefficient-point
