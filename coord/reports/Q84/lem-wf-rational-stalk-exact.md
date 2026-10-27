# Worker report — Q84 repair

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-wf-rational-stalk-exact.json: existing statement unchanged; three-step assembly.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-common-stage-weil-iterate.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-common-stage-point-return.json: statement, unsplit, no Mathlib match.
- citations.json: verbatim quotations for every citation of the parent proof.

## Attachments

None. Read the live library by tag and by rational/stalk/local-Frobenius concepts. Sheaf.Paper.RationalStalkExact.wfRationalStalkExact (namespace WeilConjectures) ends in sorry. No declaration under WeilConjectures proves every clause. No Lean was written or compiled.

## Wanted

None. The sources used are present.

## What was wrong and what changed

The released repair note orders at least two new nodes, statement-only, and an assembly proof at most 3000 characters. The sandbox initially contained only dispatcher marker files, not retained nodes, reports or searches. I therefore copied the current repository item, including all prior metadata and searches; the live proof is the returned four-step argument. The item statement and stmt_deps remain byte-for-byte unchanged as JSON values. The old proof had conflated the two descent arguments in its long last step. Its Weil-iterate half is assigned to the first new node and its point-return half to the second. Exact fibre Step 1 is retained with its existing stronger citation. No new exactness node or node for the full conclusion was introduced.

## Remaining work

The two new nodes are intentionally unsplit. Their proofs are work for subsequent parallel workers, as expressly required by the human re-split order. They have no proof steps or proof dependencies.

## Review by Q84

I read the chapter and energy unit and retained the route through the punctual Frobenius-stable fibre filtration, not a trace-formula replacement. For the item I read Bhatt–Scholze Corollary 6.8.5 (kernels/cokernels of lisse sheaves), Lemma 6.8.7 (constructible kernels/cokernels), Proposition 6.8.14 (coefficient-category comparison) and Remark 6.8.15 (pullback); these support the existing exact coefficient-fibre lemma, not arbitrary pro-etale stalk exactness. I also read the current lem-wf-l2-upper.proof.md opening punctual-bounds argument and prop-trf-karoubi-independence.proof.md final sentence. The new common-stage claims are agent-extracted details required for those uses, not purported verbatim theorems of those sources.

For new lem-wf-common-stage-weil-iterate I read the entire statements of def-weil-algebraically-closed-coefficients, def-weil-weil-sheaf-complex, def-weil-local-frobenius-trace and lem-trf-integral-pullback-comparison-realization. They specify eventual equality, pairs with invertible structures, the actual positive-iterate recursion, and the scalar/composition normalization including finite iterations and towers. I compared the existing finite-stage naturality and coefficient-extension lemmas in sec-fourier-transform: they give the finite identities but do not assert common-stage simultaneous realization, representative independence of the iterated structures, or its naturality on the literal pair category. The proposed proof must represent finitely many arrows and equations, choose a common field, enlarge to realize inverse and intertwining equations, use the iterate induction, and descend using the specified mixed scalar squares. The full original calculation is preserved below.

For new lem-wf-common-stage-point-return I read the entire statements of lem-weil-frobenius-point-transport-natural, lem-pod-integral-pullback-composition, lem-trf-local-frobenius-transport-normalization and lem-trf-integral-pullback-comparison-realization. Point-transport naturality (2) is on all morphisms. The return normalization explicitly states the finite-stage naturality and scalar equation for t, identifies the same normalized J, and includes identity/tower identifications. The realization lemma supplies equality-of-scheme-map and finite-iterate compatibility. These are the inputs needed to descend the whole point-complex functor and its return transformation. That latter conclusion is not asserted in the finite-stage nodes. I checked the direction of b and d: J has target P(T^n K), so P_M(d) b_(T^n K) (J tensor M) and J_M b_K have exactly the same source and target. The full original scalar equation and its use for F are retained below.

Parent Step 1 uses precisely lem-dl-a1-constructible-fibres-exact and def-weil-constructible-heart: the former explicitly includes finite-dimensional exact coefficient fibres and the Weil forgetful case; the latter is exactly the heart in the item's statement. All its hypotheses hold: separated finite type, the fixed finite-field datum and ell distinct from p. Parent Step 2 uses exactly the displayed common-stage iterate identity in the first new statement and the displayed common-stage J identity in the second; they quantify arbitrary Weil morphisms and underlying morphisms respectively. The closed point supplies n=e>=1 and the required rational point by its residue embedding. Parent Step 3 cites the actual composite formula in def-weil-local-frobenius-trace, uses the two already-established equations, and applies H^0 functorially. It makes no unproved assertion that a definition alone supplies coefficient compatibility. Every cited statement was opened, every citation has a verbatim quote, and all non-elementary content is assigned to the cited statements.

I checked edge cases: zero objects and zero/noninvertible arrows (no inverse of u is used); degree-one closed points (one-step base case); E=M and three-field towers (explicit unit/tower clauses); general bounded complexes in the two new nodes (no heart assumption or reduction Tor-amplitude silently added); and the semilinear equality g_Y^e xbar=xbar g_s^e instead of literal point fixation. Neither new lemma implies exact fibres or the parent's conjunction by itself. Both have independent hypotheses and conclusions and are comparable in scope. I checked B–E: self-contained statements, TeX once, notions attached to their definitions, genuine logged searches with a second phrasing, no Mathlib one-line match, no source-as-citation, no circular reference to this item, and no SGA source. The proof has no long step over 2000 characters.

## Not duplicates

lem-wf-common-stage-weil-iterate vs lem-fd-local-frobenius-weil-morphism-naturality: finite-stage naturality only; the new statement adds realization of finite Weil diagrams and descent of iterated structures to arbitrary common-stage pairs and arrows.

lem-wf-common-stage-weil-iterate vs lem-fd-local-frobenius-coefficient-extension: finite-stage scalar equations only; the new statement asserts representative-independent iterates and naturality after common-stage descent, not just an E-to-M comparison.

lem-wf-common-stage-weil-iterate vs det-sp-qbar-finite-descent: generic finite diagrams in an assumed 2-colimit; it does not supply iterated Weil structures with actual normalized pullback/scalar comparison and naturality.

lem-wf-common-stage-weil-iterate vs lem-weil-pbc-filtered-colimit-categories: generic categorical construction; no actual Frobenius pullback or specified iterate/scalar coherence.

lem-wf-common-stage-weil-iterate vs def-weil-weil-sheaf-complex: definition of a single structure and morphism square; does not prove finite diagram realization or scalar-compatible natural iterates.

lem-wf-common-stage-point-return vs lem-trf-local-frobenius-transport-normalization: finite/integral/rational E stages only; the new statement descends the actual point-complex functor and J transformation through the literal coefficient Hom colimits.

lem-wf-common-stage-point-return vs lem-fd-local-frobenius-weil-morphism-naturality: finite-stage naturality only; no common-stage functor/transformation representative independence.

lem-wf-common-stage-point-return vs lem-fd-local-frobenius-coefficient-extension: finite E-to-M comparison only; no descent of functor and J for all common-stage objects and arrows.

lem-wf-common-stage-point-return vs lem-weil-frobenius-point-transport-natural: single-step point transport on Spec(k); the new statement treats arbitrary geometric-point pullback and n-fold semilinear return with the specified mixed comparison.

lem-wf-common-stage-point-return vs lem-trf-frobenius-transports-scalar-extension: compact-support/global Frobenius transport, not a geometric-point return transformation.

lem-wf-common-stage-point-return vs lem-fd-common-stage-comparison-descent: comparison of two coefficient frameworks and their equivalences, not descent of the point fibre and semilinear return within this framework.

## Argument preservation and handoff

The following is the complete old proof text, retained verbatim to avoid losing any argument. Step 1 remains in the parent. In Step 2 the finite-stage realization and iterate induction belong to lem-wf-common-stage-weil-iterate. In Step 3 naturality of J belongs to lem-wf-common-stage-point-return; multiplication giving local-operator intertwining is now Parent Step 3. In Step 4 the composition/scalar equation for theta iterates belongs to the first new node, while the equation for J and its identity/tower descent belong to the second. The final b_K(F tensor M)=F_M b_K is the explicit consequence of those two factors, still required by the parent assembly; no argument is dropped. Existing finite-stage nodes can discharge their portions.

### Original step 1

Write $s=\operatorname{Spec}k$, and let $0\to\mathcal F\xrightarrow{i}\mathcal G\xrightarrow{j}\mathcal H\to0$ be the given short exact sequence. Apply [lem-dl-a1-constructible-fibres-exact] at $\bar x:s\to Y$: its statement uses exactly the heart [def-weil-constructible-heart] in the question, computes fibres by derived pullback and the point-fibre functor, and explicitly includes constructible Weil sheaves after forgetting their structure. Its hypotheses hold because $Y_0$ is separated of finite type over $k_0$ and $\ell\ne p$. It gives a short exact sequence $0\to\mathcal F_{\bar x}\xrightarrow{i_{\bar x}}\mathcal G_{\bar x}\xrightarrow{j_{\bar x}}\mathcal H_{\bar x}\to0$ of finite-dimensional $\Qlb$-vector spaces. These are the rational coefficient fibres specified in the question; no assertion about arbitrary pro-etale sheaf stalks is being used.

### Original step 2

Let $u:(K,\theta_K)\to(L,\theta_L)$ be either Weil morphism. All its data, the inverse Weil maps and their equations are represented over a common finite coefficient field $E$, after enlarging it: there are finitely many arrows and equations, and equality in [def-weil-algebraically-closed-coefficients] means equality after further finite extension. Work at this rationalized $E$-stage first. Put $T=Lg_Y^*$ and $e=[\kappa(x):k_0]\ge1$. By [def-weil-weil-sheaf-complex], $u\theta_K=\theta_LT(u)$. Use the iterates of [def-weil-local-frobenius-trace]. Induction gives $u\theta_K^{[n]}=\theta_L^{[n]}T^n(u)$: the base $n=1$ is the morphism equation, and the step is
$$u\theta_K^{[n+1]}=u\theta_K^{[n]}T^n(\theta_K)=\theta_L^{[n]}T^n(u\theta_K)=\theta_L^{[n]}T^n(\theta_L)T^{n+1}(u)=\theta_L^{[n+1]}T^{n+1}(u).$$
In particular this holds for $n=e$, using the specified pullback-composition comparisons.

### Original step 3

At the $E$-stage put $P=\operatorname{Fib}_sL\bar x^*$. For each $K$, let $J_K:P(K)\to P(T^eK)$ be the iterated point transport followed by the return comparison of [def-weil-local-frobenius-trace]. Thus $F_{x,K}=P(\theta_K^{[e]})J_K$. Point transport is natural by [lem-weil-frobenius-point-transport-natural] (2), and pullback composition is natural by [lem-pod-integral-pullback-composition], then scalar localization. Composing their squares gives $P(T^eu)J_K=J_LP(u)$. The return is $g_Y^e\bar x=\bar xg_s^e$, not literal fixation of $\bar x$. Consequently
$$P(u)F_{x,K}=P(u\theta_K^{[e]})J_K=P(\theta_L^{[e]})P(T^eu)J_K=P(\theta_L^{[e]})J_LP(u)=F_{x,L}P(u).$$
This is an identity of the rational point-complex morphisms over $E$.

### Original step 4

To pass this identity to $\Qlb$, use the specified comparison families of [lem-trf-integral-pullback-comparison-realization]. Its composition/scalar equation, including equality of scheme maps and arbitrary finite iterations, supplies coefficient compatibility of the return comparison and of $\theta^{[e]}$. The coefficient equation of [lem-trf-local-frobenius-transport-normalization] applies to $m=e$ and the $\mathbf F_{q^e}$-point induced by $\kappa(x)\hookrightarrow k$. Its map $t_{x,e,K}$ is exactly $J_K$, with those comparison families. For $E\subset M$, write $b_K:P_EK\otimes_EM\xrightarrow{\sim}P_M(K\otimes_EM)$ for its point comparison and $d_K:(T_E^eK)\otimes_EM\xrightarrow{\sim}T_M^e(K\otimes_EM)$. That lemma gives
$$P_M(d_K)b_{T_E^eK}(J_K\otimes_EM)=J_{K\otimes_EM}b_K.$$
The composition/scalar equation and naturality of $b$ applied to $\theta^{[e]}$ therefore give
$$b_K(F_{x,K}\otimes_EM)=F_{x,K\otimes_EM}b_K.$$
Thus the local operators and Step 3's intertwining equation define the same maps after every further common extension, with the identity and tower identifications of these lemmas. This defines the stagewise $\Qlb$ interpretation of the $E$-coefficient local operator in [def-weil-local-frobenius-trace], rather than treating that definition as already asserting coefficient compatibility. By [def-weil-algebraically-closed-coefficients] the equation holds in the common-stage category. Taking $H^0$ gives commutation for the two fibre maps of Step 1.

## Search reading

All new searches use the required msearch.py command and are recorded in searches.jsonl. Read the returned signatures: Endofunctor.Algebra.Hom.h is the single defining square, NatTrans.naturality assumes the transformation already exists, Functor.map_comp only preserves composition, filtered-colimit results handle ordinary colimit equalities, and the other semantic hits concern ring/perfection Frobenius, adic module completion or scheme limits. None constructs the specified common-stage Weil iterates or geometric point-return transformation. I also read Mathlib/CategoryTheory/Endofunctor/Algebra.lean lines 34–72 and NatTrans.lean lines 50–57 to rule out the closest general names. The two alternate semantic phrasings for each node are logged; no unavailable service is counted as absence. Blueprint searches included Frobenius natural, Frobenius coefficient, local Frobenius natural, finite diagram, Weil finite stage, iterated Weil, semilinear return and return transport. DAG searches included all local operator/return/finite-diagram statements and the existing stronger candidates listed above.
