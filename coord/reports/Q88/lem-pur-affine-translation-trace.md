# Repair report: lem-pur-affine-translation-trace

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-affine-translation-trace.json: unchanged statement; shorter assembly of the two extracted arguments and the existing comparison theorems.
- dag/nodes/sec-smooth-purity/lem-pur-universal-translation-multiplier.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-affine-constant-section-zero-detection.json: statement, unsplit; no Mathlib match.

## Attachments

None. The project search for the blueprint tag and translation/trace terminology found purAffineTranslationTrace in lean/Sheaf/Paper/AffineTranslationTrace.lean:278; its body is sorry. The WeilConjectures/ search found no declaration proving this item or the extracted nodes.

## WANTED

None. All source texts needed for this repair are available locally.

## Return repaired

The sandbox initially contained only dispatcher brief markers, with no retained node, searches or report. I continued from the current read-only node, whose four proof lengths are the exact 835/770/768/1066 named by the return for head e2a95534abdca96856ae1c3b80c5b78fb624dc06. The item statement and maintainer metadata were retained verbatim. Two new, comparably substantive work items replace the scalar and fibre arguments. Neither asserts the translation trace equation itself. Both are unsplit, with empty proof/proof_deps and null proof_origin; their intended proofs are recorded below. Parent assembly is under 3000 characters, and has no step over 2000 characters. No Lean was written or compiler run.

The multiplier node carries old steps 1 and 2, including the actual action, its inverse and base-change equations, the specified normalized trace, degree-zero full faithfulness, multiplication by the image of 1, the inverse scalar, local constancy and zero-section normalization. The detection node carries the connected-fibre and global-detection argument of old step 3, with an independently reusable statement for every abelian group and arbitrary base. The parent keeps old step 4, including specialization to a, arbitrary base change, ambientAffineTranslationTrace and the vectorIntegration comparison. Thus none of the old reasoning is discarded.

## Not duplicates

lem-pur-universal-translation-multiplier vs lem-amb-compact-action-base-change: the existing node constructs the action of an arbitrary automorphism, but does not identify a trace-conjugated action with a unique locally constant unit or normalize its zero-section scalar.

lem-pur-universal-translation-multiplier vs lem-amb-affine-space-top-trace: the latter constructs the trace and its base-change equation, without a parameterized translation action or its scalarization.

lem-pur-universal-translation-multiplier vs lem-trf-ambient-affine-translation-trace: the latter is the final ordinary translation-invariance equation; the new node stops at an unknown unit normalized on the zero section, and does not assert invariance.

lem-pur-affine-constant-section-zero-detection vs lem-pur-a1-pullback-endomorphism-rigidity: the latter concerns endomorphisms of finite locally constant modules on the pro-etale affine line tested at t=1; this is an ordinary-etale section isomorphism in all dimensions for an arbitrary abelian group, not assumed finite. Neither identifies the two sites without a comparison argument.

lem-pur-affine-constant-section-zero-detection vs lem-pur-a1-components: the latter gives connected components of A1 and Gm for a nonempty separated finite-type k-base; the new node is a natural constant-sheaf section isomorphism for every base and affine dimension, including empty bases and infinite coefficient groups.

lem-pur-affine-constant-section-zero-detection vs lem-weil-pbc-connected-locally-constant-map: that node assumes one nonempty connected topological space; it does not establish connected fibres, the global pullback identity or zero-section detection for an arbitrary base.

lem-pur-affine-constant-section-zero-detection vs lem-weil-pbc-constant-sheaf-sections-locally-constant: the existing node identifies sections on one scheme with functions; the new node proves the relative affine-space isomorphism between two schemes.

lem-pur-affine-constant-section-zero-detection vs lem-weil-pbc-etale-geometric-fibre-constant-sections: that node identifies sections over a connected scheme over an algebraically closed field; the new statement identifies global sections over arbitrary, possibly disconnected bases and includes the actual zero-section inverse.

lem-pur-affine-constant-section-zero-detection vs lem-fd-affine-line-constant-cohomology: the latter is an adic cohomology calculation over an algebraically closed field, not relative finite or arbitrary discrete constant sections.

I searched all DAG statements by locally-constant/constant-section together with affine-space, connected-fibre and zero-section wording, and read the relevant candidate statements. Whole-blueprint searches were translation, locally constant, zero section, multiplier and constant section; ancestor gives lem-pur-projection-purity-agreement. The new nodes have via=[lem-pur-affine-translation-trace], and neither has a blueprint duplicate.

## Searches

Each new node records exactly the applicable commands from searches.jsonl. Two different semantic phrasings were run for each. LeanFinder hits concerned affine coordinates, normalization and algebraic etaleness, not compact-support action or constant etale sections. Loogle returned general derived-isomorphism statements for the multiplier, and no Scheme/LocallyConstant match for the detection node. The grep hits for translation/trace are tactic tracing, while AffineSpace source gives coordinate universal properties, not the requested sheaf isomorphism. I read the affine coordinate definitions and the derived single-functor full/faithful instances to distinguish these partial inputs from a match. LeanSearch was rate-limited and is recorded unavailable, never as an empty successful search. The old item's searches remain unchanged.

## Review by Q88

I read the chapter sec-smooth-purity, unit sk-thm-smooth-purity (especially Agreement on the model), the parent blueprint statement lem-pur-projection-purity-agreement, and main-20261015 sk-prop-sp-orientation-vector-bundle.proof.md, Step 1: translation. Both extracted statements serve precisely its varying-translation/unit-multiplier/connected-fibre argument. The source is the permitted blueprint/lecture-notes route; no SGA source is used. For the constant-section input I also read Stacks etale-cohomology.tex, remark-constant-locally-constant-maps (Tag 03P5): its formula identifies sections with Zariski-locally constant functions; this does not itself assert affine-space detection.

Parent step 1 uses finite-type-over-Noetherian only for Noetherianity of S and P. A field is Noetherian and polynomial affine charts preserve finite type. The multiplier node then supplies exactly rho_P, t_P, b, e*b=1 and both exchange equations: its statement was opened while writing the step. An annihilating prime power exists for every finite coefficient A_E,n, including ramified n, and remains invertible on all k-schemes. Step 2 uses the new detection statement with the additive abelian group of A, so b=p*e*b=1; cancellation through the isomorphism t_P is elementary composition in the derived category. Step 3 is the retained final specialization step: compact-action-base-change explicitly states C_u u*rho=rho_T C_u, affine-space-top-trace explicitly states t_T C_u=u*t, so pulling along a yields the specified kappa/exchange action. I read both statements, not just their names. The coordinate-tower lemma states the ordinary normalized equation with precisely those Tate identifications and Noetherian/invertibility hypotheses; it is retained at both S and P. The site-comparison statement explicitly gives t_pi^p beta_pi=C_S(t_pi^e), including finite exponent independence, and the vector-integration definition constructs the actual trivial-bundle counit used by the item. These actual-map equations support the final pro-etale/vectorIntegration clause, without identifying coefficient categories by assertion. citations.json contains verbatim portions of every cited statement.

For the multiplier node the intended proof is old steps 1 and 2 below plus the identity-action part of step 3: polynomial charts give Noetherian P,W, the inverse translation is z+a, shifted Tate input is bounded below, and a projective completion provides compactification. Apply compact-action-base-change and affine-space-top-trace, then derived-single-fully-faithful. On any etale object a module map of the coefficient ring is multiplication by its value at 1; the inverse gives a unit, sheaf compatibility gives a global section, and 03P5 makes it locally constant. Conjugating the two explicit base-change equalities gives the formula for u*b. At zero, the canonical Tate identity and rho_1,1=1 give e*b=1. The node is not a proof sketch: only these conclusions and their fully introduced objects are in its statement.

For the detection node the intended proof is old step 3 below without using translation. On a geometric fibre P_sbar=Spec(Omega[x_1,...,x_d]), the polynomial ring is a nonzero domain, so its spectrum is nonempty connected, with the origin. Pulling back a locally constant function to this fibre makes it constant by connected-locally-constant-map; its value is its value at that origin. Every point of P lifts to a point of the geometric fibre over its image in S, so this proves b=(b e)p pointwise. The function b e is locally constant since e is continuous; the section/function identification turns the identity into p*e*=1, and pe=1 gives e*p*=1. Pullbacks commute with the projection and zero section, giving the claimed naturality. This preserves the polynomial-domain and point-detection work rather than hiding it behind a reference to connected components. No cohomology group is substituted for a derived object.

I checked d=0 (all projections/sections identify with the base and translation is the identity), the empty base (unique section/function), disconnected bases (argument is fibrewise), a=0 (identity action), nonreduced bases (geometric fibres are still polynomial rings over fields), arbitrary finite n and the zero coefficient ring (0=1 and its sole unit cause no exception). The detection node also works for infinite E, since it uses local constancy, not finiteness. No new hypothesis is added to the item. The earlier stage-2 correction metadata and statement were not modified. B1-B10, C1-C8, D1-D5 and E1-E7 were checked against these actual files: fresh ids, standalone TeX statements, no proofs in new unsplit nodes, no circular dependency, no off-route replacement, and no elementary helper extracted merely to inflate the node count. The two independent mathematical tasks are the trace-action multiplier with its specified-map naturality, and the relative sheaf-section isomorphism by geometric-fibre detection.

## Original arguments retained for the next workers

### Original step 1

First work on the ordinary étale site. The finite-type $k$-scheme $S$ is Noetherian, and so are $P=\mathbf A^d_S$ and $V_P=V\times_SP$; the affine polynomial charts give the needed separated finite-type maps. Let $q_P:V_P\to P$ be the base change of $q$, let $a_P:P\to V$ be the tautological section, and let $\tau_P:V_P\to V_P$ be $(z,a)\mapsto(z-a,a)$. It is an automorphism over $P$, with inverse $(z,a)\mapsto(z+a,a)$. Apply [lem-amb-compact-action-base-change] to $q_P$, $\tau_P$, and the canonical pullback isomorphism $\tau_P^*L\simeq L$. This gives the actual compact-support action $\rho_P:Rq_{P!}L\to Rq_{P!}L$ and its compatibility with every base change. By the base-change clause of [lem-amb-affine-space-top-trace], the normalized trace $t_P:Rq_{P!}L\to A_P$ is an isomorphism and is the pullback of $t_q$ along $P\to S$.

Cited statements: lem-amb-compact-action-base-change, lem-amb-affine-space-top-trace, lem-weil-pbc-finite-type-over-noetherian, def-sbc-affine-space, def-weil-pbc-derived-categories, lem-asd-etale-finite-twist-pullback.

### Original step 2

Conjugate the universal action by the specified trace: $\alpha=t_P\circ\rho_P\circ t_P^{-1}:A_P[0]\to A_P[0]$. It is an automorphism of the constant $A_P$-module sheaf. By full faithfulness of degree-zero sheaves [lem-weil-pbc-derived-single-fully-faithful], it is induced by a unique $A_P$-linear sheaf automorphism $\alpha_0$. Module linearity makes $\alpha_0$ multiplication by $b=\alpha_0(1)$, and the inverse action shows that $b$ is a unit. The section $b$ is a Zariski-locally constant function with values in $A$ by [lem-weil-pbc-constant-sheaf-sections-locally-constant]. Pullback of $b$ along any base-change section is the scalar by which the corresponding translated trace is multiplied, by the action and trace base-change equations in the two cited lemmas.

Cited statements: lem-amb-compact-action-base-change, lem-amb-affine-space-top-trace, lem-weil-pbc-derived-single-fully-faithful, lem-weil-pbc-constant-sheaf-sections-locally-constant.

### Original step 3

For every geometric point $\bar s\to S$, the fibre $P_{\bar s}=\operatorname{Spec}\overline{\kappa(s)}[x_1,\ldots,x_d]$ is nonempty and connected: its coordinate ring is a nonzero domain (and for $d=0$ it is the one-point scheme). The restriction of $b$ to this fibre is locally constant, and its value at the origin is $1$, because the universal translation restricted along the zero section is the identity and [lem-amb-compact-action-base-change] gives $\rho_{1,1}=1$. Hence [lem-weil-pbc-connected-locally-constant-map] makes $b|_{P_{\bar s}}=1$. Every point of $P$ lies in such a geometric fibre, so the section/function identification of [lem-weil-pbc-constant-sheaf-sections-locally-constant] gives $b=1$ globally. Therefore $\alpha=1$ and $t_P\circ\rho_P=t_P$.

Cited statements: lem-amb-compact-action-base-change, lem-weil-pbc-connected-locally-constant-map, lem-weil-pbc-constant-sheaf-sections-locally-constant.

### Original step 4

Pull the universal equality back along the section $a:S\to P$. The action base-change identity of [lem-amb-compact-action-base-change] identifies the pulled-back action with $Rq_!(\kappa_a)\circ\operatorname{Ex}_{!,\tau_a}$, while the affine trace base-change identity of [lem-amb-affine-space-top-trace] identifies the pulled-back $t_P$ with $t_q$. Thus
$$t_q\circ Rq_!(\kappa_a)\circ\operatorname{Ex}_{!,\tau_a}=t_q.$$
In the recorded coordinate-tower model, [lem-trf-ambient-affine-translation-trace] supplies precisely this ordinary equation for ambientAffineTranslationExchange followed by ambientAffineTranslationTate and the normalized affineTraceCounit; apply it both on $S$ at $a$ and on the parameter scheme $P$ at its tautological coordinates. The same argument after any $S'\to S$ gives the asserted universal and arbitrary-base-change compatibility. Finally [lem-pur-vector-integration-site-comparison] carries this actual ordinary étale equality, with the specified Tate and compact-support comparisons, to the corresponding pro-étale integration maps.

Cited statements: lem-amb-compact-action-base-change, lem-amb-affine-space-top-trace, lem-pur-vector-integration-site-comparison, def-amb-vector-integration, lem-trf-ambient-affine-translation-trace.

## Unfinished work

No part of the requested stage-1 repair remains intentionally unfinished; the new nodes are statement-only as explicitly requested. The first server dry run completed and issued .stage1-ready.json for head 86785a97db1. The parent has 1830 proof characters in steps of 450, 314 and 1066 characters. A final dry run is performed after recording these results, followed by direct delivery.
