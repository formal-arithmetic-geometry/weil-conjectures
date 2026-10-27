# Q24 repair report

## Files written

- dag/nodes/sec-six-functors/lem-pur-affine-chart-exceptional-identification.json: statement, split; unchanged statement, three assembly steps.
- dag/nodes/sec-six-functors/lem-pur-witnessed-compact-support-adjunction.json: statement, unsplit; five logged Mathlib queries, no match.
- dag/nodes/sec-six-functors/lem-pur-witnessed-open-chart-transport.json: statement, unsplit; six logged Mathlib queries, no match.
- citations.json: verbatim statement excerpts for every citation of every new parent step.

## Attachments

None. Searched the live WeilConjectures tree for the blueprint tag and the notions. Its matches for affine charts concern unrelated algebra/geometry, not this exceptional comparison. Read lean/Sheaf/Paper/PurityAffineChartExceptionalIdentification.lean: exists_liftedAdjunction (198), exists_openLift (218), compactification_independence (246), affine_chart (274), constructible_origin (343), base_open_chart (366) all have sorry. No compiler was run. The new nodes are statement-only natural-language work items; existing Lean records on the parent are retained, without claiming closure.

## WANTED

None. The source is the available blueprint; proof_origin remains agent, as required for agent-written blueprint arguments. No SGA source is used.

## Return repaired

The returned proof had 8030 characters across ten steps. The sandbox initially contained only dispatcher markers, no node/report/search log. I copied the current repository node, preserving every metadata field and the exact statement. The two new nodes are separate work items of comparable effort: the first carries the witnessed adjunction and coherent choice argument (old Steps 1–5); the second carries restriction and normalized chart transport (old Steps 6–9, with old Steps 1–2 applied to its schemes). The parent retains old Step 10 as its final assembly. Its proof is under 3000 characters. This expressly requested decomposition of the old clauses implements the human's re-split decision; neither child restates the whole item or the final base-open/chart assembly. Both children are unsplit, with no proof steps or proof dependencies. Every old argument appears verbatim below, assigned to the node whose next worker must formalize it, rather than hidden by shortening the argument. Their statements specify all data, domains, normalizations and coherence conclusions needed by the parent.

## Not duplicates

lem-pur-witnessed-compact-support-adjunction vs lem-sf-class-compact-support-comparison: the existing node gives the left witness comparison only, not an adjunction on retained witnesses or its compactification coherence.
lem-pur-witnessed-compact-support-adjunction vs thm-amb-etale-exceptional-adjoint: that is an ordinary etale unbounded adjoint, not lifts and normalized Hom bijections on witnessed pro-etale D+ objects.
lem-pur-witnessed-compact-support-adjunction vs prop-compactification-coherence-detailed: the existing node compares compact supports, not their transported right adjoints or the compatibility of witnessed Hom bijections.
lem-pur-witnessed-compact-support-adjunction vs def-weil-exceptional-inverse-image: that definition specifies the transported composite, not the asserted adjunction and coherent comparisons on witnessed categories.
lem-pur-witnessed-open-chart-transport vs lem-sf-etale-chart-adjoint-comparison: the existing node supplies natural Hom tests only; it explicitly does not assume the representing objects bounded below. The new node proves the D+ derived isomorphism, its normalization and the transport with actual witnesses.
lem-pur-witnessed-open-chart-transport vs lem-pur-etale-closed-chart-exceptional-preservation: that node assumes separated X and Y over k, includes a purity orientation/Tor conclusion, and concerns ordinary etale objects. Here X need not be separated over k, inputs are arbitrary D+ witnesses, and no purity identification or Tor bound is used.
lem-pur-witnessed-open-chart-transport vs lem-weil-pbc-comparison-pullback: the existing node is the pullback-comparison square, not the exceptional chart comparison or its bounded-below domain verification.
lem-pur-witnessed-open-chart-transport vs sk-prop-sf-rf-shriek-preservation: that node concerns Loc(Dctf), constructibility and Tor preservation, not arbitrary witnessed D+ objects, and assumes schemes separated over k.
lem-pur-witnessed-open-chart-transport vs cor-exc-base-change-open-immersion-general: this is open base change for the bounded class, not the source-chart factorization comparison for arbitrary witnessed D+ inputs.

Searched the whole DAG for witnessed adjunction, compactification independence, bounded-below chart and the two new ids; searched the whole imported blueprint with blueprint_refs.py for witnessed, chart, compactification independence, etale chart, etale origin, witnessed compact support and open chart transport. No equal or more general node with these conclusions was found. No new Stacks tag is introduced: both new statements expand the same blueprint Step 1 and the successive-restriction portion of Step 3. Their from.node is thm-pur-general-admissibility and via is [lem-pur-affine-chart-exceptional-identification].

## Review by Q24

I read the item and its entire ten-step returned proof, its stage-2 module and docstrings, the current chapter and unit records, the ancestor blueprint proof thm-pur-general-admissibility.proof.md (Steps 1 and 3), and the unit sk-prop-sf-rf-shriek-preservation's chart-locality argument. I read every one of the old proof's 20 dependency statements, not their names alone. No source statement or coefficient category was changed. In particular a finite-type k-scheme need not be separated over k, and the new chart statement keeps that generality. The geometric check makes the schemes Noetherian and qcqs and the morphisms compactifiable before ordinary adjoints are used. The field is Noetherian; open subsets of a Noetherian scheme are quasi-compact, so these open immersions are finite type. The closed immersion into a finite-dimensional affine space and its projection are separated finite type by their affine presentations.

Parent step 1 uses the new adjunction statement exactly for its two lifts, D+ witnesses and coherent comparisons. For f_V the cited base-change lemma states separated finite type, and the cited open-base-change lemma states h is an open immersion; these are precisely the hypotheses needed, not constructibility assertions. Parent step 2 uses the new restriction/chart statement at f_V, u', i, pi. Its displayed conclusion is a derived isomorphism in C(U); it does not replace it by per-degree cohomology. It supplies the retained restricted witness and compatibility of successive restrictions. Parent step 3 uses the exact bounded-constructible equivalence clause of lem-sf-proetale-constructible-origin to give L a witness, and only the independent final bounded-class clause of cor-exc-base-change-open-immersion-general, whose canonical map has the required direction. The two new statements ensure that both values of that map are witnessed D+ objects. Since witnessed morphisms are all ambient arrows, its inverse also lifts. Restricting along u' and composing with the normalized chart map proves precisely the last formula.

For the first child, I checked the original domain argument against lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, thm-nagata-compactification, lem-pod-separated-finite-type-base-change and lem-weil-pbc-open-immersion-base-change. thm-amb-etale-exceptional-adjoint gives the ordinary adjunction with a finite ring and Noetherian compactification. lem-amb-etale-compact-comparisons supplies bounded-below compact support and normalized choice comparisons; lem-etale-upper-shriek-quasicompact-bounded-below requires the quasi-compact target, which has been checked. lem-sf-class-compact-support-comparison gives the left witness with the inverse orientation; thm-weil-pbc-site-comparison gives the invertible unit and full faithfulness, and lem-sf-comparison-pullback-exact keeps the lower bound. The three-arrow Hom chain and naturality for all underlying arrows follow, not merely naturality for morphisms supplied with witness maps. For choice coherence, prop-compactification-coherence-detailed applies only on etale origin, which is the domain here. det-sp-unique-right-adjoint supplies counit-compatible uniqueness, so identities, cocycles and Hom compatibility have the normalization recorded in the new statement.

For the second child, prop-weil-pbc-inverse-image-modules-exact and prop-weil-pbc-proetale-constant-exact give the exact constant-coefficient inverse images; lem-weil-pbc-comparison-pullback supplies the natural square with identity and composite compatibilities. In the normalized chart theorem, the old lem-sf-etale-chart-adjoint-comparison is used with v=id_V, s=j and p=pi; every displayed morphism is separated finite type compactifiable. Its statement gives exactly the Hom chain copied in the new statement, but not boundedness of B or Q. The separate bounded-below adjoint theorem supplies that boundedness before evaluating at B or Q. I checked the Yoneda computation a=Theta_Q(1), b=Theta_B^{-1}(1), and both ab=1 and ba=1, and naturality in N_e. The comparison unit is then used twice, including at H_pi N_e; that object is D+, so no unbounded unit is used. Full faithfulness supplies naturality for all witnessed arrows. These details are retained verbatim below for the next worker.

The small cases are consistent: d=0 gives the identity affine projection without any positive-dimension assumption; identity maps and identity opens reduce to the adjunction identity comparisons; empty U or V gives zero derived categories; n=1 causes no coefficient change. Non-separated finite-type X remains permitted: qcqs follows from Noetherianity, while compactification needs separatedness of the maps, not of their sources over k. No uniform lower bound, bounded constructible preservation, or unrestricted ambient pro-etale adjoint is inferred. There is no dependency from either child back to its parent: the parent id occurs only in provenance. New nodes have proof=[] and proof_deps=[] as required. All parent citations have literal excerpts in citations.json. All three parent proof steps are below 2000 characters.

The Mathlib searches were run through msearch.py and recorded from its real searches.jsonl results. The first child has two semantic phrasings, a Loogle pattern, LeanSearch and grep; the second has the same plus the explicit rightAdjointUniq grep. The generic adjunction and right-adjoint uniqueness hits do not supply the etale/pro-etale functors, D+ witness construction, or normalized exceptional chart identification. Read the Mathlib rightAdjointUniq/counit declarations and derived-adjunction context; they are ingredients, not one-line specializations of either complete statement. The existing generic uniqueness node is reused in the preserved proof rather than duplicated. There were no unavailable services in these recorded searches.

## Complete retained argument for lem-pur-witnessed-compact-support-adjunction

### Returned step 1

All schemes occurring in the assertion are Noetherian: apply [lem-weil-pbc-finite-type-over-noetherian] over $\operatorname{Spec}k$ and [lem-weil-pbc-noetherian-open-subscheme-noetherian] to open subschemes. Here a field is Noetherian since its only ideals are zero and the whole field. In particular all targets are quasi-compact; intersections of affine opens are open Noetherian subschemes and hence quasi-compact, so the schemes are quasi-separated. Thus [thm-nagata-compactification] supplies the chosen compactifications for separated finite-type maps. For the chart, [lem-pod-separated-finite-type-base-change] applies to $f_V$ and [lem-weil-pbc-open-immersion-base-change] to $h$. The open maps are quasi-compact since their sources and all affine-open inverse images are Noetherian opens. They are separated and of finite type, and the same holds for the closed map $i$, the affine-space projection $\pi$, and their displayed composites. Consequently the Noetherian and compactifiability hypotheses of the etale results used below hold, without requiring $X$ or $Y$ to be separated over $k$.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, thm-nagata-compactification, lem-pod-separated-finite-type-base-change, lem-weil-pbc-open-immersion-base-change.

### Returned step 2

Write $F_v=Rv_{!,e}$ and $H_v=v_e^\times$ on the ordinary etale categories. The adjunction $F_v\dashv H_v$ is [thm-amb-etale-exceptional-adjoint]. Its restriction has both functors taking values in $D^+$: compact support is the bounded-below functor in [lem-amb-etale-compact-comparisons], and [lem-etale-upper-shriek-quasicompact-bounded-below] applies to $H_v$ because the target $R$ is quasi-compact by step 1. The latter assertion is only bounded-below preservation, with a possible lower-bound shift; it asserts no constructibility preservation. Apply this also to $f_V,i,\pi$ and the open chart maps. In particular $i_e^\times\pi_e^\times N_e$ is bounded below whenever $N_e$ is.

Cited statements: thm-amb-etale-exceptional-adjoint, lem-amb-etale-compact-comparisons, lem-etale-upper-shriek-quasicompact-bounded-below.

### Returned step 3

Put $C_T=\nu_T^*$. For $M=(M,M_e,\alpha)$ the natural isomorphism of [lem-sf-class-compact-support-comparison] gives the witness $C_RF_vM_e\cong Rv_!M$ (invert its displayed comparison). For $N=(N,N_e,\beta)$, [thm-weil-pbc-site-comparison] gives the natural isomorphism $N_e\cong R\nu_{R,*}N$: compose the comparison unit at $N_e$ with $R\nu_{R,*}\beta$. Apply $C_SH_v$ to obtain $C_SH_vN_e\cong G_vN$. Step 2 supplies bounded-below witnesses $F_vM_e$ and $H_vN_e$; [lem-sf-comparison-pullback-exact] ensures their comparison pullbacks are bounded below as well. These constructions define object lifts. On arrows use exactly $Rv_!$ and $G_v$ on the underlying pro-etale arrow; the definition of morphisms in [def-sf-etale-origin-subcategory] imposes no extra witness map. Identity and composition laws therefore remain the underlying functor laws.

Cited statements: lem-sf-class-compact-support-comparison, thm-weil-pbc-site-comparison, lem-sf-comparison-pullback-exact, def-sf-etale-origin-subcategory.

### Returned step 4

Using the witnesses from step 3, full faithfulness in [thm-weil-pbc-site-comparison], and the ordinary adjunction [thm-amb-etale-exceptional-adjoint], the required bijection is the chain
$$\operatorname{Hom}_{\mathcal C(R)}(Rv_!M,N)\cong\operatorname{Hom}_{D^+(R_e)}(F_vM_e,N_e)\cong\operatorname{Hom}_{D^+(S_e)}(M_e,H_vN_e)\cong\operatorname{Hom}_{\mathcal C(S)}(M,G_vN).$$
All four Hom sets are well typed by steps 2 and 3. Every arrow between witnessed objects corresponds to a unique etale arrow by full faithfulness, so the naturality of the comparisons and the etale adjunction proves naturality for every underlying arrow, not just arrows initially presented with etale lifts. Thus this is an actual adjunction of the two lifted functors.

Cited statements: thm-weil-pbc-site-comparison, thm-amb-etale-exceptional-adjoint.

### Returned step 5

On the stated domain, [prop-compactification-coherence-detailed] gives the canonical compact-support comparisons and their cocycle. The ordinary etale versions are those of [lem-amb-etale-compact-comparisons]. At two compactifications, their $D^+$ right adjoints from step 2 are compared by the counit-compatible uniqueness isomorphism of [det-sp-unique-right-adjoint], after identifying the left adjoints. Applying $C_S$ and the witness-unit identifications of step 3 gives comparisons of $G_v$. The Hom chain in step 4 commutes with these maps: the middle bijection does so by counit compatibility, and the outer bijections are natural comparison isomorphisms. Identity and composition of right comparisons follow because both composites are counit-compatible and uniqueness makes them equal. This proves the asserted independence, including the underlying bijections.

Cited statements: prop-compactification-coherence-detailed, lem-amb-etale-compact-comparisons, det-sp-unique-right-adjoint.

## Complete retained argument for lem-pur-witnessed-open-chart-transport

The geometric and bounded-below checks of returned Steps 1–2 above are applied here to X, V, U, T and their displayed maps. They are part of this child’s statement and proof obligation as well. The remaining argument is unchanged:

### Returned step 6

For any of the open immersions $j:W\hookrightarrow T$, constant-coefficient pullback is exact on both sites by [prop-weil-pbc-inverse-image-modules-exact] and [prop-weil-pbc-proetale-constant-exact]. Thus $Lj^*=j^*$ acts termwise and preserves a lower bound. Apply the natural inverse-image comparison of [lem-weil-pbc-comparison-pullback] termwise to the witness $C_TM_e\cong M$: it gives $C_W(j_e^*M_e)\cong j^*M$. This constructs the claimed restricted witness and the functor on $\mathcal C$. The identity and composition compatibilities in that comparison identify restriction along $u=hu'$ with successive restriction along $h$ and $u'$.

Cited statements: prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact, lem-weil-pbc-comparison-pullback.

### Returned step 7

For $N_e\in D^+(V_e,A)$ set $B=i_e^\times\pi_e^\times N_e$ and $Q=(u'_e)^*(f_V)_e^\times N_e$. By steps 2 and 6 both are in $D^+(U_e,A)$. Apply [lem-sf-etale-chart-adjoint-comparison] with $f=f_V$, $s=u'$, $v=\mathrm{id}_V$, $p=\pi$ and $K=N_e$; step 1 checks every geometric hypothesis and $f_Vu'=\pi i$ is the chosen equality. It supplies the natural bijection $\Theta_H:\operatorname{Hom}(H,Q)\cong\operatorname{Hom}(H,B)$, the inverse of the bijection displayed in that node. Explicitly its forward chain is
$$\operatorname{Hom}(H,Q)\cong\operatorname{Hom}(u'_!H,(f_V)_e^\times N_e)\cong\operatorname{Hom}(R(f_V)_{!,e}u'_!H,N_e)\cong\operatorname{Hom}(R\pi_{!,e}i_*H,N_e)\cong\operatorname{Hom}(H,B).$$
Here the cited node supplies the normalized compact-support compositor as well as the adjunctions: we use its stated natural Hom bijection, not an unstated identification of unbounded representing objects.

Cited statements: lem-sf-etale-chart-adjoint-comparison.

### Returned step 8

Evaluate step 7 at the two representing objects, which is allowed because both are bounded below. Set $a=\Theta_Q(1_Q):Q\to B$ and $b=\Theta_B^{-1}(1_B):B\to Q$. Naturality in $H$ gives $\Theta_H(t)=a\circ t$ and $\Theta_H^{-1}(z)=b\circ z$. Hence $a\circ b=1_B$ and $b\circ a=1_Q$ by the inverse identities of the bijections. The naturality in $N_e$ gives $B(\phi)\circ a_{N_e}=a_{N'_e}\circ Q(\phi)$ for every $\phi:N_e\to N'_e$, so $a$ is a natural isomorphism. Its definition as successive transposes of the normalized compact-support comparison also fixes its canonical adjunction normalization.

Cited statements: elementary Yoneda evaluation, written out.

### Returned step 9

Apply $\nu_U^*$ to the isomorphism in step 8. For $N=(N,N_e,\beta)$, step 3 and [thm-weil-pbc-site-comparison] identify $G_{f_V}N$ with $\nu_{X_V}^*(f_V)_e^\times N_e$ and $G_\pi N$ with $\nu_T^*\pi_e^\times N_e$. Apply the same unit once more at the bounded-below object $\pi_e^\times N_e$ to identify $G_iG_\pi N$ with $\nu_U^*i_e^\times\pi_e^\times N_e$. The comparison [lem-weil-pbc-comparison-pullback] identifies $L(u')^*G_{f_V}N$ with $\nu_U^*Q$. Therefore the image of $a:Q\cong B$ is precisely $L(u')^*G_{f_V}N\cong G_iG_\pi N$. Both objects have the specified etale witnesses by steps 3 and 6, so this is an isomorphism in $\mathcal C(U)$. Full faithfulness makes its naturality hold for every morphism in $\mathcal C(V)$.

Cited statements: thm-weil-pbc-site-comparison, lem-weil-pbc-comparison-pullback.

## What remains

No part of the requested repair is left unfinished. The two children intentionally remain unsplit for independent future workers. Required server dry run and delivery follow.
