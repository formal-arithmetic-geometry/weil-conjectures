## Worker report

Q87 repairs lem-pur-projection-purity-agreement after the 2026-10-21 human re-split decision. The supplied sandbox was empty, so I recovered the delivered version from the live read clone. I preserved an exact original-item.json snapshot. No repository or launcher file was edited and no git, Lean, Lake or compiler command was run by this worker. The delivery command performs its own authorized temporary-worktree operations.

The exact parent statement, statement dependencies, blueprint_update, Lean records and maintainer review fields are preserved. Its former 14-step proof had 11802 characters; the new assembly has 1457 characters. This is a division of the proof into three separately claimable mathematical arguments, not a shorter paraphrase of the old proof.

## New nodes

- lem-pur-affine-diagonal-integration-orientation: the coordinate/translation, base-change transpose and standard-pair DNC comparison at the coefficient unit. Responsibility: old steps 3-6 (3439 characters). Source: the current model proof's diagonal/DNC paragraph, and the master unit's Agreement on the model paragraph. The assertion is an equality of derived morphisms, not just equality of cohomology or existence of orientations.
- lem-pur-affine-coefficient-counit-normalization: the finite-coefficient witnesses and domains, the actual tensor-map identification, and the affine-line counit calculation through the projective compactification. Responsibility: old steps 1,2,7,8,11,12 (about 4500 characters). Source: the current model proof's coefficient and ordered-orientation identifications, expanded by the cited finite-level projection and ordinary projective-line adjunction statements in the original proof.
- lem-pur-affine-ordered-integration-transposes: identification of the actual proper/open compositor, projection compatibility, and the induction comparing the ordered line adjunctions with integration transposes. Responsibility: old steps 9,10,13,14 (about 3800 characters). Source: the current model proof's ordered-product and reassociation sentences, expanded with the original compatible-compactification and composite-counit calculation.

All three are status unsplit, with proof [], proof_deps [], proof_origin null. The complete previous arguments are preserved below for the workers who will split them. These nodes do not assert the parent's equality of smooth and affine purity for arbitrary K. The first treats only the unit orientation, the second treats coefficient counits without comparing smooth and ordered maps, and the third compares the integration transpose with ordered maps without identifying the diagonal orientation. No new node swallows the full theorem.

## Searches and attachment check

I searched lean/WeilConjectures for the exact blueprint tag and the projection/purity notions and read the affine-space source declarations. They provide existence of isomorphisms, not all the normalized-arrow equalities in this item. The recorded live theorem in lean/Sheaf/Paper/ProjectionPurityAgreement.lean:566 ends in sorry at line 575, so it is not an attachment. No Mathlib leaf was found. Each new node has two separately phrased LeanFinder searches, Loogle, LeanSearch and a Mathlib grep, run through the required msearch.py and recorded exactly in searches.jsonl and mathlib_searches. Returned signatures were read: affine-scheme maps, real orientations, coalgebra counits, monoidal adjunction identities and ordinary scheme-module adjunctions do not state these normalized etale/pro-etale integration comparisons. Generic Adjunction.comp is a tool, not a one-line specialization of the ordered geometric normalization theorem.

Before creating the nodes I searched the whole DAG, the upstream Lean source and tools/blueprint_refs.py with diagonal orientation, integration counit, ordered affine, integration transpose, affine counit and diagonal integration. The ancestor is the item itself. No existing blueprint node provides any full proposed assertion without either narrower coefficients, conditional hypotheses, or dependence back on the item. No new statement cites the item or a descendant proof of it.

## Not duplicates

lem-pur-affine-diagonal-integration-orientation vs det-sp-orientation-vector-bundle: that node restricts E to Q_l and proves its global bundle comparison by invoking this parent; the new node is the independent trivial-bundle coordinate and normalized DNC computation for arbitrary E and all n, including the explicit alpha and beta-delta identities.

lem-pur-affine-diagonal-integration-orientation vs lem-pur-diagonal-dnc-chart-normalization: chart restriction and coordinate orientation use this parent and the ordered Gamma map; the new node derives the standard affine diagonal comparison directly against the integration transpose, without using the parent or Gamma.

lem-pur-affine-diagonal-integration-orientation vs lem-pur-trace-transpose-base-change: the existing generic statement only computes P-prime from a trace base-change equality; the new node includes translation and standard-pair DNC normalization and concludes beta delta alpha inverse = P inverse.

lem-pur-affine-coefficient-counit-normalization vs lem-pur-tensor-trace-transpose: the generic node assumes invertibility of the two projection maps and gives only a formal tensor transpose identity; the new node establishes the actual affine finite-Tor domains and the projective/open normalization of the line counit at every coefficient level.

lem-pur-affine-coefficient-counit-normalization vs lem-pur-vector-integration-site-comparison: that statement transports the integration/projection/transposes between sites; it does not identify the actual open/projective composite adjunction counit at arbitrary coefficients, or discharge the two omega/L projection-domain conditions.

lem-pur-affine-coefficient-counit-normalization vs lem-asd-ordinary-finite-p1-adjunction: proper projective-line adjunction on the ordinary site; the new assertion is about the affine open counit, its compactification projection and intrinsic pro-etale coefficients, plus the tensor-domain calculation.

lem-pur-affine-coefficient-counit-normalization vs lem-amb-affine-trace-line-counit-iso: invertibility of the line counit is the conclusion there; its informal proof contains the coefficient formula, but the quantified assertion does not identify the actual projection/integration map or the pro-etale transport. The new statement records these equalities and affine coefficient domains.

lem-pur-affine-coefficient-counit-normalization vs lem-pur-finite-site-counit-projection-transport: a generic site-transport compatibility; it does not establish the normalized affine-line coefficient counit or the affine-space tensor identity with all its projection domains verified.

lem-pur-affine-ordered-integration-transposes vs lem-pur-composite-integration-counit: generic two-map calculation assuming projection, tensor-action and compositor identities; the new node discharges these assumptions for the coordinate compactifications and proves the full ordered recursion, including the actual exceptional target.

lem-pur-affine-ordered-integration-transposes vs lem-sf-composition-projection-mate: only the generic compositor/projection equation is asserted; the new node includes its geometric site normalization and the induction giving P=Gamma, with twist and exceptional conjugates.

lem-pur-affine-ordered-integration-transposes vs lem-amb-affine-space-top-trace: constructs the ordered ordinary adjunction and proves its trace at A is an isomorphism; it does not compute the coefficient counit of the ordered adjunction or its equality with the specified exceptional recursion at all K.

lem-pur-affine-ordered-integration-transposes vs lem-pur-affine-space-trace-factorization: a conditional Kunneth formula for the tensor-unit trace, with m>=1 and additional hypotheses; the new node is an unconditional identification of arbitrary-coefficient ordered exceptional transposes, including rank zero.

## Review by Q87

I read the current main-20261015 statement and proof and both chapter/unit records. The current proof uses the same diagonal/DNC standard model and ordered line orientations as the expanded returned proof. I kept that route; I did not rely on equality of geometric stalks to imply equality of arbitrary derived maps. The source of the new orientation statement is the actual standard-pair model calculation, not the later vector-bundle orientation theorem, which depends on this item and would create a cycle. Its beta is the inverse integration transpose on the normal bundle, not an arbitrary orientation.

For assembly step 1 I read the new coefficient statement: it explicitly supplies bounded etale representatives with reflected Tor intervals, finite-dimensional compactifications, projection isomorphisms and the actual rank-one counit formula independent of r. Those are precisely the inputs taken by the step. Its witnesses apply to bounded constructible K with finite Tor amplitude; no pro-etale unbounded adjunction is asserted. I checked the original statements of lem-sf-proetale-constructible-origin(ii), lem-sf-comparison-tor-amplitude(ii), lem-weil-finite-compact-projection-formula, thm-sf-ambient-adjoint-class and lem-pur-vector-integration-site-comparison: respectively they give the etale representative, reflection of its interval, projection at bounded constructible source/finite-Tor base, the bounded-origin Hom bijection with dimension bound, and equality of actual integration transposes. Polynomial and projective compactifications are finite type over k, so the original finite-type Noetherian and dimension nodes apply. No source Tor assumption is silently imposed on every six-functor datum.

For assembly step 2 the orientation statement explicitly says beta delta alpha inverse = P inverse with the same alpha, delta, beta and frame as the parent. I read lem-pur-trace-transpose-base-change and lem-pur-diagonal-base-change: B is the transpose of the exchanged counit and alpha is its pulled-back inverse. Hence J=B p2*P and alpha Delta*J=P have the correct directions. I read lem-pur-affine-translation-trace, thm-pur-dnc-invariance and the standard-pair clause of lem-pur-dnc-section-geometry: h(x,y)=(x,y-x) preserves integration, normal coordinates are u=y-x, and the normalized deformation u=t v is identity on the standard section invariant. Together these give beta delta=(Delta*J) inverse and the claimed orientation. This is a separate unit-coefficient argument; it does not assert the full parent result.

For assembly step 3 I opened def-pur-smooth-purity-map: it defines the map exactly as theta composed with tensor the inverse orientation after the fixed shift reassociation. The new coefficient node states theta(1 tensor P)=P_(p,K) as an equality, so the step takes no claim merely from its proof. The old tensor-transpose node's hypotheses are met by the explicitly stated projection domains at L and omega; omega has the etale-origin isomorphism from vector-bundle integration. For the independent line-counit argument retained in this new node I read lem-asd-ordinary-finite-p1-adjunction, lem-amb-affine-space-top-trace and lem-pur-finite-projection-action-laws, especially clause 2: the proper counit is 1 tensor t_q after inverse projection, composition with the open counit restricts t_q to I_S, and the open tensor comparison commutes with that counit. This establishes the exact affine projection formula, rather than inferring it from the existence of an adjunction.

For assembly step 4 the new ordered-transposes statement gives P_(p_d,K)=Gamma_(p_d,K) with the precise recursion and right-adjoint conjugate c_m of alpha_m, at all n. I read the original compatible-compactification triangle, ordinary unbounded proper/open comparisons, finite strict-tower evaluation comparison, thm-sf-comp-composition, composition-projection-mate and composite-integration-counit statements. They give exactly the actual compositor and projection equation written in the new node, not just an unspecified associator. The Noetherian schemes are qcqs; all required opens are quasi-compact, and etale-origin/finite-Tor domains are supplied by the coefficient calculation. The induction is based at d=0 with identity adjunction. At the induction step the counit formula holds for G_dK and the rank-one functor, and naturality of the line transpose changes G_dK to Rp_d^!K. Every twist reassociation is the fixed even-shift, ordered one; there is no hidden permutation sign.

I checked B-E with these statements open: each new node introduces its field, coefficients, schemes, functors, maps and normalizations; all bracketed notions are statement dependencies; no new node has proof steps or a proof sketch in its statement. Generic facts remain existing nodes in the recorded old arguments. I tested d=0 (empty coordinate lists, identity deformation and adjunction), d=1 (the open/projective counit), K=0 and empty Y (unique zero-object maps), and ramified E with n not divisible by its ramification index (choose any annihilating ell-power; no flatness over Z/ell^r is used). None forces a statement correction. The old proof is allocated without dropping any argument in the next section. The parent has no step above 2000 characters. This repair changes the proof division only; there is no STATEMENT-DISPUTED change.

## Full retained arguments and responsibility map

The following fourteen texts are copied verbatim from the returned live proof. They are working material for the three new unsplit items, not proofs claimed in their node files. Their cited statements remain the specific intended tools; each assigned node will be split independently later. Assignment is exhaustive and disjoint.

### Original step 1 -> lem-pur-affine-coefficient-counit-normalization

Choose $r\geq1$ with $\ell^r A=0$. Apply [lem-pur-vector-integration-site-comparison] to the trivial bundle over each base used here. Its statement gives the coherent specified Tate realization, the equality of the projective-line decompositions and traces, the open-counit restriction to $I_S$, and independence of $r$. Thus the displayed definition of each affine-line $\Gamma$ and its ordered composites is independent of $r$. This cites the coefficient and Kummer comparison as an existing lemma, rather than re-proving it using an empty divisor.

Cited statements: lem-pur-vector-integration-site-comparison

### Original step 2 -> lem-pur-affine-coefficient-counit-normalization

For $K$, choose the bounded constructible etale representative $K^e$ of [lem-sf-proetale-constructible-origin](ii). By [lem-sf-comparison-tor-amplitude](ii) it has the finite Tor interval of $K$, so [lem-pur-vector-integration-site-comparison] compares the actual projection/integration transposes on these inputs. Every scheme in the coordinate and projective compactification towers is finite type over $k$, hence Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and of finite dimension by [lem-kun-dimension-finite-type]. Their projective compactifications therefore have integer dimension bounds. The source inputs are bounded etale-origin objects, so the Hom bijections of [thm-sf-ambient-adjoint-class] apply. Empty schemes have the unique maps between zero objects.

Cited statements: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-pur-vector-integration-site-comparison, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, thm-sf-ambient-adjoint-class

### Original step 3 -> lem-pur-affine-diagonal-integration-orientation

Put $p=p_d$, $X=\mathbf A^d_Y$ and $W=X\times_YX$. The projection $p$ is smooth of pure relative dimension $d$ by [sbc-lem-affine-space-smooth]. The diagonal base-change isomorphism is $\alpha:C(p_1,\Delta)\to\omega_p$ of [lem-pur-diagonal-base-change]; the section invariant is [def-pur-section-invariant]. The diagonal is regular of codimension $d$, with normal bundle $T_{X/Y}$ by [lem-pur-diagonal-regular-immersion]. In coordinates $(x,y)$, the isomorphism $h(x,y)=(x,u=y-x)$ has inverse $(x,u)\mapsto(x,x+u)$, takes $\Delta$ to zero, and sends its conormal basis $y_i-x_i$ to $u_i$. Thus its normal-coordinate basis is unchanged. The schemes and morphisms here are separated finite type by their polynomial charts; for $d=0$ the coordinate lists are empty.

Cited statements: sbc-lem-affine-space-smooth, lem-pur-diagonal-base-change, def-pur-section-invariant, lem-pur-diagonal-regular-immersion

### Original step 4 -> lem-pur-affine-diagonal-integration-orientation

The extracted lemma [lem-pur-affine-translation-trace], applied over $X$ to the section $(x_1,\ldots,x_d)$, says exactly that $h$ preserves the normalized integration. The actual site and transpose comparisons are [lem-pur-vector-integration-site-comparison] and the Hom bijections of [thm-sf-ambient-adjoint-class]. Applying those functors and bijections to the trace equality shows that the integration-transposed comparison is unchanged by $h$. This is the translation argument of the unit model paragraph, including the universal parameter and base-change normalization.

Cited statements: lem-pur-affine-translation-trace, lem-pur-vector-integration-site-comparison, thm-sf-ambient-adjoint-class

### Original step 5 -> lem-pur-affine-diagonal-integration-orientation

For any rank-$d$ trivial bundle $q$, write $P_{q,K}:Lq^*K(d)[2d]\to Rq^!K$ for the integration transpose, which is invertible by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-site-comparison]. The integration is [def-amb-vector-integration]. Put $L=A_X(d)[2d]$, $P=P_{p,A_Y}$, $L'=A_W(d)[2d]$, and $J=P_{p_1,A_X}$. Let $B:Lp_2^*\omega_p\to\omega_{p_1}$ be the specified dualizing base-change map. The trace base-change equation is [lem-amb-affine-space-top-trace], transported by the site comparison just cited. Therefore [lem-pur-trace-transpose-base-change] applied to this square gives $J=B\circ Lp_2^*P$. In [lem-pur-diagonal-base-change], $\alpha=(L\Delta^*B)^{-1}$ under $p_2\Delta=1_X$, and hence
$$\alpha\circ L\Delta^*J=P.$$
The ordinary Tate restriction $L\Delta^*L'=L$ is the coherent restriction already fixed above.

Cited statements: thm-amb-vector-bundle-purity, lem-pur-vector-integration-site-comparison, def-amb-vector-integration, lem-amb-affine-space-top-trace, lem-pur-trace-transpose-base-change, lem-pur-diagonal-base-change

### Original step 6 -> lem-pur-affine-diagonal-integration-orientation

Apply [thm-pur-dnc-invariance] to $(p_1,\Delta)$, obtaining $\delta:C(p_1,\Delta)\xrightarrow{\sim}C(\pi_N,0_N)$. In the global coordinates $u_i=y_i-x_i$ this is a standard affine pair. Its deformation is given by $u_i=t v_i$ and has constant family object by the standard-pair clause of [lem-pur-dnc-section-geometry]. The normalization clause of the DNC theorem makes $\delta$ the identity between these two standard section invariants. Write $\beta=L0_N^*(P_{\pi_N,A_X}^{-1})$, followed by Step 3's ordinary Tate restriction, so $\beta:C(\pi_N,0_N)\to A_X(d)[2d]$. The induced normal coordinates $v_i$ use the same ordered basis as $u_i$, by Step 3. With Step 4's translation invariance, the standard-pair identity says precisely $\beta\delta=(L\Delta^*J)^{-1}$. The explicitly specified diagonal/DNC normalization in the statement and in the middle arrow of [def-pur-smooth-purity-map] is $\theta_p=\beta\delta\alpha^{-1}$. By Step 5,
$$\theta_p=(L\Delta^*J)^{-1}\alpha^{-1}=P_{p,A_Y}^{-1}.$$
This checks the actual normalized arrows; it does not deduce equality merely from existence of isomorphisms to a twist. In rank zero the displayed coordinate lists are empty, the deformation is the constant rank-zero pair, and the same equations are identities.

Cited statements: thm-pur-dnc-invariance, lem-pur-dnc-section-geometry, def-pur-section-invariant, thm-amb-vector-bundle-purity, def-amb-vector-integration, def-pur-smooth-purity-map

### Original step 7 -> lem-pur-affine-coefficient-counit-normalization

The two projection maps at $(L,K)$ and $(\omega_p,K)$ used below are invertible by [lem-weil-finite-compact-projection-formula]. Its source coefficients have bounded constructible etale witnesses: $L$ is the realized shifted Tate line, and the previous DNC computation gives $P:L\xrightarrow{\sim}\omega_p$. Its base coefficient is the witness $K^e$ above, with finite Tor interval by [lem-sf-comparison-tor-amplitude](ii). The separated finite-type projection $p$ therefore satisfies every hypothesis; no Tor condition on an arbitrary source coefficient or six-functor datum is assumed.

Cited statements: lem-weil-finite-compact-projection-formula, lem-sf-comparison-tor-amplitude

### Original step 8 -> lem-pur-affine-coefficient-counit-normalization

By [def-pur-smooth-purity-map] and the DNC computation, smooth purity is $\theta_{p,K}(1\otimes P)$ after the fixed Tate reassociation. Apply [lem-pur-tensor-trace-transpose] with $t=t_p$ and $L=A_X(d)[2d]$. It identifies this map with the transpose of $(1_K\otimes t_p)\Pi_{L,K}$. This is exactly $P_{p,K}$, by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-site-comparison]. Thus the smooth map equals the integration transpose for every $K$. The tensor/counit identification is now a separate lemma; it is not inferred from naturality in $K$ alone.

Cited statements: def-pur-smooth-purity-map, lem-pur-tensor-trace-transpose, thm-amb-vector-bundle-purity, lem-pur-vector-integration-site-comparison

### Original step 9 -> lem-pur-affine-ordered-integration-transposes

For the coordinate tower we need projection compatibility as an identity of maps. For $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, compactify $g$ by $(\mathbf P^1_Y)^d$ and take the compatible compactification triangle for $f$ supplied by [lem-weil-pbc-compatible-compactification-triangle]. All these schemes are finite type over $k$, hence Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated], so the qcqs hypothesis holds and their opens are quasi-compact. The normalized compositor of this triangle is that of [lem-amb-unbounded-compact-support-comparisons]; at the finite pro-etale level its proper/open interchange is the evaluation in [lem-cbc-strict-tower-proper-open-calculus], and with [lem-sf-class-compact-support-comparison] these are the comparisons defining the compositor $\alpha$ of [thm-sf-comp-composition] on the witnessed inputs.

Cited statements: lem-weil-pbc-compatible-compactification-triangle, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-amb-unbounded-compact-support-comparisons, lem-cbc-strict-tower-proper-open-calculus, lem-sf-class-compact-support-comparison, thm-sf-comp-composition

### Original step 10 -> lem-pur-affine-ordered-integration-transposes

For the triangle of the preceding step, [lem-sf-composition-projection-mate] states, for arbitrary ambient finite-coefficient inputs and the counit-defined projection maps of [def-exchange-projection], the identity
$$\operatorname{PF}_{gf;M,N}(\alpha_M\otimes1)
=\alpha_{M\otimes P_fP_gN}\,Rg_!(\operatorname{PF}_{f;M,P_gN})\,\operatorname{PF}_{g;Rf_!M,N},$$
with $P_u=Lu^*$ and the canonical pullback, tensor and direct-image associators inserted. By the preceding step its $\alpha$ is the actual compositor of [thm-sf-comp-composition] on the witnessed inputs used here. No coherence of a six-functor datum is invoked. Clause 3 of [lem-pur-finite-projection-action-laws] gives the tensor-action identity for each compactification projection map.

Cited statements: lem-sf-composition-projection-mate, def-exchange-projection, thm-sf-comp-composition, lem-pur-finite-projection-action-laws

### Original step 11 -> lem-pur-affine-coefficient-counit-normalization

All inverses in the tower calculation are on the domain of [lem-weil-finite-compact-projection-formula]. The source coefficients are shifted Tate lines or their products, and the affine-line direct image of such a line is $A$ by [lem-amb-affine-space-top-trace] and [lem-pur-vector-integration-site-comparison]. Base factors are $K$, its pullbacks, and their tensors with locally free Tate lines. By [lem-sf-pullback-tor-amplitude] these pullbacks are bounded constructible with the same finite Tor interval; tensor with a locally free line preserves it, and a shift translates it. Etale witnesses exist by [lem-sf-proetale-constructible-origin], and their Tor intervals are reflected by [lem-sf-comparison-tor-amplitude](ii). Thus every application of the preceding tensor-interchange and projection identities has the required witnessed bounded-below and finite-Tor inputs.

Cited statements: lem-weil-finite-compact-projection-formula, lem-amb-affine-space-top-trace, lem-pur-vector-integration-site-comparison, lem-sf-pullback-tor-amplitude, lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude

### Original step 12 -> lem-pur-affine-coefficient-counit-normalization

Work first on the ordinary etale site. For a line projection $q$, [lem-asd-ordinary-finite-p1-adjunction] identifies the actual projective-line counit at every coefficient $K$ with coefficient tensor the normalized trace after inverse projection. The explicit affine-line adjunction of [lem-amb-affine-space-top-trace] composes it with extension by zero. Its counit is that projective-line counit composed with $Rq_*$ of the open counit. Naturality of the proper projection map in its first variable, applied to the open counit at $A(1)[2]$, and the compatibility of the open tensor isomorphism with the open counit (clause 2 of [lem-pur-finite-projection-action-laws]) identify its coefficient formula with $(1_K\otimes I_S)\Pi$, where $\Pi$ is built from the compactification projection map of [def-exchange-projection] for $c=(j,q)$. The comparison [lem-pur-vector-integration-site-comparison] carries precisely this formula and its transpose to the specified pro-etale line map $\Gamma_{q,K}$. On the originally named domain this is [def-pur-affine-line-purity-comparison]. The formulas apply at all $n\geq1$ by the exponent independence established above.

Cited statements: lem-asd-ordinary-finite-p1-adjunction, lem-amb-affine-space-top-trace, lem-pur-finite-projection-action-laws, lem-pur-vector-integration-site-comparison, def-pur-affine-line-purity-comparison, def-exchange-projection

### Original step 13 -> lem-pur-affine-ordered-integration-transposes

On the pro-etale site use the explicit affine adjunctions, transported by [lem-pur-vector-integration-site-comparison], from the affine adjunctions $F_d\dashv G_d$ of [lem-amb-affine-space-top-trace], where $G_dK=p_d^*K(d)[2d]$. Inductively their counits have the coefficient formula just established in rank one. Apply [lem-pur-composite-integration-counit] to $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, taking $L_f=A(1)[2]$ and $L_g=A(d)[2d]$. The projection hypotheses are the compositor identity and the compactification tensor-action identity of the preceding steps, on the verified domains. This lemma makes the composite counit $(1_K\otimes t_{p_{d+1}})\Pi$: at the tensor unit it is precisely the trace defining [lem-amb-affine-space-top-trace], and [def-amb-vector-integration] uses that trace on a trivial bundle. The induction starts from the identity adjunction at $d=0$. Thus the integration transpose $P_{p_d,K}$ is the adjunction-preserving comparison with the ordered composite of the explicit line adjunctions.

Cited statements: lem-amb-affine-space-top-trace, lem-pur-composite-integration-counit, def-amb-vector-integration, lem-pur-vector-integration-site-comparison

### Original step 14 -> lem-pur-affine-ordered-integration-transposes

The composition convention on exceptional functors is the conjugate of $\alpha$ specified in [def-pur-affine-space-comparison], using [thm-sf-comp-composition]. Its ordered recursion uses $Rq_d^!Rp_d^!K$ instead of $G_1G_dK$. Naturality of the affine-line transpose gives
$$\Gamma_{q_d,Rp_d^!K}\,Lq_d^*(P_{p_d,K})(1)[2]
=Rq_d^!(P_{p_d,K})\,\Gamma_{q_d,G_dK}.$$
It follows from naturality of the defining projection/integration composite in [def-pur-affine-line-purity-comparison], so substitution identifies the recursion with the composite counit just computed. Here $G_dK$ has the verified finite-Tor domain, and $Rp_d^!K\cong G_dK$ by the earlier integration comparison. The fixed Tate pullback and twist-additivity identifications are those in [def-pur-affine-space-comparison]; all shift factors have even degree. Finally [lem-pur-vector-integration-site-comparison] carries this counit equality and its transposes to the pro-etale site. Hence $P_{p_d,K}=\Gamma_{p_d,K}$; combined with the earlier DNC calculation this is the desired agreement. In rank zero all maps are $1_K$, and the calculation also covers $K=0$.

Cited statements: def-pur-affine-space-comparison, thm-sf-comp-composition, def-pur-affine-line-purity-comparison, lem-pur-vector-integration-site-comparison

## Remaining work and validation

No result is claimed Lean-proved. All three new nodes are statement-only unsplit work for future workers; the parent's theorem still has sorry. None of the old dependencies is deleted from the library; they remain relevant to the extracted arguments even though the short parent cites only the extracted interfaces and the smooth-map definition. The unit record is unchanged because this item is not its key theorem.

The required server dry run and final delivery are run after this report is written; the final results are appended below. The only declared generic tools in the old proof are preserved verbatim above; they belong to the extracted subarguments, not new off-route calls by the parent.

Required server dry run: `deliver.py Q87 lem-pur-projection-purity-agreement --no-push` exited 0 and printed `OK (not pushed) deliver/Q87/lem-pur-projection-purity-agreement at e533e19aa41: preflight passed`. Local JSON inspection additionally confirmed that only proof, proof_deps, proof_origin and split_report changed on the parent; every original proof text remains verbatim in this report, no dependency is missing, and all citation quotes are exact. Final push follows this successful completed dry run.
