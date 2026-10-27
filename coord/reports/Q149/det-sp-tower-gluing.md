# Worker report — Q149 / det-sp-tower-gluing

## Files written

- dag/nodes/sec-smooth-purity/det-sp-tower-gluing.json: existing statement, unchanged; seven-step assembly, 2510 characters, status split.
- dag/nodes/sec-smooth-purity/lem-sp-tower-chart-admissibility.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-coordinate-adjunction.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-binary-ctf-fibre.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-binary-counit-representability.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-evaluated-representability.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-reduction-transpose.json: statement, unsplit; no Mathlib match.
- citations.json: every citation of every assembly step, verbatim from the cited statement.
- report.md: review, exact argument allocation, and retained proof material.

## Attachments

None. The upstream WeilConjectures tree was searched for the blueprint id, tower gluing, compact-support and adjunction notions. No declaration there states this item, with all clauses, sorry-free. General compactification associativity and finite-coefficient operations are insufficient for an attachment. No Lean was written, compiled or built.

## WANTED

None. The current main-20261015 blueprint, ringed-topos prerequisite statements, and Stacks cohomology.tex are present locally. No SGA route is used.

## Repair and current-base comparison

The supplied sandbox contained only .brief2/.brief3/.brief4/.brief5 markers, no nodes, report or search log. I therefore copied the current shared read clone's item, whose retained nineteen steps are exactly the return's 20351-character argument, before writing anything else. There was no earlier sandbox split for which a preliminary dry run could be meaningful. The current released stage-1 repair note keeps the statement and route. The inherited reviewed and tool_uses records remain maintainer-owned; this delivery changes only split-owned fields. Delivery preparation overlays those fields on the fetched current server base. The six new statements have proof=[], proof_deps=[], proof_origin=null and status=unsplit. They have comparable mathematical size, approximately 2.8–3.3 thousand characters including their fully repeated coefficient/category hypotheses. None restates the whole item. The item does not cite its own conclusion through an alias.

The earlier blueprint corrections are retained: use the Rj_* fibre, not the unshifted cone (when U=V=X and the transition is identity, the latter has the wrong shift); apply the etale fibre sum before the affine integration. The new reduction lemma retains the global counit transpose, rather than inferring equality of derived maps from their restrictions or finite evaluations. No new statement dispute or target change is made.

## Not duplicates

- lem-sp-tower-chart-admissibility vs lem-sp-etale-ctf-chart-domain: the latter concerns finite constant rings and preservation, not actual strict towers, simultaneous precise cohomology/Tor shifts, their bounded-below domains and all open compact-support windows.
- lem-sp-tower-chart-admissibility vs lem-sp-etale-pullback-twist-tor-window: the latter concerns a supplied finite etale flat representative; the new assertion concerns ordinary proetale derived towers, intrinsic constructibility, etale-origin witnesses and uniform intervals.
- lem-sp-tower-chart-admissibility vs det-sp-tower-bound-uniform: that existing node supplies the compact-support bound; it does not supply pullback/Tate chart admissibility or the finite-level domain checks. The new statement explicitly cites it for that subclause.
- lem-sp-tower-coordinate-adjunction vs lem-sp-chart-finite-ring-adjunction: the latter gives finite-ring adjunctions transported through comparison; the new assertion constructs actual maps in the ordinary varying-ring tower derived category, retaining the ordered Tate identification and its quotient transitions.
- lem-sp-tower-coordinate-adjunction vs det-sp-tower-p1-adjunction: the latter is the projective-line input, not the open affine restriction, ordered iteration and etale chart composition. It is cited in the new statement.
- lem-sp-tower-binary-ctf-fibre vs lem-sp-ringed-topos-binary-descent: the latter is ambient module descent; the new assertion identifies the proetale tower slice rings and proves that the fibre is in the uniform constructible finite-Tor subcategory with the same intervals. The ambient direct images need not be constructible.
- lem-sp-tower-binary-ctf-fibre vs lem-sp-ringed-topos-fibre-restriction: the latter identifies ambient fibre projections without even requiring a cover; it asserts neither intrinsic constructibility nor common finite-level Tor bounds.
- lem-sp-tower-binary-counit-representability vs det-sp-representing-pair-gluing: the latter is stated only for Z/ell^n coefficients and starts with a global counit. The new assertion obtains the actual tower counit from compatible local pairs and proves its representing bijection by the signed Hom diagram.
- lem-sp-tower-evaluated-representability vs det-sp-tower-evaluation-adjoint: the latter is the abelian right adjoint to evaluation, not finite representability of an evaluated chart-normalized pair on arbitrary finite ctf tests.
- lem-sp-tower-evaluated-representability vs det-sp-representing-pair-uniqueness: the latter gives finite Z/ell^n uniqueness and a Brown pair, not representability against all O_E/ell^n test objects of a given evaluated tower pair.
- lem-sp-tower-reduction-transpose vs det-sp-reduction-exceptional: the latter defines and proves the finite coefficient comparison. The new assertion determines the reduction morphism of an actual, not necessarily normalized, derived tower from its global counit, with explicit b_f normalization and triple reductions.
- lem-sp-tower-reduction-transpose vs lem-pur-integral-reconstructed-representing-pair: that node reconstructs a completed integral pair from supplied normalized systems and a Brown comparison; the new assertion is a quotient-transition identity before reconstruction and allows nonnormalized towers.
- lem-sp-tower-reduction-transpose vs lem-pur-reconstructed-pair-refinement-coherence: the latter handles compactification refinement of reconstructed integral pairs; the new assertion concerns finite coefficient quotient transitions of a supplied ordinary tower counit.

No new source record uses a Stacks tag merely borrowed from an existing node. Each new node is an agent-stated extraction from a precise paragraph of the current blueprint proof. Stacks 08DG, label lemma-glue, and 08BU, label lemma-exact-sequence-lower-shriek in cohomology.tex were read to verify the existing ringed-topos route, not presented as sources already proving strict tower constructibility. The full DAG was searched by chart, binary descent, uniform Tor, evaluation, representing pairs, reduction transitions and exact source tags. tools/blueprint_refs.py ancestor confirms the ancestor is det-sp-tower-gluing; its search found no blueprint statement replacing one of these six complete assertions. The existing lem-sp-smooth-admissible-coordinate-cover is reused for the geometric cover instead of inventing a seventh node.

## Mathlib searches

For each new id, searches ran through the mandated msearch.py under Q149/det-sp-tower-gluing: LeanFinder with two distinct semantic phrasings, LeanSearch, Loogle (including a second more targeted pattern), and two source grep patterns. Exact commands, tool output and service availability are retained in searches.jsonl and the per-id *-search-results.json files; mathlib_searches copies the actual text without invented declarations. All semantic services responded in this run. The additional Loogle pattern mentioning AlgebraicGeometry.IsSmooth reports an unknown identifier; this is recorded as an unsuccessful query, not as evidence of absence. Successful broad and targeted patterns remain recorded as well.

I read the resulting signatures and relevant Mathlib source: Adjunction.Basic homEquiv and composition, Adjunction.Evaluation ordinary functor-category evaluation adjoints, Sites.SheafCohomology.MayerVietoris the Ext sequence of an abelian sheaf, AlgebraicGeometry.Sites.Representability Zariski sheaves represented by schemes, Functor.Derived.Adjunction localization-derived adjunctions, and ModuleCat.ChangeOfRings ordinary module scalar adjunctions. None supplies the asserted geometric tower categories, domains and prescribed counit comparisons in one specialization. Hence all six nodes remain unsplit, with zero Mathlib leaves. The original item's existing searches are preserved and an additional semantic search is appended.

## Review by Q149

I read the current blueprint gluing statement and all five paragraphs of its proof, the chapter and tower-geometric unit records, GOAL.md, the three-level route rules in SETUP.md, the released re-split order, and delivery-errors B–E. I also read Stacks cohomology.tex at lemma-glue (08DG) and lemma-exact-sequence-lower-shriek (08BU). For each new node the source is the precise corresponding paragraph of that same current blueprint, with the original step numbers in source.place. The assertions are agent-expanded statements of the arguments the retained proof carried, rather than a claim that the short blueprint or Stacks already contains those tower lemmas verbatim.

Step 1 uses the entire finite-cover statement of lem-sp-smooth-admissible-coordinate-cover (including the original-base etale map, separatedness, finite type, Noetherianity and the empty cover) and the precise intervals/domain assertion of lem-sp-tower-chart-admissibility. The latter checks finite Noetherian A_n using exponent en, separate etale-origin witnesses, exact inverse image and flat models, rank-one twists, and the geometric fibre bound for every open restriction. The source of compact-support bounds is the existing det-sp-tower-bound-uniform, whose exact [s,t+2d] interval was read. No completed or condensed category is silently substituted.

Step 2 uses the explicit Hom bijection and sum-before-integration counit in lem-sp-tower-coordinate-adjunction. Its statement includes actual tower morphisms, compatibility of finite Kummer identifications with z↦z^ell, the intermediate affine-line adjunction, d=0, and evaluation of finite units/counits. I checked det-sp-tower-p1-adjunction's actual bounded-below etale-origin-level domain and lem-sp-coefficient-tower-shriek-calculus's open/etale adjunction and preservation clauses. General adjunction composition alone would not verify those domains or the twist maps.

Step 3 uses the restriction/overlap and representing-counit conclusions of lem-sp-tower-binary-counit-representability and the existence plus common-interval conclusion of lem-sp-tower-binary-ctf-fibre. Both statements were opened after writing and their cited sentence was copied verbatim into citations.json. The induction starts with one chart, and the overlap is an open of the last chart, so no affine-intersection assumption is used. The fibre lemma preserves Tor amplitude by testing every degree-zero coefficient module after open restriction; constructibility follows by refining the finitely many local stratifications on a Noetherian scheme. The counit lemma retains the signed cancellation, existence of its lift, the two shifted Hom sequences and the full five-term chase; it does not assert a unique lift or unique arbitrary derived gluing.

Step 4 uses the open-restriction assertion in the binary counit lemma, which applies to any smaller open, not just the chosen atlas. Comparing two natural Hom bijections gives both directions of the isomorphism; injectivity makes the composites identities. Thus every coordinate chart has the required pair. This is stronger than checking just the cover charts and uses the explicit open-adjunction counit.

Step 5 is the retained elementary uniqueness/functor argument, verbatim. The two representing bijections give a and b; their injectivity gives ba=1 and ab=1. For u:K→L the transpose equation determines G(u); applying it twice gives identities, composition and K-naturality. The transpose of 1_FM gives the unit and the same injectivity gives both triangle equations. No general representability theorem or functorial cone selection is hidden here.

Step 6 cites the precise finite-test representability statement and natural/unit compatibility of lem-sp-tower-evaluated-representability. I checked exact evaluation in det-sp-coefficient-towers-abelian, the unrestricted finite-evaluation clause (1) of det-sp-tower-shriek-levels, and finite etale-origin comparison in det-pe-finite-tor-comparison-noetherian. The extra global algebraically-closed-field projection-formula hypothesis of shriek-levels (2a) is never invoked. The Hom argument quantifies over arbitrary finite ctf M; no lift of M to a tower is assumed. Uniqueness is applied only after that finite representability is established.

Step 7 uses the exact reduction formula in lem-sp-tower-reduction-transpose with the finite counit comparisons from Step 6 and the same compactification throughout. I read the normalization of b_f and the nonflat scalar extension assertions in det-sp-reduction-direct-image and det-sp-scalar-extension-functor, the actual reduction formula in tower-shriek-calculus (3), and the defining transpose of c in det-sp-reduction-exceptional. The common annihilator is ell^n for A_n and A_m. The global equality comes from the actual tower counit reduction square, with b_f inverted in the correct direction. Its source is F_m((G_n)_Am), its target K_m. Finite adjunction injectivity gives the reduction formula; no local equality test on derived morphisms is used.

For B I checked that every new file has a self-contained coefficient/scheme/category introduction, exact notation and statement dependencies; no proof steps or proof dependencies are supplied. For C I reread each statement the assembly cites and copied the mathematical part it takes verbatim. All other non-elementary arguments have allocated statements; the detailed old uses are preserved in the argument material below, so subsequent workers need not guess them. For D the six nodes are strictly smaller arguments: none gives global existence, functoriality, chart form and reductions all together. For E I checked empty X and empty overlap, U=V=Z, one chart and d=0, arbitrary finite ctf test objects, ramified E (exponent en, not n), identity n=m, triple n≥m≥r, and nonnormalized towers. Taking U=V=Z recovers G rather than G[1]. Binary descent uses actual slice module categories and does not require constructibility of intermediate Rj_*. Scalar quotients may have infinite projective dimension; no flatness assumption is inserted.

The corrected points in this repair are the old workload concentration and the possible duplicate coordinate-cover argument. I split the former into the six statements and reused the existing geometric cover for the latter. The old nineteen arguments are retained verbatim below and allocated exactly, including all displayed transpose formulas and both five-term chases. The old statement is byte-for-byte unchanged. All seven assembly steps are shorter than 2000 characters and the total is below 3000. No work outside the authorized stage-1 sandbox was done.

## Argument allocation and retained source material

Old step 1 (finite coordinate cover) is supplied by the existing lem-sp-smooth-admissible-coordinate-cover; its open restriction permanence is also retained in the binary-restriction and admissibility statements. Old step 11 (finite-cover induction and every-chart comparison) is the assembly's Steps 3–4. Old step 12 is the assembly's Step 5 verbatim. Every other old step is allocated to a new statement below. The following is supporting argument material in the report, not proof steps inside any unsplit new node.

### lem-sp-tower-chart-admissibility

This new node retains old steps 2, 3, 4.

Old step 2:

The finite levels in [sk-def-sp-normalized-towers] are already the ordinary derived categories over the constant rings $A_n$, with intrinsic constructibility and Tor amplitude as in [def-weil-proetale-constructible-sheaf] and [def-weil-proetale-tor-amplitude]. No condensed or completed category comparison is needed. By [def-weil-l-adic-coefficient-extension], writing $\ell=u\varpi_E^e$ gives $A_n=\mathcal O_E/\varpi_E^{en}$, a finite commutative ring. A finite ring is Noetherian since its set of ideals is finite. All schemes under consideration, including opens and intermediate affine/projective spaces, are separated finite-type $k$-schemes; Step 1's argument makes them Noetherian and qcqs. Hence the equivalence in [det-pe-finite-tor-comparison-noetherian] supplies an etale-origin witness for each ctf level, preserving its specified Tor interval. These witnesses are chosen separately at each level, with no assertion that they form a tower. Uniform cohomological vanishing makes the tower bounded below: cohomology in the Grothendieck tower category is levelwise by [det-sp-coefficient-towers-abelian].

Cited statements: sk-def-sp-normalized-towers, def-weil-proetale-constructible-sheaf, def-weil-proetale-tor-amplitude, def-weil-l-adic-coefficient-extension, det-pe-finite-tor-comparison-noetherian, det-sp-coefficient-towers-abelian.

Old step 3:

Check the proposed local object $H_UK=e^*p_d^*K(d)[2d]$ belongs to the tower category. By [sk-lem-sp-tower-levels], inverse image on towers is exact and computed levelwise. It preserves intrinsic constructibility [def-weil-proetale-constructible-sheaf]: pull back a finite locally closed stratification and each constant finite-module local model; on our Noetherian schemes these pulled-back locally closed strata are constructible. For Tor amplitude $[u,v]$, [lem-sf-flat-model] gives a flat model supported in that precise interval, and [lem-weil-pbc-ringed-topos-flat-module-pullback] says its inverse-image terms remain flat. Exact inverse image preserves the quasi-isomorphism, so the interval is unchanged. Here the flat-model coefficient is the uniformizer quotient of exponent $en$, exactly our $A_n$. The finite twist is locally free of rank one by [lem-pur-twist-sheaf-locally-free], so tensoring with it preserves these conditions. Thus if $K_n$ has cohomological support $[a,b]$ and Tor interval $[u,v]$, $H_UK_n$ has the intervals $[a-2d,b-2d]$ and $[u-2d,v-2d]$, independently of $n$. These are precisely the membership requirements of [sk-def-sp-normalized-towers]. The same reasoning applies to each intermediate inverse image and twist.

Cited statements: sk-lem-sp-tower-levels, def-weil-proetale-constructible-sheaf, lem-sf-flat-model, lem-weil-pbc-ringed-topos-flat-module-pullback, lem-pur-twist-sheaf-locally-free, sk-def-sp-normalized-towers.

Old step 4:

Every open restriction $f|_Z$ is smooth by [lem-weil-pbc-smooth-restrict-open-subschemes]. Its fibres are open in the pure-$d$ smooth fibres of $f$, so every nonempty fibre still has pure dimension $d$. The geometric-point base changes preserve that relative dimension by [lem-sbc-smooth-relative-dimension-permanence](1). Thus [sk-lem-sp-tower-bound] makes $F_Z=R(f|_Z)_{!,\bullet}$ a functor between the uniform ctf tower categories. More explicitly [det-sp-tower-bound-uniform], with finite ordinary rings $A_n$ and the etale-origin witnesses of Step 2, gives Tor interval $[u,v+2d]$ and cohomology vanishing outside the same interval whenever the input levels have common Tor interval $[u,v]$. This verifies the required compact-support preservation hypotheses at every open and intermediate projection used below.

Cited statements: lem-weil-pbc-smooth-restrict-open-subschemes, lem-sbc-smooth-relative-dimension-permanence, sk-lem-sp-tower-bound, det-sp-tower-bound-uniform.

### lem-sp-tower-coordinate-adjunction

This new node retains old steps 5, 6.

Old step 5:

Let $q:\mathbf P^1_S\to S$, $j:\mathbf A^1_S\hookrightarrow\mathbf P^1_S$ and $p=qj$, for each intermediate base $S$. Here $\ell$ is invertible, and Step 2 supplies bounded-below etale-origin domains for every ctf tower used. The extension $j_!M$ is again ctf by [lem-sp-coefficient-tower-shriek-calculus](2). Consequently the actual $\mathscr C^+$ domains and the ctf restriction of [det-sp-tower-p1-adjunction] apply, with no need for compatible etale witnesses. Its adjunction and the open adjunction of the calculus give
$$\operatorname{Hom}(Rp_{!,\bullet}M,K)=\operatorname{Hom}(Rq_{*,\bullet}j_{!,\bullet}M,K)\simeq\operatorname{Hom}(j_{!,\bullet}M,q^*_\bullet K(1)[2])\simeq\operatorname{Hom}(M,p^*_\bullet K(1)[2]).$$
The functor identification is the compactification composition/open normalization of the calculus. The adjunction maps are actual tower morphisms and evaluate to the finite maps, by both cited statements.

Cited statements: lem-sp-coefficient-tower-shriek-calculus, det-sp-tower-p1-adjunction.

Old step 6:

The finite twist identification [lem-pur-finite-kummer-level] applies with uniformizer exponent $en$ and $N=n$. Pullback of a root of unity commutes with $u\mapsto u^\ell$, since pullback preserves multiplication; after extending scalars these finite identifications therefore give compatible maps of twist towers. Use the monoidal derived pullback isomorphism [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] on the ringed inverse-system topoi and the tensor-power definition [def-coefficient-twists-detailed]. Tensor associators then identify successive pulled-back twists with their sum twist as an actual tower isomorphism, before evaluating. Compose the Hom bijections of Step 5 for the $d$ affine-line projections and then with the etale adjunction $e_!\dashv e^*$ of [lem-sp-coefficient-tower-shriek-calculus]. This gives the chart pair $(H_UK,\varepsilon_U)$ with $H_UK=e^*p_d^*K(d)[2d]$. For $d=0$ use the identity projection adjunction. The composite counit is $\varepsilon_{p_d}\circ Rp_{d!}(\varepsilon_e)$: fibre summation precedes integration. All its finite evaluations have the specified finite counits and units. Conservativity is used only to test invertibility of constructed comparisons, never to infer equality of derived tower morphisms.

Cited statements: lem-pur-finite-kummer-level, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-coefficient-twists-detailed, lem-sp-coefficient-tower-shriek-calculus.

### lem-sp-tower-binary-ctf-fibre

This new node retains old steps 8.

Old step 8:

By [det-sp-coefficient-towers-abelian], the coefficient towers on $Z$ are modules over the ring object $\mathcal O_{E,Z}/\ell^\bullet$ in the Grothendieck topos of inverse systems of pro-etale sheaves. The constant inverse systems of the subterminal sheaves $U,V,W$ are open subtopoi with $U\cup V=Z$. For each open $D=U,V,W$, [lem-weil-proetale-weakly-etale-localization](1) identifies $D_{\mathrm{proét}}$ with $Z_{\mathrm{proét}}/D$, and (2) identifies the restricted constant ring $A_n$ with its constant ring on $D$. These identifications preserve the constant-section quotient maps $A_n\to A_m$. Applying them levelwise identifies the slice module category with the coefficient-tower category on $D$: its objects and arrows are the restricted module sheaves and semilinear transitions. Apply [lem-sp-ringed-topos-binary-descent](1) in this ringed topos to $G_U,G_V,c$. It gives an actual object $G\in D(\operatorname{Tow}(Z,\mathcal O_E))$ with the prescribed restrictions. Concretely it is the fibre, not the unshifted cone, of
$$Rj_{U*}G_U\oplus Rj_{V*}G_V\longrightarrow Rj_{W*}(G_V|_W).$$
The intermediate derived direct images need not be constructible; the glued object is. Exact restriction and evaluation show its cohomology vanishes outside the common local interval. Each cohomology sheaf is intrinsically constructible by [def-weil-proetale-constructible-sheaf]: combine the finitely many local stratifications, refining their finitely many intersections and complements to a finite locally closed stratification of the Noetherian scheme. The same restriction test applied to $G_n\otimes^L N$ gives its common Tor interval. A sheaf vanishing on both members is zero by the sheaf condition. Consequently $G$ belongs to the category of [sk-def-sp-normalized-towers].

Cited statements: det-sp-coefficient-towers-abelian, lem-sp-ringed-topos-binary-descent, def-weil-proetale-constructible-sheaf, sk-def-sp-normalized-towers, lem-weil-proetale-weakly-etale-localization.

### lem-sp-tower-binary-counit-representability

This new node retains old steps 7, 9, 10.

Old step 7:

Suppose $U,V$ cover an open $Z\subseteq X$, with pairs $(G_U,\varepsilon_U)$ and $(G_V,\varepsilon_V)$ already representing the local functors; put $W=U\cap V$. For an open inclusion $i:W\hookrightarrow U$, [lem-sp-coefficient-tower-shriek-calculus] gives $F_W=F_Ui_!$ and $i_!\dashv i^*$, with $i_!$ preserving the constructible tower category. Thus
$$\operatorname{Hom}(N,G_U|_W)\simeq\operatorname{Hom}(i_!N,G_U)\simeq\operatorname{Hom}(F_WN,K).$$
The associated counit is $\varepsilon_U\circ F_U(i_!i^*G_U\to G_U)$. With $i_V:W\hookrightarrow V$ the second restriction has the bijection $\operatorname{Hom}(N,G_V|_W)\simeq\operatorname{Hom}(i_{V!}N,G_V)\simeq\operatorname{Hom}(F_WN,K)$ and counit $\varepsilon_V\circ F_V(i_{V!}i_V^*G_V\to G_V)$. There is a unique counit-preserving isomorphism $c:G_U|_W\to G_V|_W$: apply the second representing bijection to the first counit to get $c$, and reverse the roles to get its inverse; injectivity of the two bijections makes both composites identities. This argument uses representing pairs on $W$, rather than asserting that arbitrary local derived isomorphisms glue uniquely.

Cited statements: lem-sp-coefficient-tower-shriek-calculus.

Old step 9:

Apply [lem-sp-ringed-topos-binary-descent](2) to $G$ and then the exact compact-support functor $F_Z$ of [lem-sp-coefficient-tower-shriek-calculus]. The result is the triangle
$$F_W(G|_W)\to F_U(G|_U)\oplus F_V(G|_V)\to F_ZG\longrightarrow.$$
Under the selected restriction isomorphisms, the map $(\varepsilon_U,\varepsilon_V)$ to $K$ kills the first arrow: its two components are the same overlap counit by the definition of $c$ in Step 7, and the first arrow has signs $(1,-1)$. By [lem-weil-pbc-hom-out-of-triangle-exact](i) it factors through a map $\varepsilon:F_ZG\to K$. This is the needed global counit. Only existence of this lift has been used.

Cited statements: lem-sp-ringed-topos-binary-descent, lem-sp-coefficient-tower-shriek-calculus, lem-weil-pbc-hom-out-of-triangle-exact.

Old step 10:

For arbitrary $M$ in the constructible tower category, apply the two contravariant functors $\operatorname{Hom}(-,G)$ and $\operatorname{Hom}(F_Z(-),K)$ to the open-cover triangle of Step 9 with $M$ in place of $G$. The arrows $\theta_N:a\mapsto\varepsilon F_Z(a)$ form a morphism of these exact Hom sequences: for each triangle arrow $t:N\to N'$ one has $\varepsilon F_Z(a\circ t)=\varepsilon F_Z(a)\circ F_Z(t)$, including the shifted boundary arrow. Exactness at all positions follows by rotations and shifts from [lem-weil-pbc-hom-out-of-triangle-exact]. By [lem-sp-coefficient-tower-shriek-calculus] and the local adjunctions, $\theta$ is a bijection on all shifts of $j_{U!}(M|_U)$, $j_{V!}(M|_V)$ and $j_{W!}(M|_W)$. Indeed transposing $a:j_{U!}N\to G$ gives $a_U:N\to G_U$, and $\theta(a)=\varepsilon_UF_U(a_U)$ by the restriction equation of Step 9. For $D=U,V,W$, let $j_D:D\hookrightarrow Z$ and let $\varepsilon_D$ be the restricted representing counit. For every integer $t$, the open adjunction sends $a:j_{D!}(N[t])\to G$ to $a_D:N[t]\to G|_D$, and the restriction equation gives $\theta(a)=\varepsilon_DF_D(a_D)$. Thus each shifted vertical map is exactly the corresponding local representing bijection. In the five-term segment of the two exact sequences with $\theta_M$ in the centre, the other four vertical arrows are bijective. To see the central bijectivity directly, lift the image of a bottom central element to the top term on its right; its next image is zero by the rightmost injection, so exactness lifts it to the top centre, and the residual bottom element comes from the left and can be lifted using the left surjection. For injectivity a central kernel element has zero right image, hence comes from the top left; its bottom left image lies in the image of the preceding bottom term, which lifts by the leftmost surjection, leaving zero by the adjacent left injection. Thus $\theta_M$ is a bijection, natural in $M$. This proves representability of $(G,\varepsilon)$.

Cited statements: lem-sp-ringed-topos-binary-descent, lem-sp-coefficient-tower-shriek-calculus, lem-weil-pbc-hom-out-of-triangle-exact.

### lem-sp-tower-evaluated-representability

This new node retains old steps 13, 14, 15, 16.

Old step 13:

Evaluation at $n$ is exact by [det-sp-coefficient-towers-abelian], so it descends to a triangulated functor by [lem-sf-exact-functor-derived-triangulated]. The input towers here are bounded below by their uniform bounds. Thus [det-sp-tower-shriek-levels](1) identifies the evaluated compact-support functor with the finite operation for the same chosen compactification. The open extension and its evaluated adjunction maps are those of [lem-sp-coefficient-tower-shriek-calculus](2). By [det-sp-tower-p1-adjunction] and the compositions in Steps 5–6, evaluated chart counits and units are the finite ones. Only the unrestricted evaluation clause of det-sp-tower-shriek-levels is used; its projection formula with the extra algebraically closed finite-field hypothesis is not invoked.

Cited statements: det-sp-coefficient-towers-abelian, lem-sf-exact-functor-derived-triangulated, det-sp-tower-shriek-levels, lem-sp-coefficient-tower-shriek-calculus, det-sp-tower-p1-adjunction.

Old step 14:

Prove finite representability by induction on the same chart cover as Step 11. The empty case is the zero category. For a single chart the finite chart adjunction is obtained by the same composed Hom bijections as Steps 5–6. All finite ctf test objects and their open extensions admit etale-origin witnesses by [det-pe-finite-tor-comparison-noetherian] on our qcqs schemes over finite Noetherian $A_n$; hence the stated finite projective-line domains apply, not merely objects that lift to a tower. For the induction step write $Z=U\cup V$, $W=U\cap V$, and evaluate the constructed pair to $(G_{Z,n},\varepsilon_{Z,n})$. Its restrictions have the finite representing counits by the induction hypothesis, the finite chart case on $V,W$, and the evaluated restriction equation of Step 9. For arbitrary finite ctf $M$ on $Z$, [lem-sp-ringed-topos-binary-descent](2) gives the triangle $A\to B\to M\to A[1]$, with $A=j_{W!}(M|_W)$ and $B=j_{U!}(M|_U)\oplus j_{V!}(M|_V)$. These terms stay ctf by [lem-sp-coefficient-tower-shriek-calculus](2). No lift of $M$ to a tower is assumed.

Cited statements: det-pe-finite-tor-comparison-noetherian, det-sp-tower-p1-adjunction, lem-sp-ringed-topos-binary-descent, lem-sp-coefficient-tower-shriek-calculus.

Old step 15:

The rotations and shifts of [lem-weil-pbc-hom-out-of-triangle-exact] give the exact segment
$$\operatorname{Hom}(B[1],G_{Z,n})\to\operatorname{Hom}(A[1],G_{Z,n})\to\operatorname{Hom}(M,G_{Z,n})\to\operatorname{Hom}(B,G_{Z,n})\to\operatorname{Hom}(A,G_{Z,n})$$
and the segment with terms $\operatorname{Hom}(F_{Z,n}(-),K_n)$. The vertical maps are $a\mapsto\varepsilon_{Z,n}F_{Z,n}(a)$. For every triangle arrow $t$, including its shifted boundary, $\varepsilon_{Z,n}F_{Z,n}(a\circ t)=\varepsilon_{Z,n}F_{Z,n}(a)F_{Z,n}(t)$, proving commutativity. The open adjunctions of [lem-sp-coefficient-tower-shriek-calculus] and the evaluated restriction equation identify the four outer vertical maps with local representing bijections on the appropriate shifts. The central map is bijective by the explicit five-term chase of Step 10: lift the right image, use exactness to lift centrally, and lift the residual from the left; for a kernel element lift from the left and subtract the lift from the preceding term. This proves finite representability for all $M$ and completes induction.

Cited statements: lem-weil-pbc-hom-out-of-triangle-exact, lem-sp-coefficient-tower-shriek-calculus.

Old step 16:

The constructible adjunction in [det-sp-reduction-exceptional] is on the ordinary constant-ring finite-Tor categories in our standing scheme setting and for the same coefficient-independent compactification. Its hypotheses hold: $f$ is smooth of pure dimension $d\geq0$ and $A_n$ is finite and annihilated by $\ell^n$. Its finite representing pair therefore has a unique counit-preserving comparison $G_n\simeq f^!_{A_n}K_n$, by the elementary uniqueness argument of Step 12. Evaluating $\varepsilon_LF(G(u))=u\varepsilon_K$ identifies the action on each tower morphism with that of the finite adjoint. Evaluating $\varepsilon_{FM}F(\eta_M)=1$ gives the finite transpose equation for $1_{F_nM_n}$. Injectivity of the finite bijection identifies the units as well. This proves the level, counit and unit assertions of clause 3.

Cited statements: det-sp-reduction-exceptional.

### lem-sp-tower-reduction-transpose

This new node retains old steps 17, 18, 19.

Old step 17:

Use the chosen compactification $f=\bar f j$ of [sk-def-sfb-dc-setting], the same one used in [det-sp-tower-shriek-levels](1). Apply [det-sp-reduction-direct-image] with $A=A_n$, $B=A_m$, $M=G_n$, and this compactification. The rings are finite by [def-weil-l-adic-coefficient-extension]: $A_n=\mathcal O_E/\varpi_E^{en}$, $A_m=\mathcal O_E/\varpi_E^{em}$, for $\ell=u\varpi_E^e$. Since $1\leq m\leq n$ the quotient map is unital and both rings are killed by $\ell^n$. The object $G_n$ is in the ordinary ctf category by Steps 3, 8 and 16, and $f$ is separated finite type. Hence the canonical comparison is an isomorphism
$$b_f(G_n):(R\bar f_*j_!G_n)\otimes^L_{A_{n,Y}}A_{m,Y}\xrightarrow{\sim}R\bar f_*j_!(G_n\otimes^L_{A_{n,X}}A_{m,X}).$$
Its proper part is the $A_m$-linear adjoint transpose of the $A_n$-counit after extension of scalars, followed by the canonical open-extension tensor comparison, exactly the normalization of the cited statement. No flatness or finite projective dimension of $A_m$ over $A_n$ is required.

Cited statements: sk-def-sfb-dc-setting, det-sp-tower-shriek-levels, det-sp-reduction-direct-image, def-weil-l-adic-coefficient-extension.

Old step 18:

Write $r_G:(G_n)_{A_m}\to G_m$ and $r_K:(K_n)_{A_m}\to K_m$ for the natural reduction maps of [det-sp-coefficient-towers-abelian]. The counit-preserving comparisons from Step 16 are fixed throughout. The comparison $b_f(G_n)$ just specified is the one in [lem-sp-coefficient-tower-shriek-calculus](3); therefore $r^{FG}_{n,m}=F_{f,m}(r_G)b_f(G_n)$. Naturality of the reduction map for the actual tower counit $\varepsilon:FG\to K$ gives
$$\varepsilon_mF_{f,m}(r_G)b_f(G_n)=r_K(\varepsilon_n)_{A_m},$$
and hence
$$\varepsilon_mF_{f,m}(r_G)=r_K(\varepsilon_n)_{A_m}b_f(G_n)^{-1}.$$
Both sides have source $F_{f,m}((G_n)_{A_m})$ and target $K_m$. The inverse exists by Step 17. This equality is in the global derived category, not an inference from equalities on chart restrictions.

Cited statements: det-sp-coefficient-towers-abelian, lem-sp-coefficient-tower-shriek-calculus.

Old step 19:

For [det-sp-reduction-exceptional], the unital coefficient quotient $A_n\to A_m$ has common annihilator $N=\ell^n$ and uses the same coefficient-independent compactification and ordinary ctf categories as above. The finite identifications from Step 16 preserve precisely its counits. Apply its defining transpose equation to $K_n$ and use naturality of the finite counit:
$$\begin{aligned}
\varepsilon_mF_{f,m}\bigl(f^!_{A_m}(r_K)c_{n,m}(K_n)\bigr)
&=r_K\varepsilon_{m,(K_n)_{A_m}}F_{f,m}(c_{n,m}(K_n))\\
&=r_K(\varepsilon_n)_{A_m}b_f(G_n)^{-1}.
\end{aligned}$$
These are the same source and target as in Step 18. Scalar extension preserves ctf here by [det-sp-scalar-extension-functor], so the finite adjunction may be tested on $(G_n)_{A_m}$. Injectivity of its Hom bijection gives $r_G=f^!_{A_m}(r_K)c_{n,m}(K_n)$, the required reduction formula without any normalization assumption. For $n=m$ the quotient reductions and comparisons are identities. For $n\geq m\geq r$, the composition clause of [det-sp-reduction-direct-image] and the reduction composition law of [det-sp-coefficient-towers-abelian] identify both iterated transposes with the transpose for $A_n\to A_r$.

Cited statements: det-sp-reduction-exceptional, det-sp-scalar-extension-functor, det-sp-reduction-direct-image, det-sp-coefficient-towers-abelian.

### Retained assembly arguments

Old step 1:

Fix $K=K_\bullet$ and abbreviate $F_Z=R(f|_Z)_{!,\bullet}$ for opens $Z\subseteq X$. The standing schemes are Noetherian: a field has just the ideals $0,(1)$ and [lem-weil-pbc-finite-type-over-noetherian] applies to the structure morphisms. The statement [lem-weil-pbc-noetherian-open-subscheme-noetherian] then says that $X$ and every open in it are Noetherian and quasi-compact. By [lem-sc-standard-smooth-local-relative-dimension] every point has a standard-smooth affine neighbourhood of relative dimension $d$ over an affine open $T\subseteq Y$. The etale polynomial chart of [lem-sc-standard-smooth-etale-polynomial-chart] gives $U\to\mathbf A^d_T$; composing with $\mathbf A^d_T\hookrightarrow\mathbf A^d_Y$ remains etale by [lem-weil-pbc-etale-composition-cancellation]. Thus choose a finite cover $X=\bigcup_{i=1}^rU_i$ by such charts. Every open subset of a chart is again a chart by the same etale composition statement. If $X$ is empty, the zero pair represents the zero functor; henceforth use induction on $r\geq1$.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-sc-standard-smooth-local-relative-dimension, lem-sc-standard-smooth-etale-polynomial-chart, lem-weil-pbc-etale-composition-cancellation.

Old step 11:

Use induction on the finite cover in Step 1. For a single chart the pair is Step 6. Given the pair on $Z=U_1\cup\cdots\cup U_{r-1}$, use $U=Z$, $V=U_r$ in Steps 7–10. The intersection is an open of the chart $U_r$, so its chart pair is available, and Step 7 also identifies the restriction of the pair from $Z$ with it. This constructs the pair on $X$. For an additional coordinate chart $j:D\hookrightarrow X$, the open adjunction $j_!\dashv j^*$ and the open normalization $F_Xj_!=F_D$ of [lem-sp-coefficient-tower-shriek-calculus](1),(2) give $\operatorname{Hom}(N,G|_D)\simeq\operatorname{Hom}(j_!N,G)\simeq\operatorname{Hom}(F_DN,K)$, with counit $\varepsilon F_X(j_!j^*G\to G)$. The unique counit-preserving comparison of representing pairs therefore identifies $G|_D$ with the chart pair in Step 6. This proves clause 1 for every chart, not just the chosen atlas.

Cited statements: lem-sp-coefficient-tower-shriek-calculus.

Old step 12:

If $(G,\varepsilon)$ and $(G',\varepsilon')$ represent the same functor, take $M=G$ in the second bijection to obtain the unique $a:G\to G'$ with $\varepsilon'F(a)=\varepsilon$. Reversing the roles gives $b:G'\to G$; injectivity gives $ba=1$ and $ab=1$. For $u:K\to L$, define $G(u)$ as the unique map with $\varepsilon_LF(G(u))=u\varepsilon_K$. Applying this equation twice proves preservation of identities and composition. It also proves naturality in $K$ of the representing bijections. Set $\eta_M$ equal to the transpose of $1_{FM}$. The transpose equations give $\varepsilon_{FM}F(\eta_M)=1_{FM}$ and, by injectivity, $G(\varepsilon_K)\eta_{GK}=1_{GK}$. These are the two adjunction identities and prove clause 2 without requiring a functorial choice of cones.

Cited statements: .

## Unfinished work

The six new lemmas intentionally have no proofs: this is the requested one-level re-split, so separate workers can take them up. There are no unresolved mathematical or tool failures identified before the delivery checks. Server dry-run and push results will be recorded after they exit.
