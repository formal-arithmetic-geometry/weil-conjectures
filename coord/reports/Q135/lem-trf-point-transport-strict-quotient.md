## Worker report

1. Files written: the existing item `lem-trf-point-transport-strict-quotient` (statement unchanged; proof reassembled); `lem-trf-quotient-tensor-insertion` (statement, unsplit, no Mathlib match); `lem-trf-point-quotient-tower-homotopy` (statement, unsplit, no Mathlib match). No Lean or repository files written.
2. Attachments: none. The project source search found no exact declaration under WeilConjectures; Sheaf.Paper.PointTransportStrictQuotient has the matching theorem with `sorry` at line 307, so it does not finish this item.
3. WANTED: none.
4. The returned defect was granularity: all nine arguments were concentrated in this node. The sandbox contained only dispatcher marker files, not the claimed old node/report/search log. I copied the current returned nine-step node from the read-only repository, preserving its statement, citations, searches and maintainer fields; no original report or searches.jsonl existed to retain. The current repository contains the returned 7902-character argument, so no competing retained repair needed rebasing.
5. All requested stage-1 work is supplied. The two new statements intentionally have no proof or proof dependencies: their proofs are separate future items.

## Repair of the return

The return has one repeated point: spread the work into at least two comparable statement-only nodes and keep assembly under 3000 characters. Tensor insertion isolates the sheafification/balancing/transported scalar computation for arbitrary scheme isomorphisms and arbitrary coefficient complexes. Homotopical tower construction isolates tensor reduction on K-flat complexes, exact pullback/restriction/sections, the abelian diagram target, transition-compatible homotopies and identification of the entire coherent reduction tower. Neither statement asserts the parent's Frobenius point natural transformation or its derived finite evaluation. The parent keeps its statement verbatim. The exact original argument is retained below for the next workers, with a coverage map rather than a shortened replacement.

## Coverage of every old argument

- Old 1: restriction/colimit insertion naturality remains the cited restriction theorem in parent step 1; completed scalar linearity and sheafified tensor insertion are obligations of tensor-insertion node.
- Old 2: coefficient transition balancing using the structure square, generator formula, restrictions and differentials are obligations of tensor-insertion node.
- Old 3 and 4: the two explicit sigma naturality composites remain parent step 1. Tensor-insertion node additionally carries the augmented tower identity.
- Old 5: the tensor-insertion naturality square and transitions under maps are in tensor-insertion node; strict tower functoriality is in homotopical tower node; composition with sigma remains parent step 1.
- Old 6: change-of-rings for K-flat quasi-isomorphisms without flat quotient rings, exact finite pullback, unchanged abelian sheaves under restriction, and exact point sections are homotopical tower node's quasi-isomorphism assertion.
- Old 7: existence and pointwise abelian structure of the tower category, reordering complexes/towers, and the explicit transition-compatible homotopies are homotopical tower node's assertions. No homotopy coherence is suppressed.
- Old 8: resolving-class equivalence, functor and transformation descent, uniqueness and roof calculation remain parent step 2.
- Old 9: the K-flat finite evaluation and whole coherent-source identification (including the adic datum A=O_E,I=(varpi)), target quotient-tower identification and augmentations are in homotopical tower node. Bounded constructible finite reductions and equality with the prescribed iota remain parent step 3.

## Not duplicates

lem-trf-quotient-tensor-insertion vs lem-trf-point-system-transport-descent: the latter is point sections and transport for Frobenius powers on a derived system category; the new statement concerns sheaf maps on arbitrary scheme isomorphisms X to Y, no point sections or Frobenius, arbitrary quotient-linear systems and augmented completed-ring complexes. It supplies completed-ring linearity and cross-coefficient chain identities before sections.
lem-trf-quotient-tensor-insertion vs def-weil-inverse-image-pullback-comparison: the definition supplies the maps and theta on chosen representatives but expressly postpones naturality; the new theorem verifies simultaneous insertion naturality for arbitrary quotient-linear maps and completed actions.
lem-trf-quotient-tensor-insertion vs lem-trf-integral-pullback-resolution-matching: the latter identifies derived-limit counit images under iterated integral pullback on bounded constructible objects; the new statement has neither derived limits nor counits and treats arbitrary chain-level systems.
lem-trf-quotient-tensor-insertion vs lem-cbc-adic-pullback-presentation-transport: the latter compares two presentations of completed ring pullback via universal derived pairs; this lemma concerns inverse-image-to-finite-pullback insertion and semilinear coefficient maps.
lem-trf-point-quotient-tower-homotopy vs lem-trf-point-system-transport-descent: the latter starts with a complex of semilinear coefficient systems; it does not assert that quotienting one integral K-flat quasi-isomorphism produces quasi-isomorphisms of the entire two section towers or give its integral homotopies.
lem-trf-point-quotient-tower-homotopy vs def-weil-pbc-adic-coefficient-datum: the latter defines the sheaf reduction tower; this lemma proves both section tower functors (one including finite automorphism pullback) homotopical and identifies their strict-complex and coherent-derived forms.
lem-trf-point-quotient-tower-homotopy vs lem-weil-pbc-pulled-reduction-strict-tower-comparison: that theorem compares constant/completed pullback and derived-limit presentations; this statement concerns point sections and explicit integral-complex homotopies, without a constant/completed ambient comparison.
lem-trf-point-quotient-tower-homotopy vs lem-sp-semilinear-kflat-tower-model: that node constructs a K-flat model of an arbitrary semilinear system, whereas this node starts with one integral K-flat complex and proves homotopical functoriality of its simultaneous quotient sections.
lem-trf-point-quotient-tower-homotopy vs lem-pur-integral-ambient-operation-models: that node compares ambient pullback and completed operations after derived limit; this node asserts the pre-limit whole section-tower functors and their homotopies.

## Searches

Searched the whole DAG by tensor insertion and quotient/homotopy/K-flat concepts; read the candidate statements named above and the completed-tensor-unit-insertion and finite-pull-evaluation statements (they concern completion reflection and finite mate comparisons). Ran blueprint_refs ancestor and whole-blueprint searches for tensor insertion, quotient tower, homotopy tower, coefficient transition, inverse image coefficient, K-flat tower, tensor insertion coefficient and quotient sections. No blueprint node states either new fact. Searched WeilConjectures and the item's Sheaf module, found the existing sorried theorem only. New ids were absent before writing.

For each new node two distinct LeanFinder queries, Loogle and grep actually ran through msearch.py, and LeanSearch was attempted (rate-limited, recorded unavailable). Read every returned hit. For tensor insertion, sheafificationCompPullback in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:118 is an isomorphism of functors, not the assertion about these insertion maps and quotient coefficient changes. AdicCompletion tensor naturality concerns ordinary modules and does not specify the sheaf insertion or cross-coefficient actions. For the tower node, Functor.mapHomotopyCategory at Algebra/Homology/HomotopyCategory.lean:232 supplies a generic additive homotopy functor, not the K-flat quotient quasi-isomorphism assertion or the two specific coherent quotient towers. Flat module tensor-exactness hits assume a flat tensor factor, which S_n over R is not assumed to be. Localization comparison hits supply only localization. Hence neither is a Mathlib leaf. Exact query texts and actual outcomes are in the new nodes and searches.jsonl.

## Review by Q135

I read blueprint main-20261015 prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)-(3) and the reduction-compatibility route, the entire returned nine-step proof, its chapter sec-trace-formula and unit sk-d-weil. For tensor insertion I read Stacks sites-modules.tex section-tensor-product (03EK) and the pullback clause of definition-pushforward (03D6), plus the full statements of def-weil-inverse-image-pullback-comparison and lem-weil-proetale-isomorphism-inverse-image. For homotopical towers I read sites-cohomology.tex lemma-derived-tor-quasi-isomorphism-other-side (06YT), lemma-factor-through-K-flat (0G7D), and the stated K-flat-resolution/derived-base-change route (06YS/06YY), together with the full existing change-of-rings, exact point-sections, small-module-diagram and coherent-adic-datum statements. The blueprint does not prove these chain details itself: the split stays agent-origin, with these sources as supporting inputs.

Parent step 1 takes strict tensor insertion, completed linearity, transition balancing and chain-map naturality from the precise new tensor-insertion statement. I checked the actions: source uses c_R inverse followed by G(pi_n), target uses pi_X,n. The ring square implies c_n G(pi_Y,n)(c_R inverse(a))=pi_X,n(a). The restriction theorem's statement explicitly covers any unbounded complex and any point automorphism, and all chain maps, so it applies to P, P_n, t_n, r_n and f_n restricted to the integral ring. The two displayed composites use exactly that naturality. No quotient inverse or separately chosen derived model appears.

Parent step 2 takes actual functors, preservation of quasi-isomorphisms and homotopies in the abelian whole-tower target from the new homotopical statement. I read lem-weil-pbc-site-derived-tensor-descent: its first assertion is the equivalence for flat-term K-flat homotopy complexes on a small site; it is not merely a tensor existence claim. I read localization-universal-property (1),(2) and its uniqueness clause: they extend both functors and the transformation. Naturality on the quotient homotopy category follows from strict naturality and equality of homotopic maps in the target. The roof calculation includes the inverse of the quasi-isomorphism only after localization. The fixed skeleton supplies the smallness hypothesis.

Parent step 3 takes the whole coherent-source and target identifications from the new tower statement, rather than inferring a whole-tower identification from its finite evaluations. I read def-weil-derived-complete-integral-detailed: it explicitly imposes bounded constructibility of every reduction. I read def-weil-frobenius-point-transport: finite iota is precisely Gamma(kappa) sigma on the finite representative. Hence the final equality uses its actual definition and does not cite the definition for an extra naturality theorem. Every parent citation has a verbatim quote in citations.json.

For new statements I checked self-contained quantifiers, no proof steps/proof sketches, single-escaped TeX, precise source places and complete statement dependencies. Tensor insertion uses an arbitrary system of quotient-linear maps, not a disguised statement of the parent's section transformation; homotopical towers uses any point automorphism and makes no assertion about sigma or iota. Tested the zero complex and zero maps, g=id (insertion becomes the usual scalar-change unit), n=1, arbitrary nonflat finite quotients, acyclic and unbounded K-flat complexes, and homotopies whose degree -1 components must commute with transitions. The homotopies are obtained by applying the same termwise tensor, pullback and sections functors to h; no flatness of S_n is inferred. For the coherent-source specialization O_E is Noetherian, its quotients are finite and have a two-term finite-free resolution by multiplication by varpi^n, so they satisfy the adic datum's perfectness hypothesis. Empty-site concerns do not arise for s=Spec k. No SGA route or new Lean is used.

I corrected only the returned overlarge granularity; no statement dispute or change of hypotheses was needed. Existing generic off-unit tools remain the restriction and resolving-class/localization tools, with the original accepted tool uses preserved; the new nodes inherit the item's unit. Parent proof length is reported below. All original arguments are retained for the future split workers in the following archival section; the new node JSONs are statement-only.

## Original nine-step argument retained for future workers

### Original step 1

Put $S_n=(A_n)_s$ and $\rho_n:S_{n+1}\to S_n$. Use the same inverse-image functor on underlying abelian sheaves at every coefficient level. Apply [lem-weil-point-automorphism-restriction-natural] to $g=\operatorname{Spec}(\gamma)$ with $\Lambda=\mathcal O_E$, on $P$ and on each $P_n$ restricted along $\pi_n:R\to S_n$. It gives $\mathcal O_E$-linear chain maps $\sigma$ and strict naturality for $r_n,t_n$ and $f_n$. These are the specified restriction/colimit-insertion/sheafification maps, since their underlying construction does not change with the coefficient ring. In [def-weil-inverse-image-pullback-comparison](a), write $j_n=\kappa_{P_n}$ for the actual sheafified tensor insertion. It is a chain map. It is $R$-linear with the transported integral action on its source: for a local section $a$ of $R$ and $x$ of $g^{-1}P_n$, the square $\pi_nc_{\mathcal O_E}=c_{A_n}g^{-1}(\pi_n)$ gives
$$j_n(c_{\mathcal O_E}^{-1}(a)x)=x\otimes\pi_n(a)=a\,j_n(x).$$
Consequently $u_n=\Gamma(j_n)\sigma_{P_n}$ is an $\mathcal O_E$-linear chain map. This uses no completeness or boundedness assumption on $P$.

Cites: lem-weil-point-automorphism-restriction-natural, def-weil-inverse-image-pullback-comparison

### Original step 2

The coefficient-defined map $v_n$ of [def-weil-inverse-image-pullback-comparison](b) is induced on the presheaf tensor by $x\otimes b\mapsto g^{-1}(t_n)(x)\otimes\rho_n(b)$. Its balancing relation is respected because $\rho_n c_{A_{n+1}}=c_{A_n}g^{-1}(\rho_n)$ by [lem-weil-proetale-isomorphism-inverse-image](3). Thus, on $x\in g^{-1}P_{n+1}(U)$, both $v_nj_{n+1}$ and $j_ng^{-1}(t_n)$ send $x$ to $g^{-1}(t_n)(x)\otimes1$. Their composites with the sheafification unit are equal, so
$$v_nj_{n+1}=j_ng^{-1}(t_n).$$
Here we used the actual tensor product of [def-pur-sheaf-tensor-product], not an identification between independently chosen derived reductions. The calculation is degreewise and respects every restriction map.

Cites: def-weil-inverse-image-pullback-comparison, def-pur-sheaf-tensor-product, lem-weil-proetale-isomorphism-inverse-image

### Original step 3

Naturality of $\sigma$ in [lem-weil-point-automorphism-restriction-natural], applied to the $R$-linear chain map $t_n:P_{n+1}\to P_n$, gives $\Gamma(g^{-1}t_n)\sigma_{P_{n+1}}=\sigma_{P_n}\Gamma(t_n)$. Combining with Step 2 yields
$$\Gamma(v_n)u_{n+1}=\Gamma(j_ng^{-1}t_n)\sigma_{P_{n+1}}=\Gamma(j_n)\sigma_{P_n}\Gamma(t_n)=u_n\Gamma(t_n).$$
By [def-weil-inverse-system] these equations make $u(P)$ a strict map of towers, already in complexes over $\mathcal O_E$.

Cites: lem-weil-point-automorphism-restriction-natural, def-weil-inverse-system

### Original step 4

By [def-weil-inverse-image-pullback-comparison](b), $\theta_n=j_ng^{-1}(r_n)$. Apply the same strict naturality of [lem-weil-point-automorphism-restriction-natural] to $r_n:P\to P_n$, regarded as an $R$-linear chain map. Then
$$\Gamma(\theta_n)\sigma_P=\Gamma(j_n)\Gamma(g^{-1}r_n)\sigma_P=\Gamma(j_n)\sigma_{P_n}\Gamma(r_n)=u_n\Gamma(r_n).$$
The scalar action on this equation is the one verified in Step 1 by the structure square; no inverse of a quotient map is used.

Cites: def-weil-inverse-image-pullback-comparison, lem-weil-point-automorphism-restriction-natural

### Original step 5

For a chain map $f:P\to P'$, the maps $f_n=f\otimes1$ commute with $t_n$ by the tensor formula, and their pullbacks commute with $v_n$ by the formula in Step 2. Tensor insertion satisfies the strict sheaf-map equality $(g_n^*f_n)j_n(P)=j_n(P')g^{-1}(f_n)$: on a section $x$ both sides are $g^{-1}(f_n)(x)\otimes1$, followed by sheafification [def-pur-sheaf-tensor-product, def-weil-inverse-image-pullback-comparison]. Naturality of $\sigma$ [lem-weil-point-automorphism-restriction-natural] now gives
$$\Gamma(g_n^*f_n)u_n(P)=\Gamma(j_n(P'))\Gamma(g^{-1}f_n)\sigma_{P_n}=u_n(P')\Gamma(f_n).$$
Functoriality of the termwise constructions and these two tower compatibilities make $D(P)$ and $B(P)$ functors on the flat-term K-flat complexes and $u$ a natural transformation between them.

Cites: def-pur-sheaf-tensor-product, def-weil-inverse-image-pullback-comparison, lem-weil-point-automorphism-restriction-natural

### Original step 6

If $f:P\to P'$ is a quasi-isomorphism between the indicated K-flat complexes, [lem-pur-derived-change-of-rings](1), applied to $R\to S_n$, says $f_n$ is a quasi-isomorphism, even though $S_n$ need not be flat over $R$. At finite level the inverse image and module pullback in [def-weil-inverse-image-pullback-comparison](a) are exact for this scheme automorphism; hence $g_n^*f_n$ is a quasi-isomorphism. Restriction of scalars changes only the action [def-pc-sheaf-restrict-scalars], so kernels and cokernels have the same underlying abelian sheaves and quasi-isomorphisms remain quasi-isomorphisms. Exact sections [lem-weil-point-proetale-sections-exact] therefore send both maps to quasi-isomorphisms. Thus both strict tower functors take $f$ to a levelwise quasi-isomorphism.

Cites: lem-pur-derived-change-of-rings, def-weil-inverse-image-pullback-comparison, def-pc-sheaf-restrict-scalars, lem-weil-point-proetale-sections-exact

### Original step 7

Take as target $\mathcal T=D(\operatorname{Fun}(\mathbf Z_{\ge1}^{\mathrm{op}},\operatorname{Mod}(\mathcal O_E)))$: a strict tower of complexes is a complex of towers, and its quasi-isomorphisms are exactly the levelwise ones. The required abelian diagram category exists by [lem-weil-pbc-small-module-diagrams-grothendieck], applied to the one-object trivial site with ring $\mathcal O_E$ and the small tower index. Kernels and cokernels are pointwise: take the kernels or cokernels at every level and use the commuting transition squares to induce their transitions; their universal properties are checked levelwise. Use the derived category of [def-weil-abstract-derived-category]. If $f-f'=dh+hd$, apply tensor, inverse image and sections termwise to $h$ as well. This produces homotopies $\Gamma(h\otimes1)$ for $D$ and $\Gamma(g_n^*(h\otimes1))$ for $B$. Their components commute with transitions by the same tensor formulas as in Step 5. Thus they are homotopies in complexes of towers, and the two functors in Step 5, after target localization, factor through the homotopy category of flat-term K-flat complexes. Their natural transformation does also.

Cites: lem-weil-pbc-small-module-diagrams-grothendieck, def-weil-abstract-derived-category

### Original step 8

By [lem-weil-pbc-site-derived-tensor-descent], the homotopy category of K-flat $R$-complexes with flat terms, localized at its quasi-isomorphisms, is equivalent to $D(R)$. The pro-etale site is taken in the small skeleton and containing universe fixed in the statement. Step 6 says the two functors of Step 7 invert these quasi-isomorphisms. Apply [lem-weil-pbc-localization-universal-property](1),(2) to obtain the two functors $D(R)\to\mathcal T$ and their natural transformation; its uniqueness clause gives compatibility with the comparison for every other flat-term K-flat representative. Explicitly, naturality $B(a)u(Q)=u(P)D(a)$ for a quasi-isomorphism $a:Q\to P$ implies
$$B(a)^{-1}u(P)=u(Q)D(a)^{-1}.$$
Composing this with $B(b)u(Q)=u(P')D(b)$ proves naturality for a roof $P\xleftarrow{a}Q\xrightarrow{b}P'$; the localization property ensures independence of roof presentation and of representative. The construction retains the strict quotient towers before localization, rather than choosing each level separately.

Cites: lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-localization-universal-property

### Original step 9

The $n$-th source evaluation is $\Gamma(P\otimes_RS_n)$, representing sections of $N\otimes_R^LS_n$ by [lem-pur-derived-change-of-rings](2). Its transitions and augmentations are exactly those of [def-weil-integral-reduction-tower]. By [def-weil-pbc-adic-coefficient-datum], applied with $A=\mathcal O_E$, $I=(\varpi)$, so that $A_s=R$ and $(A/I^n)_s=S_n$, the coherent reduction tower of $N$ is the class in $D(\operatorname{Tow}_{\mathcal O_E}(s))$ of the strict tower $F(P)_n=P\otimes_RS_n$ with transitions $1\otimes\rho_n=t_n$, computed on the flat-term K-flat representative $P$ itself; applying the exact functor $\Gamma$ levelwise gives the tower $D_\bullet(P)$, so the descended source functor of Step 8 is sections of the coherent reduction tower. The target evaluation is sections of the corresponding finite module pullback of that same quotient complex, as specified in [def-weil-inverse-image-pullback-comparison](a),(b). If $N=[P]\in D^b_c(s,\mathcal O_E)$, [def-weil-derived-complete-integral-detailed] says $N_n=N\otimes_R^LS_n$ is bounded constructible at finite coefficients. At that level [def-weil-frobenius-point-transport] defines $\iota_{N_n}$ as the class of $\Gamma(j_n)\sigma_{P_n}$, which is exactly $u_n(P)$. Step 8 gives this equality independently of the representative. This proves the last clause and identifies the two descended tower functors as claimed.

Cites: lem-pur-derived-change-of-rings, def-weil-integral-reduction-tower, def-weil-pbc-adic-coefficient-datum, def-weil-inverse-image-pullback-comparison, def-weil-derived-complete-integral-detailed, def-weil-frobenius-point-transport


Parent proof character count: 2395.
