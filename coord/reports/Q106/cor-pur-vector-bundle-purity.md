# Worker report: cor-pur-vector-bundle-purity

## Files written

- Item: `dag/nodes/sec-smooth-purity/cor-pur-vector-bundle-purity.json`, same statement; six assembly steps.
- `dag/nodes/sec-smooth-purity/lem-pur-vector-trace-geometric-descent.json`: statement, unsplit, no Mathlib match; Geometric descent and ordered multiplication of vector integration traces.
- `dag/nodes/sec-smooth-purity/lem-pur-integration-transpose-base-change.json`: statement, unsplit, no Mathlib match; Base-change calculus and adjunction transport for integration transposes.
- `dag/nodes/sec-smooth-purity/lem-pur-integration-transpose-composition.json`: statement, unsplit, no Mathlib match; Composition and dualizing tensor calculus for integration transposes.
- `dag/nodes/sec-smooth-purity/lem-pur-finite-tate-scalar-source-normalization.json`: statement, unsplit, no Mathlib match; Normalized derived scalar comparison for ordinary finite Tate sources.
- `dag/nodes/sec-smooth-purity/lem-pur-vector-trace-scalar-descent.json`: statement, unsplit, no Mathlib match; Derived scalar descent of Kummer-normalized vector integration traces.
- `dag/nodes/sec-smooth-purity/lem-pur-integration-transpose-scalar-mate.json`: statement, unsplit, no Mathlib match; Exceptional scalar mate equation from normalized integration.

## Attachments

None. The project declaration `WeilConjectures.PurityFiniteSetting.vectorBundlePurity` in `lean/Sheaf/Paper/VectorBundlePurity.lean` ends in `sorry`; upstream keyword and blueprint-tag searches found no complete project theorem.

## WANTED

None. The current blueprint proof and the cited DAG statements are available locally.

## Returned defect and repair

The return orders at least four independent unsplit nodes and a parent proof of at most 3000 characters, retaining all twelve arguments. The sandbox had no node, report or search log when this retry began. The initial required dry run exited with "no node files". I copied the current returned node from the read-only shared repository as baseline. No statement, statement dependency, Lean field, blueprint import field or existing node was edited. Six new nodes replace the long argument; each has empty proof/proof_deps and null proof_origin, and the report below preserves the full old proof for subsequent workers. No repository or launcher file was written; no compiler or git command was run by me.

## Work allocation and preserved argument

Old Step 1 is the existing ambient purity theorem, retained in assembly Step 1. Old Step 12 is the coefficient-unit specialization in assembly Step 6, with its rank-zero/empty trace assertions included in the geometric node and scalar-unit assertions included in the Tate-source node.
- `lem-pur-vector-trace-geometric-descent` receives old Steps 3, 5; its statement makes their intermediate assertion available independently of the parent.
- `lem-pur-integration-transpose-base-change` receives old Steps 2, 4; its statement makes their intermediate assertion available independently of the parent.
- `lem-pur-integration-transpose-composition` receives old Steps 6; its statement makes their intermediate assertion available independently of the parent.
- `lem-pur-finite-tate-scalar-source-normalization` receives old Steps 7; its statement makes their intermediate assertion available independently of the parent.
- `lem-pur-vector-trace-scalar-descent` receives old Steps 9, 10; its statement makes their intermediate assertion available independently of the parent.
- `lem-pur-integration-transpose-scalar-mate` receives old Steps 8, 11; its statement makes their intermediate assertion available independently of the parent.

## New nodes and sources

### lem-pur-vector-trace-geometric-descent

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraph 2, trivializing opens, direct sums, degree-zero descent and frame invariance; old Steps 3,5,12. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 3:

For the base-change square of [def-pur-vector-purity-base-change], let $C:g^*R\pi_!\cong R\pi'_!g'^*$ be compact-support exchange. It exists with its proper/open normalization by [lem-amb-unbounded-compact-support-comparisons]. On every trivializing open and its pullback, the trace of [def-amb-vector-integration] is the affine-space counit and [lem-amb-affine-space-top-trace] gives $t_{\pi'} C_W=g^*t_\pi$. Both source and target have cohomology only in degree zero, since the source is locally isomorphic to the constant sheaf by that affine-space trace. The gluing and equality assertion [lem-pur-degree-zero-derived-map-gluing] therefore makes this equality global. Frame changes give the same trace by the actual equality $t_{p_r}\rho_G=t_{p_r}$ of [lem-amb-linear-trace-invariance]. This applies on Noetherian overlaps, without requiring overlaps to be affine. Pullback bases are Noetherian as required by the stated base-change predicate.

Original cited statements: def-pur-vector-purity-base-change, lem-amb-unbounded-compact-support-comparisons, def-amb-vector-integration, lem-amb-affine-space-top-trace, lem-pur-degree-zero-derived-map-gluing, lem-amb-linear-trace-invariance.

Old Step 5:

Let $F,G$ have ranks $r,s$, and use $q:E(F\oplus G)\to E(G)$, $p:E(G)\to B$, $h=pq$ and $j$ as in [def-pur-vector-purity-direct-sum]. The relative symmetric-algebra description in [def-asd-vector-bundle-zero-section] identifies the sum bundle with $E(F)\times_BE(G)$: an algebra map from $\operatorname{Sym}(F\oplus G)$ is a pair of maps from its summands, so the relative spectra have this product universal property. Hence $q$ is the pulled-back rank-$r$ bundle. Use the composition comparison $\alpha:R p_!R q_!\cong Rh_!$ of [lem-amb-unbounded-compact-support-comparisons], formed through the compactification triangle in that statement. The ordered composite trace is $t_p\circ Rp_!(t_q)$ with projection and twist associators inserted. On simultaneous trivializations this is exactly the coordinate-tower counit of [lem-amb-affine-space-top-trace] and [def-weil-pbc-composite-adjunction]. Both it and $t_h$ have degree-zero source and target, so [lem-pur-degree-zero-derived-map-gluing] makes their local equality global. Reordering blocks preserves the trace by [lem-amb-linear-trace-invariance].

Original cited statements: def-pur-vector-purity-direct-sum, def-asd-vector-bundle-zero-section, lem-amb-unbounded-compact-support-comparisons, lem-amb-affine-space-top-trace, def-weil-pbc-composite-adjunction, lem-pur-degree-zero-derived-map-gluing, lem-amb-linear-trace-invariance.

### lem-pur-integration-transpose-base-change

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraphs 1--2, actual counit normalization and transposing the base-change trace equation; old Steps 2,4. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 2:

The normalization gives $\varepsilon_K R\pi_!(\gamma_{\pi,K})=c_{\pi,K}$, by the transpose formula [def-weil-pbc-adjunction-mate]. A different natural family with this same equation has equal components because the adjunction Hom map is injective. Write $G_0K=\pi^*K(r)[2r]$. The adjunction carried through $\gamma:G_0\cong\pi^\times$ has counit $\varepsilon_0=\varepsilon\circ R\pi_!\gamma$ and unit $\eta_{0,M}=\gamma_{R\pi_!M}^{-1}\circ\eta_M$. Substitution in each triangle identity, followed by naturality of $\gamma$ and cancellation of $\gamma^{-1}\gamma$, gives the identity. Thus the identification preserves the specified units and counits and proves compatibility with adjunctions, rather than asserting only an isomorphism of objects.

Original cited statements: def-weil-pbc-adjunction-mate.

Old Step 4:

Apply [lem-asd-compact-projection-exchange] to $\pi$, its pulled-back compactification, $K$ and $W$. It says precisely that compact-support projection commutes with this arbitrary base change. Its inverse square and the trace equality of Step 3 identify the base-changed $c_{\pi,K}$ with $c_{\pi',g^*K}$. Define $e:g'^*\pi^\times K\to\pi'^\times g^*K$ by its transpose
$$R\pi'_!g'^*\pi^\times K\xrightarrow{C^{-1}}g^*R\pi_!\pi^\times K\xrightarrow{g^*\varepsilon_K}g^*K.$$
This is exactly the exceptional mate convention [def-weil-pbc-adjunction-mate]. Naturality of $C$ and the equation $\varepsilon R\pi_!\gamma=c$ give equal transposes for $e_K g'^*\gamma_{\pi,K}$ and $\gamma_{\pi',g^*K}a_K$. Injectivity of transposition gives their equality. The source comparison $a_K$ is the canonical tensor/pullback comparison with the ordinary Tate identifications of [lem-asd-etale-finite-twist-pullback]. Since $a_K$ and both gamma maps are invertible, $e_K=\gamma_{\pi',g^*K}a_K(g'^*\gamma_{\pi,K})^{-1}$ is invertible. This proves the exact predicate of [def-pur-vector-purity-base-change] and its inverse-alpha square.

Original cited statements: lem-asd-compact-projection-exchange, def-weil-pbc-adjunction-mate, lem-asd-etale-finite-twist-pullback, def-pur-vector-purity-base-change.

### lem-pur-integration-transpose-composition

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraph 2, transposing ordered composite integrations and identifying the dualizing tensor map; old Step 6. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 6:

The exact projection/composition identity [lem-amb-shriek-tensor-composition], with invertible projection maps from Step 1, permits tensoring the trace equality of Step 5 by $K$. Define $c:Rh^!\cong Rq^!Rp^!$ by the composite Hom bijection of [def-weil-pbc-composite-adjunction] under $\alpha$. Its counit is $\varepsilon_p\circ Rp_!(\varepsilon_q)\circ Rp_!Rq_!(c)$, inserting $\alpha^{-1}$ at the source. Transposing the tensored trace equality gives
$$\gamma_{h,K}=c_K^{-1}\circ\gamma_{q,Rp^!K}\circ(1\otimes q^*\gamma_{p,K})\circ a_{r,s,K}.$$
The Tate-power reassociation and shift comparison in $a_{r,s}$ are the ordinary tensor powers of [lem-asd-etale-finite-twist-pullback]; swapping shifts gives $(-1)^{(2r)(2s)}=1$. To identify the stipulated $\gamma_q$, let $\theta_{q,L}$ be the dualizing tensor map, the transpose of inverse projection followed by $1\otimes\varepsilon_{q,A}$. Naturality of projection in its source and $\varepsilon_{q,A}Rq_!\gamma_{q,A}=t_q$ show that $\theta_{q,L}(1\otimes\gamma_{q,A})$ has transpose $c_{q,L}$, hence equals $\gamma_{q,L}$ by [def-weil-pbc-adjunction-mate]. Step 4 at the unit identifies $\gamma_{q,A}$ with the pulled-back unit orientation of $F$. Thus the displayed formula is exactly [def-pur-vector-purity-direct-sum], for every compactification triangle, not a choice of unrelated comparison. Step 1 supplies these maps even on ambient inputs $Rp^!K$, so no additional finite-Tor preservation theorem is being assumed here.

Original cited statements: lem-amb-shriek-tensor-composition, def-weil-pbc-composite-adjunction, lem-asd-etale-finite-twist-pullback, def-weil-pbc-adjunction-mate, def-pur-vector-purity-direct-sum.

### lem-pur-finite-tate-scalar-source-normalization

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraph 2, finite reduction: ordinary Tate balancing, scalar/single unit, tensor and shift source; old Step 7. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 7:

Fix $1\le m\le n$, put $A'=A_{E,m}$, and let $Q_T=(-)\otimes_A^LA'$ [lem-pur-derived-change-of-rings]. Choose one $N=\ell^a$ killing both rings. Their ordinary Tate lines are $\mu_N\otimes_{\mathbf Z/N}A$ and $\mu_N\otimes_{\mathbf Z/N}A'$ and are flat rank-one sheaves [lem-asd-finite-etale-twist-line]. The balancing map $(a\otimes z)\otimes b\mapsto\phi(a)b\otimes z$, and its tensor powers, identify their scalar extensions, including power zero. For a flat degree-zero sheaf $M$, [lem-pur-derived-change-of-rings] computes $Q(M[0])$ by $M\otimes_AA'$ in degree zero. Use the actual normalized scalar adjunction of [lem-pur-sheaf-ring-derived-coefficient-adjunction]. The unit roof in [lem-weil-pbc-scalar-extension-unit-triangles] is then $x\mapsto x\otimes1$. Transposing this roof under the fixed scalar adjunction shows that the comparison $q_M$ of [def-pur-vector-purity-scalar-single] is exactly the same balancing map: its composite with the unit sends $x$ to $x\otimes1$, which determines its transpose. For $M=A$ this is multiplication $A\otimes_AA'\to A'$. Thus the scalar/single comparison at the unit and at rank zero is the stipulated one. With the K-flat tensorator [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and shift and pullback identifications, these give precisely the invertible source arrow $a_{\rm scalar}$ of [def-pur-vector-purity-finite-reduction]. No flatness of $A'$ over $A$ is used.

Original cited statements: lem-pur-derived-change-of-rings, lem-asd-finite-etale-twist-line, lem-weil-pbc-scalar-extension-unit-triangles, def-pur-vector-purity-scalar-single, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-pur-vector-purity-finite-reduction, lem-pur-sheaf-ring-derived-coefficient-adjunction.

### lem-pur-vector-trace-scalar-descent

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraph 2, Kummer/projective-line coefficient reduction, affine-space composition and degree-zero bundle descent; old Steps 9--10. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 9:

First check scalar compatibility of the projective-line trace. By [lem-asd-ordinary-supported-kummer], its supported hyperplane class and its ordinary Chern class are derived scalar extensions of the same $\mathbf Z/N$ class; associativity of the K-flat scalar tensor [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] gives $Q(h_A)=h_{A'}$ under the proper counit-mate comparison [lem-asd-proper-finite-coefficient-extension]. The unit component is preserved as well: by the defining transpose of that proper comparison, its composite with the scalar extension of the old inverse-image/direct-image unit has transpose the identity, hence is the new unit (apply the adjunction triangle identity). Therefore $q\,Q(b_A)=b_{A'}$ for the two-component decomposition of [lem-asd-ordinary-finite-p1-adjunction], under Step 7's scalar source identifications. By [def-amb-p1-trace], $t_A=\operatorname{pr}_2b_A^{-1}$ and $t_{A'}=\operatorname{pr}_2b_{A'}^{-1}$. Functoriality preserves inverses and the finite direct-sum projection, so $t_{A'}q=Q(t_A)$. This proof uses the derived scalar extension of the Kummer class, not an assertion that a nonflat quotient commutes with individual cohomology groups.

Original cited statements: lem-asd-ordinary-supported-kummer, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-asd-proper-finite-coefficient-extension, lem-asd-ordinary-finite-p1-adjunction, def-amb-p1-trace.

Old Step 10:

For the affine line, the trace is $t_q$ after the open-extension counit into the projective-line compactification [lem-amb-affine-space-top-trace]. The open scalar comparison preserves this counit: on the open it is the same scalar tensor map and counit identity, while the source is zero off the open; the open adjunction uniquely determines the map. Step 9 therefore proves scalar compatibility for that trace. The composition identity of [lem-pur-etale-compact-scalar-coherence] and the ordered composite-counit formula [def-weil-pbc-composite-adjunction] propagate the equality through each coordinate of [lem-amb-affine-space-top-trace]; rank zero starts with the identity. For a bundle, [def-amb-vector-integration] gives these coordinate traces on every trivializing open. Under $q$ and Step 7's line comparison, both scalar traces have source isomorphic to $Q(A_B[0])=A'_B[0]$, because the original trace is an isomorphism. Both targets are $A'_B[0]$. Thus [lem-pur-degree-zero-derived-map-gluing] applies to the resulting global derived maps and yields
$$t_{\pi,A'}\circ\widetilde q_{\pi,W}=u_B\circ Q_B(t_{\pi,A}),$$
where $l:Q_EW\cong W'$ is Step 7's scalar line map, $\widetilde q_{\pi,W}=R\pi_{!,A'}(l)\circ q_{\pi,W}$ and $u_B:Q_B(A_B[0])\cong A'_B[0]$ is the normalized scalar unit. The open-restriction clause of [lem-pur-etale-compact-scalar-coherence] identifies $q$ restricted to each $U_i$ with the comparison for $E|_{U_i}\to U_i$ and its restricted compactification, and its refinement clause passes to the coordinate-tower compactification. So the local equations compare the actual maps.

Original cited statements: lem-amb-affine-space-top-trace, lem-pur-etale-compact-scalar-coherence, def-weil-pbc-composite-adjunction, def-amb-vector-integration, lem-pur-degree-zero-derived-map-gluing.

### lem-pur-integration-transpose-scalar-mate

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, paragraph 2, actual exceptional scalar mate and transposition of the scalar trace/projection square; old Steps 8,11. This is an agent-written extraction of the source argument, not a claim that the blueprint already states this helper as a theorem. The original argument allocated to this task follows verbatim; downstream references to old step numbers refer to the preserved twelve-step proof.

Old Step 8:

Apply [lem-pur-etale-compact-scalar-coherence] on the chosen compactification of $\pi$. It gives the actual isomorphism $q_{\pi,M}:Q_BR\pi_{!,A}M\to R\pi_{!,A'}Q_EM$, constructed from the proper scalar counit mate followed by the open scalar comparison; this is exactly $q_{\rm scalar}$ in [def-pur-vector-purity-finite-reduction]. In particular it is invertible at $M=R\pi_A^!K$, including $K=A_B$, without invoking a general smooth-purity theorem. Define $b_K$ to be the transpose of
$$R\pi_{!,A'}Q_ER\pi_A^!K\xrightarrow{q_{\pi,R\pi_A^!K}^{-1}}Q_BR\pi_{!,A}R\pi_A^!K\xrightarrow{Q_B\varepsilon_{A,K}}Q_BK.$$
The convention [def-weil-pbc-adjunction-mate] makes this the published exceptional scalar mate. Its invertibility will follow from the normalized-gamma square, rather than from the false general principle that an invertible square always has invertible mate.

Original cited statements: lem-pur-etale-compact-scalar-coherence, def-pur-vector-purity-finite-reduction, def-weil-pbc-adjunction-mate.

Old Step 11:

The projection square of [lem-pur-etale-compact-scalar-coherence], Step 10's trace equality, and the source identification of Step 7 give the exact equation
$$Q_B(c_{\pi,A,K})\,q_{\pi,G_{0,A}K}^{-1}=c_{\pi,A',Q_BK}\,R\pi_{!,A'}(a_{{\rm scalar},K}).$$
Both sides have source $R\pi_{!,A'}Q_EG_{0,A}K$ and target $Q_BK$. By naturality of $q$ and Step 8's defining counit formula for $b$, the transpose of $b_K Q_E(\gamma_{\pi,A,K})$ is the left side. The transpose of $\gamma_{\pi,A',Q_BK}a_{{\rm scalar},K}$ is the right side, by [def-weil-pbc-adjunction-mate]. Consequently
$$b_K Q_E(\gamma_{\pi,A,K})=\gamma_{\pi,A',Q_BK}a_{{\rm scalar},K}.$$
The scalar functor preserves isomorphisms, Step 1 makes both gamma maps invertible, and Step 7 makes $a_{\rm scalar}$ invertible. Solving this equation gives invertibility of $b_K$. This applies to every stated $K$ and to the coefficient-unit OBJECT, where all scalar/single identifications were checked in Step 7. It proves exactly [def-pur-vector-purity-finite-reduction]; taking inverses gives the compatibility for $\alpha$. No exceptional coefficient comparison restricted to prime-power scalar rings or to separated bases has been applied to ramified $A_{E,n}$.

Original cited statements: lem-pur-etale-compact-scalar-coherence, def-weil-pbc-adjunction-mate, def-pur-vector-purity-finite-reduction.

### Parent integration and edge arguments

Old Step 1:

Work with $A=A_{E,n}$ on the ordinary etale site, as the current statement requires. The base and the bundle have the Noetherian and constant-rank meaning of [def-asd-vector-bundle-zero-section]; $\ell$ is invertible by [def-pur-conventions]. The construction [def-amb-vector-integration] supplies a compactification, the ordinary Tate sheaf, and the actual trace $t_\pi:R\pi_!A_E(r)[2r]\to A_B$. Let $W=A_E(r)[2r]$. The theorem [thm-amb-vector-bundle-purity] states that the canonical projection is invertible and that the transpose of
$$c_{\pi,K}=(1_K\otimes t_\pi)\circ P_{\pi;K,W}^{-1}:R\pi_!(\pi^*K\otimes W)\to K$$
is an isomorphism $\gamma_{\pi,K}:\pi^*K\otimes W\to\pi^\times K$, for every ordinary etale complex $K$. Restrict to the bounded constructible finite-Tor category and set $\alpha_{\pi,K}=\gamma_{\pi,K}^{-1}$. Tensor symmetry identifies the displayed source with the statement's ordered convention. This is exactly the integration-normalized family of [def-pur-vector-purity-normalization], including its coefficient-unit component; no pro-etale witness or higher coefficient passage is needed in this finite ordinary-etale assertion.

Old Step 12:

Set $K=A_B$ in Step 1. Exact coefficient pullback preserves the unit, so the inverse of $\gamma_{\pi,A_B}$ is $\omega_\pi\cong A_E(r)[2r]$, with the reduction square already supplied by Step 11 at that object. At rank zero the relative symmetric algebra of the zero module is $\mathcal O_B$, so [def-asd-vector-bundle-zero-section] identifies $E\cong B$; the coordinate trace is the identity by [lem-amb-affine-space-top-trace]. Its transpose, all composition comparisons and the rank-zero scalar line map above are the identity comparisons. An empty base has only zero sheaves and hence only the unique maps in these formulas; the degree-zero gluing statement includes the empty cover. The current statement explicitly reserves integral, rational and algebraically closed coefficients for the separate transport section, so no limit construction is asserted here.

## Not duplicates

- lem-pur-vector-trace-geometric-descent vs lem-amb-vector-integration-local-trace-compatibility: that node states overlap equality for specified local charts, not global base-change exchange or multiplication under a compactification compositor.
- lem-pur-vector-trace-geometric-descent vs def-amb-vector-integration: the definition constructs one global trace and its local restrictions; the new theorem states its global base-change and product equations.
- lem-pur-vector-trace-geometric-descent vs lem-amb-affine-space-top-trace: the existing assertion is for trivial affine-space bundles, not direct sums of arbitrary locally free modules and descent on their base.
- lem-pur-integration-transpose-base-change vs lem-pur-trace-transpose-base-change: that lemma is a unit-target pro-etale finite-type assertion; the new task treats ordinary-etale arbitrary inputs with projection, arbitrary W, ambient right adjoints and transported units/counits over Noetherian bases.
- lem-pur-integration-transpose-base-change vs def-weil-pbc-adjunction-mate: that definition gives the mate correspondence but does not give the integration projection/base-change equation or transported-adjunction conclusion.
- lem-pur-integration-transpose-composition vs prop-pur-affine-space-composition-law: the latter concerns specified pro-etale affine-space comparisons with positive ranks; the new conditional theorem concerns arbitrary compactifiable composable maps, trace objects and actual ordinary-etale compositors, and identifies the dualizing tensor map on all ambient inputs.
- lem-pur-integration-transpose-composition vs lem-amb-shriek-tensor-composition: that node states a projection/compositor square, not the integration transpose and dualizing tensor equations.
- lem-pur-finite-tate-scalar-source-normalization vs lem-pur-shifted-tate-unit-scalar-coherence: that node treats completed integral coefficients and field inclusions on pro-etale sites; this node treats nonflat finite ring maps and actual ordinary-etale scalar/single adjunction normalization.
- lem-pur-finite-tate-scalar-source-normalization vs lem-pur-twist-coefficient-tensor: that node explicitly makes no assertion about Tate twists or arbitrary module tensors; here those source comparisons are the conclusion.
- lem-pur-finite-tate-scalar-source-normalization vs lem-asd-finite-etale-twist-line: the latter gives local freeness and flatness, without identification with the fixed derived scalar/single adjunct.
- lem-pur-vector-trace-scalar-descent vs lem-sp-p1-counit-scalar: the latter assumes separated finite-type schemes over a field and states a ctf counit equation; the new task includes the two-component Kummer decomposition, all Noetherian bases, coordinate compactification refinement and global bundle trace descent.
- lem-pur-vector-trace-scalar-descent vs lem-sp-affine-counit-scalar: that node is restricted to separated finite-type field bases and trivial affine spaces; this task includes arbitrary bundles over Noetherian bases and derived degree-zero descent.
- lem-pur-vector-trace-scalar-descent vs lem-asd-ordinary-supported-kummer: scalar origin of the supported class alone does not state the unit component, decomposition, projected trace or compact-support descent.
- lem-pur-integration-transpose-scalar-mate vs lem-pur-etale-compact-scalar-coherence: that lemma supplies q and its projection/composition squares, but deliberately assumes no orientation and has no exceptional integration-mate equation.
- lem-pur-integration-transpose-scalar-mate vs lem-sf-constructible-exceptional-coefficient-coherence: that theorem assumes a normalized constructible coefficient-construction record with b already invertible; this conditional ordinary-etale theorem derives invertibility from a trace and gamma equation on arbitrary inputs.
- lem-pur-integration-transpose-scalar-mate vs lem-pur-finite-smooth-adjunction-general-base: that theorem is downstream smooth purity over a field with prime-power scalar rings. It cannot replace pre-smooth-purity mate calculus for ramified finite coefficient rings.

All six new nodes cite the same blueprint proof as a source because they extract its separate arguments. Sharing a source is not sharing a conclusion. No new Stacks tag is asserted, so no same-tag pair is introduced. Whole-DAG statement candidates and whole-blueprint searches are retained in dag-statement-candidates.txt and dag-blueprint-searches.txt.

## Mathlib searches

Each new node has five actual logged searches: two LeanFinder phrasings, Loogle, source grep, and LeanSearch. `repair-queries.json`, `searches.jsonl` and the six `*.search-results.txt` files retain queries and full returned hits. All services answered. Loogle reported unknown names in two compound queries; these are recorded as such, and the two semantic phrasings plus source grep independently checked the notions. The abstract adjunction hits (`mateEquiv`, `mateEquiv_counit`, `Adjunction.comp`, `ofNatIsoRight`) supply constituent identities, not the full derived projection/tensor/trace assertions. I read Adjunction/Mates.lean and Basic.lean to confirm that distinction. Other hits concern module traces, formally etale rings, topological bundles or underived modules. No new node is a one-line specialization of those results.

## Review by Q106

I read the item source in main-20261015, its complete proof, the current sk-prop-an unit, and every statement cited by the old twelve-step argument. The unit uses affine-line/projective-line integration, coordinate composition and descent. The six tasks preserve this route and introduce no general smooth-purity or SGA trace input. The parent statement is byte-for-byte unchanged. The direct-sum predicate has an existing typo Rp^!Rq^! in its prose: the item already explicitly fixes Rh^! ≅ Rq^!Rp^!, and I retained that correct order rather than using the typo. The scalar-single definition points at an overly narrow coefficient comparison; the new normalization task states its actual ordinary scalar-adjunction formula, as the already reviewed old Step 7 did. Neither issue changes the statement here.

Assembly Step 1 uses the ambient theorem exactly: its statement gives gamma for every ordinary-etale complex, the actual integration and canonical projection; the normalization definition fixes the same counit equation. Hence ambient inputs Rg^!K used in the composition task need no added finite-Tor-preservation premise. Assembly Step 2 takes only the new base-change calculus node's uniqueness and explicit unit/counit transport; no base-change hypothesis is needed for its final transported-adjunction assertion.

Assembly Step 3 takes the first trace equation of the geometric node and the ordinary Tate pullback isomorphism, then applies the base-change calculus node with W'=g'^*W identified by that Tate map. Both bases are Noetherian, all vector-bundle maps are compactifiable and the annihilator is invertible. Both gamma families come independently from ambient purity. The calculus node concludes the same exceptional mate of inverse exchange used in the item, so invertibility is deduced from gamma, not from a false principle about arbitrary mates.

Assembly Step 4 uses the geometric node's product geometry and its exact ordered trace equation; the composition node states the resulting right-mate formula with c:R_h→R_qR_p. Its last clause identifies gamma_q with the dualizing tensor map following its unit orientation. Step 3 at the unit supplies precisely that pulled-back orientation. At a vector bundle projection with omega_q follows by naturality from its invertible gamma at the unit; this missing explicit hypothesis is now stated in the composition task. The shift sign is +1 and both ranks may be zero.

Assembly Step 5 takes the Tate-source node's actual balancing, scalar/single and coefficient-unit maps, and the scalar-trace node's derived trace equality. The scalar-mate node states both the transposed counit equation and invertibility when gamma components are invertible. It uses the canonical proper/open q on all complexes, so q is invertible even at Rpi^!A_B. All source maps have the same K-flat normalization and no flatness of A' over A is inserted. In the scalar trace task the composition/refinement input is applied only to a flat Tate line shifted by an even integer; its scalar image is another such line, so both are bounded below as the existing coherence node requires. Open restriction and proper refinement are expressly included in the conclusion, preserving the correction made by the earlier maintainer.

Assembly Step 6 specializes Step 1 at the actual coefficient-unit object and Step 5 at that same object. The geometric node explicitly includes rank zero and the empty base; the scalar-source node explicitly fixes rank-zero multiplication. Small cases checked for every task: identity base change, identity compactification/refinement, empty base, rank-zero first or second summand, identity scalar map m=n, and the nonflat Z/4→Z/2 quotient with N=4 on a base where 2 is invertible. The tensor-source task computes only flat sheaves by underived tensor; it never applies that computation to arbitrary nonflat complexes. The two transpose tasks make trace compatibility an explicit hypothesis; neither asserts smooth purity for general f. The scalar-trace task uses derived classes rather than false commuting of Q with individual H^i.

B--E self-review: statements introduce their objects, sites, coefficient hypotheses and canonical maps; new nodes have no proof steps or hidden proof prose. Each is a strict intermediate task, not the item's conjunction. Their original arguments are preserved verbatim above. Parent citations are checked against the actual node statements in citations.json. The longest parent step and total parent proof are measured before delivery; there is no non-elementary parent step over 2000 characters. All new nodes remain unsplit to allow separate workers to prove them. No statement dispute or uncompleted mathematical clause remains in this stage-1 split.

## Could not finish

No outstanding stage-1 repair item. The six new proof tasks are deliberately statement-only, as the return requires.

## Delivery verification

The server dry run exited 0: `OK (not pushed)` at `f90f4155ef1`, preflight passed. The parent statement and all pre-existing non-split metadata match the read baseline. The parent proof has 2319 characters; its longest step has 536. All six new nodes are unsplit statements with five logged searches each; there are zero Mathlib leaves. A final rerun checks the shortened verbatim citation excerpts and removal of a reason clause from the composition statement (that explanation remains in the review above).
