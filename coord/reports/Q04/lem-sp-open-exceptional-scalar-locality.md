# Stage-1 repair: lem-sp-open-exceptional-scalar-locality

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-sp-open-exceptional-scalar-locality.json: statement, split; statement retained verbatim, three-step assembly (1111 characters).
   - dag/nodes/sec-smooth-purity/lem-sp-open-scalar-inverse-transpose-factorization.json: statement, unsplit; no Mathlib match. Carries returned steps 1 and 4: canonical composition/counit normalization on all pro-etale finite-Tor inputs and inverse-natural coefficient factorization.
   - dag/nodes/sec-smooth-purity/lem-sp-open-scalar-restricted-transpose-expansion.json: statement, unsplit; no Mathlib match. Carries returned steps 2 and 3: actual open-counit scalar equation, counit naturality at an arbitrary candidate r, and its expanded transpose.
   - report.md and citations.json are the review and verbatim statement evidence; searches.jsonl records searches actually run.
2. Attachments: none. A project search for the blueprint tag and exceptional/scalar notions found no finished declaration of this item. CoefficientChange.lean:283-302 defines restriction-of-scalars/open-extension comparisons, not this exceptional scalar-extension equality on pro-etale finite-Tor objects. MateCube.lean:56-76 proves an abstract cube conditional on a left square; it does not supply the geometric square or normalize the open scalar map here.
3. WANTED: none. The named current blueprint and Stacks sources are present. coord/dag-sync.md, mentioned by the inherited brief, is absent; the explicit shared-repository brief and delivery tools govern this repair.
4. The returned item was mathematically reviewed, but its five-step proof totaled 3725 characters and carried two separate calculations. The human's 2026-10-21 re-split instruction requires at least two comparable new statement-only work units. This delivery performs that decomposition; it does not merely abbreviate the old proof. There is no source/statement dispute and no change of unit or route.
5. Unfinished: the two new nodes deliberately have no proof steps and no proof dependencies, as required for parallel follow-on stage-1 work. No Lean was written, compiled, or built. The sandbox initially held only dispatcher brief markers, not a retained split/report/search log; the current shared node is the returned reviewed five-step version and was copied as the baseline.

## Sources and searches

I read the current main-20261015 sec-smooth-purity chapter/unit records and sk-lem-sp-reduction-exceptional.proof.md, especially its Locality paragraph. Both new assertions make explicit subcalculations of that paragraph and are agent-written elaborations, not claims that Stacks states the entire formula. I also read categories.tex at lemma-compose-counits, Tag 0DV0, lines 3576 onward: the actual composite counit is epsilon_f composed with F_f of the open counit. I read more-etale.tex at lemma-shriek-composition (Tag 0F7J), lines 3159 onward, and remark-Rf-lower-shriek-change-of-rings (Tag 0GL6), lines 3739 onward. These give the underlying compact-support composition and coefficient constructions; the precise normalization/coherence is provided by the existing project nodes, not silently attributed to either tag. For the all-pro-etale input clause of the first new node, I read sk-cor-pe-finite-tor-comparison-noetherian.md and the statement of det-pe-finite-tor-comparison-noetherian.

Before creating nodes I searched the whole DAG by the three tags, by the inverse-factorization/counit-transpose/open-scalar notions, and the candidate identifiers. I ran tools/blueprint_refs.py ancestor on the item and search on composition coefficient, counit transpose, open scalar, inverse transpose, transpose expansion, counit factorization, scalar factorization and restricted transpose. No blueprint node states either complete subcalculation. The nearest ancestor is det-sp-reduction-exceptional; both new nodes record it, with the item in via and exact Locality places. The item's existing blueprint metadata is retained.

For each new node I ran msearch.py leanfinder with two separate phrasings, loogle, source grep, and leansearch. The exact queries and returned digests are in the nodes and searches.jsonl. For the second node LeanSearch returned its actual rate-limit error, recorded unavailable. Both LeanFinder requests and Loogle and grep ran successfully for each. I inspected Mathlib CategoryTheory/Adjunction/Basic.lean:565-585 (comp, comp_counit_app, comp_homEquiv), Mates.lean:123-132 (mateEquiv_counit and its inverse) and :209-220 (mateEquiv_hcomp). These are general algebraic tools, not one-line specializations establishing the specified geometric comparisons: one must still prove the coefficient/composition coherence, pass from etale-origin objects to all pro-etale finite-Tor objects, or identify the actual open counit and balanced scalar/restriction map. Search hits on Scheme.Modules.restrictAdjunction concern O_X-module restriction/pushforward, not the constant-coefficient pro-etale extension-by-zero adjunction. ModuleCat scalar adjunction hits concern ordinary modules, not these sheaf derived operations.

## Preservation of the returned argument

The first new node states the composite-counit formula, the correctly ordered composition square, and the final inverse-factorization equation. The second states the cancelled open-counit equation and the two-stage transpose expansion for an arbitrary r satisfying the outer counit equation. Neither states the parent's conclusion: the first never mentions an exceptional scalar mate; the second does not use b_g or compare with the mate for g. Their proof work is independent and comparable (returned steps 1+4 versus 2+3). Their conclusions meet at exactly the intermediate four-factor morphism Q. Only the parent identifies these outputs and uses the Hom bijection.

The full returned arguments are retained below as proof handoff notes in this report, not as proof steps in the new unsplit node files. This preserves all calculations for the workers who will split them, while obeying the statement-only delivery rule.

### Argument assigned to lem-sp-open-scalar-inverse-transpose-factorization

Returned step 1:

Fix $K$ and put $M=G_{f,A}K$ and $L=U_AM$. Use the adjunction-preserving composition identifications in the statement throughout; thus $F_{g,R}=F_{f,R}J_R$, $G_{g,R}=U_RG_{f,R}$. The composite-adjunction definition gives
$$\epsilon_{g,R,K}=\epsilon_{f,R,K}\circ F_{f,R}(v_{R,G_{f,R}K}).$$
The coefficient/composition square of [lem-sp-et-proet-coefficient-compatibility], applied to $U\xrightarrow{j}X\xrightarrow{f}Y$, gives, in these identifications,
$$b_g(L)=F_{f,B}(b_j(L))\circ b_f(J_AL).$$
Here $b_j:T_XJ_A\simeq J_BT_U$ is the normalized open tensor map. The refinement clause of that same node ensures this formula for the chosen compactifications, including comparison through a common refinement. All inputs are in the finite-Tor categories stipulated in the statement. That node states the pro-etale composition square for etale-origin objects; by [det-pe-finite-tor-comparison-noetherian] (the schemes are qcqs and $A,B$ are finite, hence Noetherian) $\nu_U^*$ is an equivalence $D^b_{ctf}(U_{\mathrm{et}},A)\simeq\mathcal C_{U,A}$, so $L\simeq\nu_U^*L'$ with $L'$ etale bounded constructible of finite Tor amplitude, and naturality of both sides of the square in $L$ transfers it to $L$. The site/composition identifications are thus the specified etale-origin ones of that node and the adjunction transfer, not arbitrary isomorphisms of the underlying functors.

Returned step 4:

The comparison $b_f$ is natural by [det-sp-reduction-direct-image]. Apply its naturality square to $v_{A,M}:J_AL\to M$ and compose with inverses of its two isomorphism components. This gives
$$b_f(M)^{-1}\circ F_{f,B}(T_X(v_{A,M}))=T_Y(F_{f,A}(v_{A,M}))\circ b_f(J_AL)^{-1}.$$
Substitute in step 3. Functoriality of $T_Y$, the composite-counit equation in step 1, and inversion of the two-factor expression for $b_g(L)$ in step 1 give
$$\begin{aligned}
\tau&=T_Y\bigl(\epsilon_{f,A,K}\circ F_{f,A}(v_{A,M})\bigr)\circ b_f(J_AL)^{-1}\circ F_{f,B}(b_j(L)^{-1})\\
&=T_Y(\epsilon_{g,A,K})\circ b_g(L)^{-1}.
\end{aligned}$$
The order of the inverse factors is reversed, so their composite has source $F_{g,B}T_UL$ and target $T_YF_{g,A}L$.

Thus the new node includes the previously essential correction: the coefficient/composition square was stated only on etale-origin pro-etale input. Finite rings A and B are Noetherian and our schemes are qcqs. The equivalence in det-pe-finite-tor-comparison-noetherian supplies L ≅ nu_U^*L'; conjugating the natural composition square along this isomorphism gives the square on L. The composite counit formula is unchanged under the adjunction-preserving comparisons. Naturality of b_f at v_A then moves b_f(M)^{-1} past F_f,B(T_X(v_A)); reversing the two factors when inverting b_g gives exactly the displayed final factorization. All these tasks are visible in this node's hypotheses and conclusions, and the old calculation is preserved above.

### Argument assigned to lem-sp-open-scalar-restricted-transpose-expansion

Returned step 2:

Apply [lem-sp-open-proetale-counit-scalar] to $M$. Its identity for the actual open counit is
$$v_{B,T_XM}\circ J_B(a_{j,M})\circ b_j(L)=T_X(v_{A,M}).$$
Since $b_j(L)$ is invertible, right-composition with its inverse gives the precisely typed equality
$$v_{B,T_XM}\circ J_B(a_{j,M})=T_X(v_{A,M})\circ b_j(L)^{-1}.$$
Both sides go from $J_BT_UL$ to $T_XM$. This uses no inverse of an exceptional comparison.

Returned step 3:

Set $d_K=U_B(c_{f,K})\circ a_{j,M}:T_UL\to U_BG_{f,B}T_YK$ and take its counit transpose
$$\tau=\epsilon_{g,B,T_YK}\circ F_{f,B}J_B(d_K).$$
Naturality of $v_B:J_BU_B\to1$, evaluated at $c_{f,K}:T_XM\to G_{f,B}T_YK$, says
$$v_{B,G_{f,B}T_YK}\circ J_BU_B(c_{f,K})=c_{f,K}\circ v_{B,T_XM}.$$
Insert the composite counit from step 1, then this equality, and then step 2. The defining counit equation for $c_f$ in the statement yields
$$\begin{aligned}
\tau&=\epsilon_{f,B,T_YK}\circ F_{f,B}(c_{f,K})\circ F_{f,B}\bigl(v_{B,T_XM}\circ J_B(a_{j,M})\bigr)\\
&=T_Y(\epsilon_{f,A,K})\circ b_f(M)^{-1}\circ F_{f,B}(T_X(v_{A,M}))\circ F_{f,B}(b_j(L)^{-1}).
\end{aligned}$$
This is just naturality, functoriality and substitution of the displayed identities.

For the new statement replace c_f,K by an arbitrary r with the same defining counit equation. The computation only uses that equation and naturality of the actual open counit, so it proves precisely the more reusable stated identity. Specifically apply lem-sp-open-proetale-counit-scalar at M and compose on the right with b_j(L)^{-1}. Then apply v_B naturality to r, expand epsilon_g,B by the composite-counit formula, and substitute the equation for r. This establishes both displayed lines of tau. It does not invoke coefficient/composition coherence, essential surjectivity, or invertibility of r.

### Argument retained in the parent

By definition in the statement, $c_{g,K}$ has counit transpose $T_Y(\epsilon_{g,A,K})\circ b_g(G_{g,A}K)^{-1}$; here $G_{g,A}K=L$. Step 4 proves that $d_K$ has this very transpose. The composite adjunction's Hom bijection in [def-weil-pbc-composite-adjunction] is a bijection, hence injective. Therefore $d_K=c_{g,K}$, which is the required equality for each $K$. No assertion about smoothness, a chart, or invertibility of either right mate enters this argument.

## Not duplicates

- lem-sp-open-scalar-inverse-transpose-factorization vs lem-sp-et-proet-coefficient-compatibility: the existing square is on etale-origin pro-etale objects and has no exceptional adjunction counit or inverse-transpose factorization. The new node requires extension to arbitrary finite-Tor pro-etale L, the specified composite counit, and its factorization at the open counit.
- lem-sp-open-scalar-inverse-transpose-factorization vs det-pe-finite-tor-comparison-noetherian: the existing equivalence supplies etale origin, but states no compact-support/coefficient square, adjunction counit, or factorization.
- lem-sp-open-scalar-inverse-transpose-factorization vs det-sp-reduction-direct-image: the existing statement gives naturality/invertibility of b_h and coefficient-map associativity, but not open source composition or the counit factorization.
- lem-sp-open-scalar-inverse-transpose-factorization vs def-weil-pbc-composite-adjunction: the generic definition gives the composite counit alone; it does not identify the canonical pro-etale compactification coefficient maps or their inverses.
- lem-sp-open-scalar-inverse-transpose-factorization vs lem-sp-finite-compact-site-coherence: that node is site/refinement coherence on etale-origin input, without scalar change or the inverse-transpose factorization on arbitrary pro-etale finite-Tor input.
- lem-sp-open-scalar-inverse-transpose-factorization vs lem-amb-compact-support-open-source-composition: that node computes a fixed-coefficient etale compositor, not scalar/counit factorization on pro-etale finite-Tor input.
- lem-sp-open-scalar-inverse-transpose-factorization vs lem-sf-compact-coefficient-composition: that node is restricted to quotient maps of O_E/powers and etale-origin objects over the fixed algebraic closure, and states no counit factorization; here A to B is any finite ell-primary ring map and k is arbitrary of characteristic p.
- lem-sp-open-scalar-inverse-transpose-factorization vs det-sp-composition-comparisons: that node requires smooth morphisms (and for its tower clause the finite-field datum); here f is arbitrary and the assertion is only the one inverse counit computation.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-open-proetale-counit-scalar: the existing node gives the first cancelled open-counit identity before applying F_f,B. The new node additionally expands the composite-adjunction counit transpose at an arbitrary r and uses its outer counit equation; it is not a second statement of the open scalar identity alone.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-proper-open-coefficient-mate: the existing assertion concerns a proper/open Cartesian square and direct-image coefficient interchange, not the exceptional-adjunction transpose of a restricted candidate.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-proper-open-coefficient-mate-transposed: the existing assertion transposes that proper/open Cartesian interchange, not this source-open exceptional candidate and actual open counit.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sf-adjunct-conjugate-open-factor: the latter has a five-category conjugation diagram and an invertible open unit; its conclusion is an equality of right adjoints' adjuncts in that diagram, not this expansion through the normalized scalar/open counit. Supplying its conjugation square and identifying its maps would itself require the calculations at issue.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-asd-tensor-mate-etale-precomp: that node concerns a tensor/dualizing-object morphism over a single ring on the etale site, not scalar change or the present four-factor expression.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-restriction-transition-transpose: that node uses the scalar extension/restriction adjunction and a compact-support restriction-of-scalars comparison, not the exceptional adjunction or source-open restriction.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sfb-open-scalar-conjugate-normalization: that node identifies restriction of a condensed-coefficient conjugate via the open unit. It neither computes the exceptional transpose nor states an ordinary finite-ring open-counit formula for an arbitrary r.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-categorical-projection-mate-square: that node concerns a monoidal projection/tensor comparison with extra bifunctor compatibility assumptions, not this scalar/open counit expansion.
- lem-sp-open-scalar-inverse-transpose-factorization vs lem-sp-open-exceptional-scalar-locality: the new assertion identifies the A-side inverse-transpose factors, with no c_f or c_g; it cannot conclude the parent's mate equality without the independent restricted-transpose calculation.
- lem-sp-open-scalar-restricted-transpose-expansion vs lem-sp-open-exceptional-scalar-locality: the new assertion computes the B-side candidate transpose without identifying b_g, and makes no assertion about c_g. The other new node and Hom injectivity remain necessary.

## Review by Q04

I checked the repair against delivery-errors B through E, reading the current Locality source and the statements I cite, not their proofs as hidden interfaces. Both new nodes introduce k, ell, A, B, X, Y, U, their functors, maps, K, M and L, and their coefficient/adjunction identifications. They carry proof=[], proof_deps=[], proof_origin=null and status unsplit, with logged successful semantic, Loogle and grep searches; the unavailable request is labelled honestly. They are distinct subarguments rather than individual clauses of the target equality or an entire renamed target. The human re-split instruction is the reason to expose these intermediate calculations as separately assignable work even though their final algebra uses routine naturality. No source route is changed.

For parent step 1 I read the entire new restricted-transpose statement: its hypothesis on r is literally the parent's defining equation for c_f,K, and its conclusion is exactly the displayed four-factor Q. Thus substituting r=c_f,K is legitimate without extra flatness, smoothness, or invertibility. K belongs to the stated finite-Tor category and M,L are defined by its chosen functors. For parent step 2 I read the full new inverse-factorization statement: with the same K,M,L and comparisons it identifies Q with T_Y(epsilon_g,A,K) composed with b_g(L)^{-1}. This is a statement about arbitrary pro-etale finite-Tor L, not a silent use of the etale-origin-only square. For parent step 3 I read def-weil-pbc-composite-adjunction, whose statement explicitly supplies the composite Hom bijection; injectivity equates the two right-adjoint morphisms since their source and target agree. citations.json quotes verbatim the complete statements used, including their formulas. The only off-unit proof tool left in the parent is that generic adjunction definition, declared in split_report.tool_uses.

For the first new node I checked the old step-1 inputs individually. def-weil-pbc-composite-adjunction states precisely epsilon_f composed with F_f of the open counit. lem-sp-et-proet-coefficient-compatibility states the correctly ordered b_g composition square, refinement through any common refinement, and naturality, but only on etale-origin pro-etale objects. det-pe-finite-tor-comparison-noetherian gives exactly the equivalence needed to extend this equality: finite A is discrete Noetherian, U is qcqs, and L has the required bounded constructible finite-Tor properties. det-sp-reduction-direct-image states b_f is natural and invertible, which is what the old step-4 inverse-naturality identity uses. I retained that correction and the reversed inverse order in the first new node's interface and its full handoff calculation above.

For the second new node I checked lem-sp-open-proetale-counit-scalar: its actual open counit formula is v_B J_B(a_j) b_j(U_A M)=T_X(v_A). With L=U_A M, cancellation of b_j(L) is correctly typed. Counit naturality at r gives v_B,G_f,B T_YK composed with J_B U_B(r) equal to r composed with v_B,T_XM. Expanding epsilon_g,B using the actual composite counit, applying F_f,B, then substituting the assumed counit equation of r yields exactly Q in the node. No inverse of r is used, and no equality involving c_g is smuggled into that lemma.

I checked types of both new final formulas: all maps run from F_g,B T_U L to T_Y K. In the cancelled open equation both sides run from J_B T_U L to T_X M. The new node which mentions general H quantifies H in C_Y,R and R in {A,B}. Edge cases: j=id recovers ordinary counit scalar compatibility; U empty gives zero source and the unique morphisms; phi=id gives the original counit/naturality equations; K=0 gives zero composites. For the nonflat map Z/ell^2 to Z/ell, derived tensor and b maps are retained throughout and no exact ordinary tensor argument appears. The zero ring makes the relevant module categories trivial and causes no inversion of a non-isomorphism. Only b_f, b_j and b_g (explicitly isomorphisms) are inverted. I found no statement dispute requiring a change to the retained parent statement.

All arguments in the original five steps remain visible in the two new statements and the detailed handoff above; the parent now does only the 1111-character assembly. There are no long non-elementary parent steps, and no proof was added to either new node. The source, baseline and preserved metadata were read from the shared repository, which I did not edit or run git in. The delivery command will rebase this owned-field overlay on current server main before preflight.
