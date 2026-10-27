# Q69 repair: lem-pur-smooth-exchange-scalar-compatibility

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-smooth-exchange-scalar-compatibility.json: statement unchanged verbatim; four-step assembly, 2171 characters of proof text.
- dag/nodes/sec-smooth-purity/lem-pur-rational-purity-exchange-endpoints.json: statement, status unsplit; no Mathlib match. Rational domains and the two scalar endpoint squares (A),(B), with the localized purity square (P) and their exact coefficient coherence.
- dag/nodes/sec-smooth-purity/lem-pur-twisted-pullback-square-scalars.json: statement, status unsplit; no Mathlib match. The twist, composition and middle squares (Z),(C),(M), with their actual comparison maps and coefficient coherence.
- report.md and citations.json: self-review and literal statements backing every citation of every assembly step. Search results and searches.jsonl are retained in the sandbox.

## Attachments

None. I searched the live WeilConjectures source for the item tag, purity/scalar and smooth exchange. The finite-coefficient smoothPurityIso, smoothPullbackExchange and leftDerivedUpperStarTwistShiftBaseChangeIso constructions in EtaleCohomology/Purity/Smooth/Basic.lean do not state the rational-field scalar equation. The finite purity theorem depends on the sorry at line 211. No exact completed declaration was found for the item or either new statement.

## WANTED

None. The sources of this repair are already present. No Stacks tag supplies the specific rationalized purity endpoint comparison or the specified twisted pullback/scalar square. I do not assign an unrelated tag to either. The blueprint itself is agent-written, and the assembly retains proof_origin.by = agent. No SGA source is used in this repair.

## What required repair

The return requires spreading the 7747-character proof across at least two comparable statement-only nodes and keeping the parent's assembly below 3000 characters. The sandbox contained only dispatcher marker files, with no retained node, report, citations or search log. I therefore copied the current shared-repository item, whose nine proof steps and lengths agree with the returned version, and preserved it in baseline.json before editing. I ran no git commands in the shared repository. The delivery tool rebases its own overlay onto current origin/sheaf-dag.

No mathematical statement dispute was found and the parent statement is unchanged. This is a substantive re-split, not a shortened paraphrase of the old proof: the new nodes have independent complete conclusions and proof=[] and proof_deps=[]; all arguments to be performed by their future workers are transcribed below. Neither new conclusion contains the asserted smooth exchange equation. The first has exceptional/purity endpoint data but no middle arrow; the second has the middle arrow and no exceptional inverse image. Only the parent pastes the three squares and identifies the actual reconstructed exchange.

The first work package carries old steps 1,2,6,7 (3041 characters before its share of step 9); the second carries old steps 3,4,5 (2763 characters before its share of step 9). Thus there is no dominant new node carrying the full old proof. Their statements explicitly expose (P),(A),(B) and (Z),(C),(M) respectively, not just the final equations with omitted normalization or coherence. Parent step 3 carries the original step 8 assembly, which is the work the parent should retain.

## What remains unfinished

The two newly created nodes are deliberately unsplit: their proofs are future parallel stage-1 items. This repair does not write Lean or invoke a compiler, Lake or any build. Delivery checks and push are performed with the prescribed launcher tools.

## Not duplicates

lem-pur-rational-purity-exchange-endpoints vs lem-pur-adic-purity-scalar-naturality: the latter is the integral simultaneous family and square, with completed scalar rings; the new node must establish the rational finite-Tor domain and localized morphism extension, then the pulled-back inverse endpoint and the final endpoint at the actual p_v, including their tower/shift equations. It does not copy the full exchange conclusion.
lem-pur-rational-purity-exchange-endpoints vs thm-pur-rational-and-qbar-purity: that theorem gives rationalized purity isomorphisms, not equations (A),(B) with the specified b,p,r and their coefficient coherence.
lem-pur-rational-purity-exchange-endpoints vs prop-weil-pbc-rational-transport: the latter is the generic extension property for supplied functors and transformations, not the applicability/domain and endpoint identifications in this new statement.
lem-pur-twisted-pullback-square-scalars vs lem-pur-derived-pullback-tensor-iso: that node states monoidality and its scalar compatibility. The new statement also compares pullback of the specified Tate line, the two paths of a geometric square, and their shifted scalar composites (Z),(C),(M).
lem-pur-twisted-pullback-square-scalars vs det-prop-sfb-cartesian-coefficients-twists: that node gives geometric pullback of twists but no square mixing those maps with coefficient extension, no two-path composition square, and no equation (M).
lem-pur-twisted-pullback-square-scalars vs lem-weil-integral-twist-scalar-coherence: that is coherence in a coefficient tower for a twist on one fixed scheme; the new node includes geometric pullback and the two composites in a Cartesian square, at rational coefficients.
lem-pur-twisted-pullback-square-scalars vs lem-pur-shifted-tate-unit-scalar-coherence: that node treats only the shifted coefficient unit and extensions from Q_l on one scheme, rather than arbitrary K and geometric pullbacks around the square.
lem-pur-twisted-pullback-square-scalars vs det-sp-purity-bc-factors: that node compares orientation and tensor formulas with a finite/tower exceptional base-change mate, without these rational scalar squares. No mate identification is used here.
lem-pur-twisted-pullback-square-scalars vs lem-pur-composition-comparison-scalar-compatibility: that node compares exceptional composition along two smooth morphisms. The new node concerns ordinary pullbacks along the two paths of a geometric square, with arbitrary v.

Whole-DAG searches by id and by formulas r_A/r_B/P_U/P_V and purity/scalar/twist notions were followed by opening the closest statements listed above. The blueprint_refs ancestor is prop-pur-rational-purity-trace-coherence. Searches for purity scalar, twisted pullback, purity square, conjugat, pullback comparison, scalar extension, counit-normalized, twist comparison, smooth exchange, and scalar pullback yielded no existing node with either new statement. I read the relevant orientation definition, Cartier Kummer statement, Kummer additivity statement and functor-package statement: they respectively define an orientation datum, construct a divisor class, give its additivity, or summarize six functors, and do not supply these two assertions. Both new nodes therefore have same_as=[] and from.via=[lem-pur-smooth-exchange-scalar-compatibility]. No new source carries a Stacks tag, so there are no same-tag pairs to distinguish beyond these conceptual near matches.

## Mathlib search assessment

Each new node has its own natural-language LeanFinder query, Loogle query, source grep, LeanSearch query and second independently phrased LeanFinder query. Their exact tool/query records come from searches.jsonl and their full hits are in search-result-01.txt through search-result-10.txt. The second node's LeanSearch request returned a rate-limit error and is recorded as unavailable. Its successful LeanFinder/Loogle/grep searches satisfy the three kinds without treating that error as absence.

I read the returned signatures. The closest hits were AlgebraicGeometry.Scheme.Modules.pullbackComp and conjugateEquiv_pullbackComp_inv; a further logged msearch grep located them at Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:241 and :265. Reading lines 230–275 confirms these are pullbacks of structure-sheaf modules, not constructible pro-etale coefficient categories, Tate lines, or the supplied exceptional purity natural transformation. The free-module pullback hits concern ordinary free objects. The Loogle pullback/tensor hits concern residue-field tensor rings of scheme points. Generic cochain-shift and representation-theory hits likewise do not identify our specified comparisons. Neither node is an exact match or one-line specialization of those declarations; no Mathlib leaf is claimed.

## Review by Q69

I read the current smooth-purity chapter and purity-transport unit records, SETUP's three levels, the stage-1 brief and delivery-errors B–E. The chapter and unit are unchanged. The source for the item and BOTH new nodes is main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md, the paragraph transporting base-change coherence along the same exact functors. I also read the current thm-pur-rational-and-qbar-purity.proof.md (the lattice and exact localization argument) and prop-pur-adic-reconstruction-trace-coherence.proof.md (the reconstruction of the specified coherent finite maps). The new nodes make explicit the two independent arguments hidden in that paragraph. I did not substitute the SGA trace route or an exceptional mate for the purity-defined exchange.

Assembly step 1 cites lem-pur-rational-purity-exchange-endpoints. Its statement gives the geometric and lattice domains, the localized square (P), and precisely equations (A),(B), with r_A,r_B,beta_A,beta_B fully defined. I checked that b is the counit-normalized integral comparison rationalized, not an arbitrary isomorphism. In (A), naturality of p_u at gamma_f inverse is necessary; in (B), naturality at the actual p_v is necessary. Both obligations are preserved in the first work package below and neither is silently replaced by equality of reductions.

Assembly step 2 cites lem-pur-twisted-pullback-square-scalars. Its statement fixes a_h=D(p_h)q, the actual twist pullback z and t=c_(f',v)c_(u,f)^(-1), and gives (Z),(C),(M). Thus the r_A,r_B in step 2 are the same maps as in step 1. I checked (Z) before specializing M to Lf_E^*K: its source is T_(X') Lu_E^* D_X^E M, and both sides land in D_(X')^L Lu_L^* T_X M. In (C), P_U and P_V compare the two ordinary pullback composites and the shared total map is f u = v f'. No proper, flat or smooth condition on v is used. I corrected an overly general notation for the tower equation while drafting: a single family F_R with its input/output schemes is now specified, so the intermediate functors match and the target associator is F_L of the input-scheme associator.

Assembly step 3 cites def-pur-smooth-pullback-exchange, prop-pur-adic-reconstruction-trace-coherence, and prop-weil-pbc-rational-transport. I opened all three statements. The definition explicitly gives the three-factor purity composite, not an adjoint mate; the reconstruction statement transports the coherence data; the localization statement extends exact linear functors and natural transformations with their components. Those are exactly the three uses in the step. The exact functors and their constructible inputs are supplied by the first new lemma and the fixed reconstruction/purity family. After that identification, the displayed calculation uses (B), (M), (A) in that order, with composition and inverses preserved by functors. It does not require a new lemma hidden in the assembly.

Assembly step 4 cites both new statements. Each explicitly asserts naturality and unit/tower/shift compatibility for its squares, and the middle statement says the twist line has degree zero. I checked that substituting the three tower squares into the three-factor paste cancels each internal associator with its inverse, leaving exactly the source/target associators in beta_A and beta_B. This last pasting is elementary from the cited equations; I have retained the concrete cancellation argument rather than writing just 'compatibility transports'. No non-elementary parent step exceeds 2000 characters.

For the first new statement I checked all original inputs' statements: finite type over a Noetherian field base, finite-dimensionality over a field, smooth relative-dimension permanence (including the empty case), separated finite-type base change, raw rational-category objects, integral stratified-perfect characterization, integral residue Tor, and preservation of integral constructibility by pullback. These give the stated domains without assuming that a discrete non-torsion etale theory or a Karoubi object is an integral lattice. For both new statements I read the canonical scalar-extension statement, simultaneous integral purity/scalar statement, rational-transport and rational-purity statements. For the second I additionally read the full derived-pullback/tensor statement, detailed twist definition, derived pullback tensor isomorphism and geometric twist comparison. The relevant clauses genuinely include the normalization/line/composition assertions used in the preserved arguments, not merely definitions carrying similar names. These inputs are future proof obligations for unsplit children; no child's argument is presented as a completed proof.

Small cases checked for each new assertion: E=L makes comparison maps identities; v=id and the identity square reduce to the ordinary purity scalar square or identity pullback comparison; d=0 uses the coefficient-unit map (not a tensor with a nonexistent negative power); K=0 makes the equations zero maps; empty X' is allowed by the relative-dimension permanence statement. For general d the roots-of-unity line is in degree zero, so the existing even shift introduces no sign. Ramified field extensions use the completed-coefficient scalar comparison and its rationalization, with no nonexistent finite reduction of a field coefficient. The maps retain the original domain and arbitrary-v hypotheses throughout.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against this repair. The new nodes are self-contained statement-only work packages with actual smaller intermediate conclusions, no proof-dependencies and no references to the parent or to each other. Definitions they use are in stmt_deps; proof sources are places, not substitutes for nodes. There are no new definitions, no duplicate ids, and no alteration of the parent's statement. The only off-unit proof tool remaining in the parent is generic rational transport, declared in split_report.tool_uses. citations.json quotes the literal complete relevant statements, so no citation is justified by a proof-only construction.

## Preserved proof work, assigned to the new nodes

The following text is copied verbatim from the nine-step returned proof, rather than shortened. It is a work brief for the future workers, not proof steps inside the unsplit JSON files. This preserves every calculation and source obligation. The allocation is: steps 1,2,6,7 to lem-pur-rational-purity-exchange-endpoints; steps 3,4,5 to lem-pur-twisted-pullback-square-scalars; step 9 split between their endpoint and middle coherence clauses; step 8 remains the parent's actual-composite identification and short assembly. For each quoted step, the original uses list records the input statements that its future worker should split or cite.

### Original step 1 → lem-pur-rational-purity-exchange-endpoints

All four schemes are Noetherian and finite-dimensional: apply [lem-weil-pbc-finite-type-over-noetherian] to their structure morphisms over the field $k$, and [lem-kun-dimension-finite-type]. Since $\ell\ne p$, $\ell$ is invertible on them. By [lem-sbc-smooth-relative-dimension-permanence] and [lem-pod-separated-finite-type-base-change], $f'$ is smooth separated finite type of pure relative dimension $d$, including when $X'$ is empty. Thus both $f$ and $f'$ satisfy the geometric hypotheses of the simultaneous purity family. The raw rationalization [def-weil-pbc-rational-category] gives an integral representative for every rational object. The characterization [lem-weil-pbc-integral-stratified-perfect-characterization] identifies that integral category with the one in purity, and [lem-coef-integral-residue-tor] gives its uniform finite-Tor condition. Pullbacks used below preserve integral constructibility by [lem-pur-integral-operations-preserve-constructible], so this applies also to $Lv_E^*K$. No restriction on $v$ beyond the displayed scheme setting is used.

Original cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, lem-sbc-smooth-relative-dimension-permanence, lem-pod-separated-finite-type-base-change, def-weil-pbc-rational-category, lem-weil-pbc-integral-stratified-perfect-characterization, lem-coef-integral-residue-tor, lem-pur-integral-operations-preserve-constructible.

### Original step 2 → lem-pur-rational-purity-exchange-endpoints

For $h=f,f'$, denote by $a_{h,M}:T H_{h,E}M\to H_{h,L}TM$ the rationalization of the comparison $a$ in [lem-pur-adic-purity-scalar-naturality]. Its purity square, after applying [prop-weil-pbc-rational-transport], is
$$b_{h,M}\circ T(\gamma_{h,E,M})=\gamma_{h,L,TM}\circ a_{h,M}.\tag{P}$$
Here $b$ is exactly the counit-normalized comparison named in the item, not an independently chosen isomorphism. By [thm-pur-rational-and-qbar-purity], these rationalized $\gamma$ are the purity maps used in the item. Localization preserves the equality on each integral representative and extends naturality to localized morphisms. It also preserves the unit, successive-extension and shift equations in the simultaneous integral family. In particular (P) holds at every rational $M$ required below.

Original cited nodes: lem-pur-adic-purity-scalar-naturality, prop-weil-pbc-rational-transport, thm-pur-rational-and-qbar-purity.

### Original step 3 → lem-pur-twisted-pullback-square-scalars

Write $D_W^R(M)=M(d)[2d]$ and let $q_{W,M}:T_WD_W^E M\to D_W^L T_WM$ be the tensor/twist/shift comparison. The comparison $a$ of step 2 factors, by its specified pullback/tensor/twist/shift construction, as
$$a_{h,M}=D_{\mathrm{source}(h)}^L(p_{h,M})\circ q_{\mathrm{source}(h),Lh_E^*M}.$$
Let $z^R_{u,M}:Lu_R^*D_X^R M\to D_{X'}^R Lu_R^*M$ be the pullback/twist/shift comparison occurring in the definition of the middle arrow. The tensor comparisons commute with scalar extension by [lem-pur-derived-pullback-tensor-iso]. The twist-line pullback of [det-prop-sfb-cartesian-coefficients-twists] commutes with scalar extension directly from [def-coefficient-twists-detailed]: for $d\geq0$ both routes send a tensor of $d$ roots-of-unity sections with coefficient $e\in E$ to the same pulled-back tensor with coefficient the image of $e$ in $L$; for $d=0$ this is the unit map. Tensor balancing gives equality of these line maps. Together with the shift comparisons this gives
$$z^L_{u,T_XM}\circ Lu_L^*(q_{X,M})\circ p_{u,D_X^E M}=D_{X'}^L(p_{u,M})\circ q_{X',Lu_E^*M}\circ T_{X'}(z^E_{u,M}).\tag{Z}$$
This uses the scalar compatibility of the actual tensor comparison, not detection of equality from unrelated finite reductions.

Original cited nodes: lem-pur-adic-purity-scalar-naturality, prop-weil-pbc-scalar-extension, lem-pur-derived-pullback-tensor-iso, det-prop-sfb-cartesian-coefficients-twists, def-coefficient-twists-detailed.

### Original step 4 → lem-pur-twisted-pullback-square-scalars

Put $U_R=Lu_R^*Lf_R^*$ and $V_R=Lf'_R{}^*Lv_R^*$. Let $t_R:U_R\to V_R$ be the untwisted comparison of the commutative square, namely $c_{f',v}\circ c_{u,f}^{-1}$. Here these are the transported pullback composition comparisons in [def-pur-smooth-pullback-exchange]. Define
$$P_U=Lu_L^*(p_f)\circ p_{u,Lf_E^*(-)},\qquad P_V=Lf'_L{}^*(p_v)\circ p_{f',Lv_E^*(-)}.$$
The composition compatibility of the canonical scalar pullback comparisons in [prop-weil-pbc-scalar-extension], applied first to $(u,f)$ and then to $(f',v)$, gives
$$P_V\circ T_{X'}(t_E)=t_L\circ P_U.\tag{C}$$
Indeed the two composition squares have the common third side $p_{f\circ u}=p_{v\circ f'}$. Reverse the first composition square (all its arrows are isomorphisms) and paste the second. This proves (C) for the specified comparisons.

Original cited nodes: prop-weil-pbc-scalar-extension, def-pur-smooth-pullback-exchange.

### Original step 5 → lem-pur-twisted-pullback-square-scalars

Let $m_R:Lu_R^*H_{f,R}\to H_{f',R}Lv_R^*$ denote the middle arrow of the transported purity composite. Thus
$$m_R=D_{X'}^R(t_R)\circ z^R_{u,Lf_R^*(-)}.$$
Set
$$r_A=Lu_L^*(a_f)\circ p_{u,H_{f,E}(-)},\qquad r_B=H_{f',L}(p_v)\circ a_{f',Lv_E^*(-)}.$$
Using the factorization of $a$ in step 3 and naturality of $q$, equation (Z) says
$$z^L_{u,Lf_L^*T_Y(-)}\circ r_A=D_{X'}^L(P_U)\circ q_{X',U_E(-)}\circ T_{X'}(z^E_{u,Lf_E^*(-)}),$$
whereas $r_B=D_{X'}^L(P_V)\circ q_{X',V_E(-)}$. Therefore naturality of $q$ at $t_E$, followed by (C), gives
$$r_B\circ T_{X'}(m_E)=m_L\circ r_A.\tag{M}$$
These identities are pastings of (Z), (C), and naturality; in particular no exceptional base-change theorem is used to identify this middle arrow.

Original cited nodes: (elementary from earlier displayed equations).

### Original step 6 → lem-pur-rational-purity-exchange-endpoints

Let $s_R=(Lu_R^*\gamma_{f,R})^{-1}$. Invert the isomorphisms in (P) for $h=f$ to obtain
$$a_{f,K}\circ T_X(\gamma_{f,E,K}^{-1})=\gamma_{f,L,T_YK}^{-1}\circ b_{f,K}.$$
Naturality of $p_u$ at $\gamma_{f,E,K}^{-1}$, followed by this equality, gives
$$r_{A,K}\circ T_{X'}(s_{E,K})=s_{L,T_YK}\circ\beta_{A,K}.\tag{A}$$
In detail the left side is
$$Lu_L^*(a_{f,K})\circ Lu_L^*T_X(\gamma_{f,E,K}^{-1})\circ p_{u,G_{f,E}K},$$
which becomes $Lu_L^*(\gamma_{f,L,T_YK}^{-1})\circ Lu_L^*(b_{f,K})\circ p_{u,G_{f,E}K}$, exactly the right side.

Original cited nodes: prop-weil-pbc-scalar-extension.

### Original step 7 → lem-pur-rational-purity-exchange-endpoints

For the final purity factor, use (P) at $h=f'$ and $M=Lv_E^*K$, and then naturality of $\gamma_{f',L}$ at the actual morphism $p_{v,K}:T_{Y'}Lv_E^*K\to Lv_L^*T_YK$. This yields
$$\begin{aligned}
\beta_{B,K}\circ T_{X'}(\gamma_{f',E,Lv_E^*K})
&=G_{f',L}(p_{v,K})\circ\gamma_{f',L,T_{Y'}Lv_E^*K}\circ a_{f',Lv_E^*K}\\
&=\gamma_{f',L,Lv_L^*T_YK}\circ H_{f',L}(p_{v,K})\circ a_{f',Lv_E^*K}\\
&=\gamma_{f',L,Lv_L^*T_YK}\circ r_{B,K}.\tag{B}
\end{aligned}$$
The naturality used here is the rationalization of the natural transformation in [lem-pur-adic-purity-scalar-naturality], extended to all rational morphisms by [prop-weil-pbc-rational-transport].

Original cited nodes: lem-pur-adic-purity-scalar-naturality, prop-weil-pbc-rational-transport.

### Original step 8 → parent assembly

The finite exchange is defined in [def-pur-smooth-pullback-exchange] by $\gamma_{f'}\circ m\circ s$. The reconstruction of [prop-pur-adic-reconstruction-trace-coherence] and the rational transport [prop-weil-pbc-rational-transport] carry that specified composite to the actual $\operatorname{Ex}^{!,\mathrm{sm}}_R$ of the item, since functors preserve composition and inverses. Thus (B), (M), and (A), in order, give
$$\begin{aligned}
\beta_B\circ T_{X'}(\operatorname{Ex}^{!,\mathrm{sm}}_E)
&=\gamma_{f',L}\circ r_B\circ T_{X'}(m_E)\circ T_{X'}(s_E)\\
&=\gamma_{f',L}\circ m_L\circ r_A\circ T_{X'}(s_E)\\
&=\gamma_{f',L}\circ m_L\circ s_L\circ\beta_A
=\operatorname{Ex}^{!,\mathrm{sm}}_L\circ\beta_A.
\end{aligned}$$
Every component here is evaluated at $K$, and the $L$-exchange at $T_YK$. This is the asserted component equation.

Original cited nodes: def-pur-smooth-pullback-exchange, prop-pur-adic-reconstruction-trace-coherence, prop-weil-pbc-rational-transport.

### Original step 9 → both new nodes: endpoint/middle coherence, respectively

All the factors in (P), (Z), (C), and the purity composite are natural in their arguments, so the component equation of step 8 is an equality of natural transformations. The unit and successive coefficient-extension equations for $a,b$ are those of [lem-pur-adic-purity-scalar-naturality], rationalized as in step 2; those for $p$ are in [prop-weil-pbc-scalar-extension]. The tensor comparisons respect associators and units and commute with scalar extension by [lem-pur-derived-pullback-tensor-iso]. Under one more extension, substitute these equations for each factor in the displayed pasting: intermediate associators occur consecutively with their inverses and cancel. The remaining external associators are precisely those of $\beta_A$ and $\beta_B$. For the identity extension all these factors are identities. The same substitution with the shift comparisons, which the cited $a,b,p$ respect, gives the shifted equation. Twists use tensor powers of a degree-zero line, so the comparison (Z) introduces no extra shift sign. This proves the last coherence clause with exactly the specified identifications.

Original cited nodes: lem-pur-adic-purity-scalar-naturality, prop-weil-pbc-scalar-extension, lem-pur-derived-pullback-tensor-iso.
