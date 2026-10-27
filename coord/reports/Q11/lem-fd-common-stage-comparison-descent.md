# Worker report — Q11

## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-common-stage-comparison-descent.json`: existing statement unchanged, split into a four-step assembly (1708 characters).
- `dag/nodes/sec-fourier-transform/lem-fd-hom-linear-equivalence.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-fourier-transform/lem-fd-shift-triangle-reflection.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-fourier-transform/lem-fd-mixed-pullback-transformation.json`: statement, unsplit; no Mathlib match.

## Attachments

None. Project-wide searches of `lean/WeilConjectures/` for the blueprint tag and common-stage comparison notions did not locate the full item. I read `lean/Sheaf/Paper/FdCommonStageComparisonDescent.lean`: fdCommonStageComparisonDescent, fdCommonStageHomDescent, fdCommonStageComparisonEquations, fdNormalizedCommonStageDescent, fdFrameworkPullbackFamily_existsUnique, fdMixedPullbackDescent and fdNormalizedPullbackDescent each still have `sorry`. The closed generic comparison_characterization in WeilConjectures/CategoryTheory/FilteredTwoColimitCharacterization.lean is a criterion for a coherent cocone comparison; it does not state the two actual coefficient systems' transport bijections, scalar linearity, descended shift or mixed pullback naturality. No false attachment is claimed.

## WANTED

None. The current blueprint final sentence is available; it specifies the PBC category but gives no proof of this auxiliary comparison. The proof remains explicitly agent-written. No SGA source is used.

## Repair of the return

The only numbered substantive return is the human's re-split order. The live repository, rather than a retained sandbox draft, held the delivered 12-step proof: the sandbox initially contained only dispatcher markers. I copied that current node and retained every existing metadata field, the exact statement, statement dependencies, source and original search records. The released keep_plan stage-1 repair note explicitly reopens it. Three new nodes divide the old work into independent arguments with their own complete hypotheses; all are unsplit, with empty proof/proof_deps, null proof_origin and no Lean changes. The item is now short assembly. Each new statement has roughly the same size (about 3k characters), and none restates the full item.

Ownership of the old arguments: old steps 1–5 belong to lem-fd-hom-linear-equivalence; old steps 6–8 belong to lem-fd-shift-triangle-reflection; old steps 9–11 and the equation-descent portion of old step 12 belong to lem-fd-mixed-pullback-transformation. The final comparison-datum field check of step 12 remains assembly step 4. The full old proof follows verbatim below, so its detailed associator calculation, inverse formula, finite-model reflection and unequal-field naturality calculation are not lost. These are implementation briefs for the later workers, not proof steps in the statement-only nodes.

## Not duplicates

lem-fd-hom-linear-equivalence vs lem-sbc-coherent-pair-functor-descent: the latter constructs additive functors and transformations; it does not assert stagewise Hom bijections, inverses commuting with transport, essential surjectivity or varying-field scalar linearity.
lem-fd-hom-linear-equivalence vs lem-coef-qbar-adjunction-hom-descent: the latter assumes a compatible family of additive group equivalences; it does not establish conjugation compatibility, functoriality, essential surjectivity or Omega-linearity in these coefficient categories.
lem-fd-hom-linear-equivalence vs lem-trf-fully-faithful-ess-surj-equivalence: the latter is the generic equivalence criterion, not the construction or verification of its hypotheses on pairs.
lem-fd-shift-triangle-reflection vs lem-sf-framework-common-stage-descent: the latter has framework categories on both ends and gives forward exactness; here the target is the distinct PBC raw category, with its explicit cone shift, and the statement includes lifting a finite target triangle model and reflection.
lem-fd-shift-triangle-reflection vs lem-trf-exact-equivalence-inverse: the latter assumes an already exact equivalence and proves inverse exactness; it does not descend shifts, prove forward exactness or construct the finite reflection witnesses here.
lem-fd-mixed-pullback-transformation vs lem-sbc-coherent-pair-functor-descent: that generic theorem assumes compatible composite systems; this lemma identifies those comparisons a and c for the two actual pullbacks and obtains their compatibility from the mixed square.
lem-fd-mixed-pullback-transformation vs prop-weil-pbc-descent-functors: that statement has PBC categories at both ends and does not compare framework/PBC coefficient-pullback composites or identify their mixed square.
lem-fd-mixed-pullback-transformation vs lem-sbc-common-stage-inverse-through-karoubi: that statement treats inverses at projectors and outer Karoubi objects; it does not identify the actual cross-framework composite systems.
lem-fd-mixed-pullback-transformation vs lem-fd-frobenius-fixed-pair-comparison: that lemma assumes a simultaneous comparison datum and acts on Frobenius-intertwining pairs; the new lemma supplies its earlier common-stage pullback transformation.
All three new nodes vs lem-fd-common-stage-comparison-descent: each carries one separate argument of the explicitly ordered re-split; no one new node contains the whole comparison theorem or all its clauses. The parent retains the assembly and field check.

Searches before creating the nodes: whole-DAG key phrases conjugation/bijection, inverse Hom-colimit, mixed scalar square, reflection of distinguished triangles; blueprint_refs search 'common stage', 'Hom colimit', 'shift comparison', 'mixed scalar' and 'equivalence'; read the candidate statements above. The blueprint has no exact match. Every new node has blueprint.from.node def-fd-trace-function, with via [the item, lem-fd-rational-coefficient-category-comparison] and a precise final-sentence subclaim location. No new Stacks tags are claimed: these are agent-extracted facts about the blueprint's explicit categories, not Stacks theorems.

## Mathlib searches

For each proposed id I ran and read LeanFinder, LeanSearch, Loogle and grep via the required msearch.py command, then a second semantic phrasing. Exact outputs are retained in search-results.json and search-*.txt; searches.jsonl contains the command's own records. The nodes copy the exact tool/query text and actual hits. The mixed Loogle query using CategoryTheory.NatIso reported an unknown identifier and is explicitly marked as such; it is not evidence by itself.

Hom searches returned ModuleCat.FilteredColimits.M.mk_eq/mk_map, scalar-action facts, Types.FilteredColimit.rel_equiv and generic colimit equivalences. I read ModuleCat/FilteredColimits.lean: these concern a diagram over one fixed ring and do not state the varying-coefficient equivalence or its transport computation. Shift searches returned Equivalence.IsTriangulated.mk', mk'' and Functor.distTriang_iff. I read Triangulated/Adjunction.lean and Localization/Triangulated.lean: the former assumes a given shift-compatible exact functor and the latter assumes a triangulated functor and essential surjectivity on arrows, so neither constructs our descended shift or finite target triangle model in one line. Mixed searches returned CategoricalPullback.mkNatIso and Pseudofunctor coherence. I read Limits/Shapes/Pullback/Categorical/Basic.lean: this is a categorical fiber product of triples, not our common-stage category or actual pullback composite descent. All three new nodes therefore remain unsplit rather than Mathlib leaves.

## Review by Q11

I read the current main-20261015 def-fd-trace-function.md final sentence, the full old item proof, the current chapter/unit records and the released repair note. The final sentence requires using the PBC coefficient category for Frobenius, but does not supply this auxiliary argument, so I retain agent origin. I read every cited assembly node's full statement, including both comparison-datum definitions. For the new tasks I also read the statements of def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category, def-weil-pbc-finite-stage-pair-category, def-weil-pbc-common-stage-cones, the coherent pair-functor lemma, the scalar-extension proposition, the descent-functor proposition and the actual framework pullback definition. These fix the meanings and orientations of every new hypothesis.

Assembly step 1 takes exactly the first new node's stagewise conjugation bijections, inverse Hom-colimit maps, field-preserving functor, essential surjectivity, linearity in both directions and finite-inclusion equality. It does not take shifts or triangles from that statement. I checked the old calculation: the cocycle gives s_X J_N(A_X)=B_X P(r_X)t_X at each endpoint; naturality of j cancels the middle t factors. The inverse transport equation follows from injectivity at the larger stage, with no faithful-transition hypothesis. A finite stage containing both M and lambda exists because Omega is algebraic. Essential surjectivity is up to an isomorphism, never literal equality of objects.

Assembly step 2 invokes the second node only after step 1 has provided its explicit Hom-bijection hypothesis and its prescribed functor. The finite shift comparisons are assumed compatible with j in the unchanged item. I checked the cone definition's third arrow sigma inverse times p_u; identity endpoint classes identify it with the finite-stage cone. Full faithfulness lifts all three component isomorphisms and their inverse equations, and the descended shift comparison handles the third triangle square. I refined the draft statement to introduce its endpoints explicitly and state the triangle-isomorphism conclusion without an embedded proof sketch. Reverse exactness uses the induced inverse shift, not an arbitrary shift structure.

Assembly step 3 takes from the third new node the actual composite families a=J(alpha^s)j_U inverse and c=F^p(j_T) inverse alpha^p, their descent to the actual common-stage functors and the component formula. Both comparisons have source P_U of the finite composite and target the larger-field composite of S_T. Multiplying the mixed square by F^p(j_T) inverse on the left and j_U inverse on the right gives exactly b_L a=c P_U(b_E). The unequal-field representative equation in the new statement is the old step-11 computation, using finite naturality in its middle; no object-only naturality is substituted. All equation descent remains conditional on the finite equations, as the parent says.

Assembly step 4 is an elementary tuple-field check, not an existence theorem for normalized lifts. The coefficient-datum definition asks for literal-pair equivalence, exactness in both directions and the induced finite shift components, supplied by steps 1–2. The pullback-datum definition asks for the compatible transformation of actual composites and precisely the finite component classes, supplied by step 3. Integral and finite fields are already stipulated in the parent's conditional final sentence; none is constructed silently. citations.json has a verbatim statement substring for each of the five assembly citations, and I checked every substring against its file.

Small cases checked for every new statement: E=F=M=N and identity j reduce the Hom and mixed formulas to their finite-stage forms; zero maps and zero objects obey conjugation and linearity; distinct endpoint fields remain covered after taking their compositum; nonfaithful transitions do not invalidate the inverse transport argument; lambda=0, lambda=1 and lambda outside the first representing field are covered by finite enlargement. For triangles a zero or identity cone has the specified sigma inverse third arrow, and reflection is conditional on the target being distinguished. For mixed pullback h=id and b=id yield the identity transformation when those are the assumed finite data. No finite composition or shift equation is inferred without its hypothesis. No stronger geometry than noetherian, finite-dimensional and ell invertible is introduced, and no Karoubi completion appears.

B–E audit: all new objects and hypotheses are introduced in each statement, definition citations are explicit, the three new nodes have no proof steps, and the parent has no long step over 2000 characters. Non-elementary assembly steps cite statements that state their precise conclusion; the elementary last step only fills named tuple fields. No new node is a two-line fact: each owns a roughly 2500–3200 character original argument retained below. No duplicate or circular dependency is introduced. The statements are unchanged in mathematical content; no STATEMENT-DISPUTED correction was needed. The only repairs to the draft were explicit object/endpoint quantification, removal of an unused pullback statement dependency in the first two tasks, and separating finite-cone identification data from proof prose. Report and citations are retained in the sandbox; only the permitted node files and delivery report are submitted.

## What could not be finished

Nothing remains for the requested stage-1 re-split; the three new nodes are intentionally statement-only for later workers. Server dry-run and final delivery results are recorded below when available.

## Original proof retained verbatim and ownership map

### Original step 1 — lem-fd-hom-linear-equivalence

Fix $W$ and suppress it from the notation. All coefficient fields are subfields of the fixed $\Omega$; the index and each overfield index are small directed sets, since a compositum is a finite common overfield. The literal pair constructions in [def-weil-algebraically-closed-coefficients] and [def-weil-pbc-qbar-category] use the same index. Apply the additive pair-functor lemma [lem-sbc-coherent-pair-functor-descent] with $U=S$, $V=P$, $\Phi_E=J_E$, and its comparison $b_{L/E}=j_{L/E}^{-1}$. Inverting the stated scalar cocycle gives precisely that lemma's tower equation; identity normalization supplies its unit condition. It yields the functor on literal pairs with exactly the object and conjugation formulas in the statement. Only its pair-category conclusion is used, before its optional Karoubi extension.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category, lem-sbc-coherent-pair-functor-descent

### Original step 2 — lem-fd-hom-linear-equivalence

Here is the transport calculation, including the associators. For endpoints $X=(E,K)$ and $Y=(F,H)$ put $r_X=j_{M/E,K}$, $t_X=j_{N/M,S_{M/E}K}$, $s_X=j_{N/E,K}$, $A_X=a^s_{N,M,E,K}$, $B_X=a^p_{N,M,E,J_EK}$, and use the analogous symbols for $Y$. The scalar cocycle says $s_XJ_N(A_X)=B_XP_{N/M}(r_X)t_X$. Write $\phi_M(u)=r_YJ_M(u)r_X^{-1}$. Since $u_N=A_YS_{N/M}(u)A_X^{-1}$, substitution gives
$$\phi_N(u_N)=B_YP(r_Y)t_YJ_N(Su)t_X^{-1}P(r_X)^{-1}B_X^{-1}=B_YP(\phi_M(u))B_X^{-1}=(\phi_M(u))_N.$$
The middle equality is naturality of $j_{N/M}$ at $u$. This proves the asserted commuting square on actual Hom transition maps, rather than on abstractly identified Hom groups.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-finite-stage-pair-category

### Original step 3 — lem-fd-hom-linear-equivalence

At a fixed common field $M$, $J_M$ is fully faithful by the assumed equivalence, and conjugation by $r_X,r_Y$ is invertible. Thus $\phi_M$ is a bijection with inverse
$$\psi_M(v)=(J_M|_{\operatorname{Hom}})^{-1}(r_Y^{-1}vr_X).$$
The preceding transport identity and injectivity of $\phi_N$ give $\psi_N(v_N)=\psi_M(v)_N$. Therefore both maps respect eventual equality of representatives, the equality relation in the two pair categories. They descend to maps $[M,u]\mapsto[M,\phi_M(u)]$ and $[M,v]\mapsto[M,\psi_M(v)]$ on the two Hom colimits. Their composites are the identity on every representative. This proves both full faithfulness and the claimed inverse Hom-colimit maps without assuming any transition functor is faithful.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-finite-stage-pair-category

### Original step 4 — lem-fd-hom-linear-equivalence

For any target pair $(E,A)$, choose $K\in\mathcal C^s_E(W)$ and a finite-stage isomorphism $J_EK\simeq A$ using essential surjectivity of $J_E$. Its class at $E$, with inverse represented by the inverse finite map, is an isomorphism $J_W(E,K)\simeq(E,A)$. Together with the preceding Hom bijections, [lem-trf-fully-faithful-ess-surj-equivalence] now makes $J_W$ an equivalence (take a common sufficiently large universe for both pair categories). The object choices and Hom inverses describe its quasi-inverse: choose such a preimage for each target pair and lift morphisms uniquely through the Hom bijections after conjugating by these chosen isomorphisms.

Cited statements: def-weil-pbc-finite-stage-pair-category, lem-trf-fully-faithful-ess-surj-equivalence

### Original step 5 — lem-fd-hom-linear-equivalence

The functor is additive by step 1. For $\lambda\in\Omega$ and $f=[M,u]$, choose a finite $N$ containing $M$ and $\lambda$. The scalar action on both pair categories is represented by $\lambda u_N$. Since $J_N$ is $N$-linear and composition in its target is bilinear,
$$\phi_N(\lambda u_N)=j_YJ_N(\lambda u_N)j_X^{-1}=\lambda\phi_N(u_N).$$
Step 2 identifies this with the transport of $\phi_M(u)$, so $J_W(\lambda f)=\lambda J_W(f)$. The inverse Hom bijections are also $\Omega$-linear: apply the injective linear map $J_W$ to the proposed additive and scalar identities. Conjugating these inverse Hom maps by the chosen object isomorphisms preserves linearity, so the quasi-inverse is linear too.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category

### Original step 6 — lem-fd-shift-triangle-reflection

At stage $E$, the identity comparison $j_{E/E}=1$ makes $J_W\iota^s_E=\iota^p_EJ_E$ on objects and arrows. Let $\delta_E:J_E(-[1])\xrightarrow{\sim}(J_E-)[1]$ be the given exact-functor shift comparison. Compatibility of $j$ with shifts is exactly the transformation-compatibility equation for the families $J_E\circ[1]$ and $[1]\circ J_E$. Apply the compatible-transformation clause of [lem-sbc-coherent-pair-functor-descent]: the classes $[E,\delta_{E,K}]$ give the shift comparison of $J_W$, with inverse given by their inverse classes. Thus the comparison restricts to the specified finite-stage comparison, for the actual pair shifts.

Cited statements: lem-sbc-coherent-pair-functor-descent, def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category

### Original step 7 — lem-fd-shift-triangle-reflection

A distinguished source triangle is isomorphic to the inclusion of a distinguished triangle $D$ over a finite field $M$, by [def-weil-algebraically-closed-coefficients]. Step 6 identifies its image with the inclusion of $J_M(D)$ using the given shift comparison. The assumed exactness of $J_M$ makes this triangle distinguished, so the target definition [def-weil-pbc-qbar-category], whose distinguished triangles are those isomorphic to the common-stage cone triangles of [def-weil-pbc-common-stage-cones] (with $T_{M/M}=\operatorname{id}$, a stage-$M$ distinguished triangle is its own cone triangle there), shows that $J_W$ preserves distinguished triangles. This proves exactness directly on the raw pair categories.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category, def-weil-pbc-common-stage-cones

### Original step 8 — lem-fd-shift-triangle-reflection

Conversely, let a triangle $D$ in the source have distinguished image. In the target pair category choose a finite-stage distinguished triangle $A$ and an isomorphism $J_WD\simeq\iota^p_M A$: by [def-weil-pbc-common-stage-cones] $J_WD$ is isomorphic to a common-stage cone triangle of some $[M,u]$, and the classes $[M,\operatorname{id}]:(E,K)\simeq(M,T_{M/E}K)$ identify that triangle with $\iota^p_M$ of the stage-$M$ cone triangle of $u$, the third arrow by the shift comparison $\sigma_{M/E}$. Choose an exact quasi-inverse $R_M$ of the assumed exact equivalence $J_M$. Then $R_M A$ is distinguished, and $J_MR_M A\simeq A$ as triangles, with the exact-equivalence shift comparisons. Using step 6 gives $J_W\iota^s_M R_M A\simeq J_WD$. Lift the three component isomorphisms and their inverses through the Hom bijections of step 3. Faithfulness, together with the shift comparison, lifts all triangle commutativity equations and the inverse identities. Hence $D\simeq\iota^s_M R_M A$, so $D$ is distinguished by the source definition. Applying this to the chosen quasi-inverse proves reverse exactness. This argument uses only finite-stage exact equivalences already assumed, and never a Karoubi completion.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category, def-weil-pbc-common-stage-cones

### Original step 9 — lem-fd-mixed-pullback-transformation

Fix $h:U\simeq T$. To compare the actual composites, set $A_E=J_{U,E}F^s_{h,E}$ and $B_E=F^p_{h,E}J_{T,E}$. In the orientation required by the pair-functor lemma their scalar comparisons are
$$a_{L/E}=J_{U,L}(\alpha^s)\circ j_{U,F^s_{h,E}K}^{-1},\qquad c_{L/E}=F^p_{h,L}(j_T)^{-1}\circ\alpha^p_{J_{T,E}K}.$$
Indeed both start with $P_{U,L/E}$ applied to the stage-$E$ composite and end with the stage-$L$ composite applied to $S_{T,L/E}$. The actual source pullback representative formula is specified in [def-weil-derived-pullback-tensor-hom]; the target scalar/pullback comparisons and their unit and tower equations are specified in [prop-weil-pbc-scalar-extension], and the actual target common-stage pullback $F^p_h$ is by [prop-weil-pbc-descent-functors] the functor descended from $(F^p_{h,E},\alpha^p)$ by the same conjugation formula $[M,u]\mapsto[M,(\alpha^p)^{-1}F^p_{h,M}(u)\alpha^p]$ as in the pair-functor lemma. Together with the assumed $j$ cocycle these give the composite stage families. The composition clause of [lem-sbc-coherent-pair-functor-descent] identifies their descended functors with the actual $J_UF_h^s$ and $F_h^pJ_T$, respectively.

Cited statements: def-weil-derived-pullback-tensor-hom, prop-weil-pbc-scalar-extension, lem-sbc-coherent-pair-functor-descent, prop-weil-pbc-descent-functors

### Original step 10 — lem-fd-mixed-pullback-transformation

Multiply the assumed mixed scalar square on the left by $F^p_{h,L}(j_T)^{-1}$ and on the right by $j_{U,F^s_{h,E}K}^{-1}$. With the comparisons just defined, it becomes
$$b_{h,L,S_TK}\circ a_{L/E}=c_{L/E}\circ P_U(b_{h,E,K}).$$
This is exactly the compatible-transformation hypothesis of [lem-sbc-coherent-pair-functor-descent], so the components $[E,b_{h,E,K}]$ define a natural transformation $b_h:A\Rightarrow B$. Each is invertible: $[E,b_{h,E,K}^{-1}]$ is its two-sided inverse since the composites are represented by the finite identity maps. Thus it is a natural isomorphism with precisely the claimed components.

Cited statements: lem-sbc-coherent-pair-functor-descent

### Original step 11 — lem-fd-mixed-pullback-transformation

For completeness, the naturality calculation uses the mixed square at both endpoints, not only at objects with field label $L$. For $u:S_{T,M/E}K\to S_{T,M/F}H$, suppress $h$ and write $a_E,c_E,a_F,c_F$ for the stage-$M$ comparisons. The representative of $B[u]\circ b_{E,K}$ is
$$c_F^{-1}B_M(u)c_EP_U(b_{E,K})=c_F^{-1}B_M(u)b_{M,S_EK}a_E=c_F^{-1}b_{M,S_FH}A_M(u)a_E=P_U(b_{F,H})a_F^{-1}A_M(u)a_E.$$
The middle equality is finite-stage naturality of $b_M$; the first and last use step 10. The last expression represents $b_{F,H}\circ A[u]$. Equality of these representatives proves naturality for arbitrary common-stage arrows.

Cited statements: def-weil-pbc-finite-stage-pair-category

### Original step 12 — lem-fd-mixed-pullback-transformation (equations) and parent assembly step 4 (datum fields)

The identity and composition clauses of [lem-sbc-coherent-pair-functor-descent] preserve composite stage families and equations of compatible transformations. Apply them to each finite identity or composition equation for $b$, retaining the actual pullback associators. Shift equations are equations of the shift comparisons descended in step 6, and scalar equations use the same compatible transformations and the scalar calculation of step 5. Thus every equation stipulated in the question descends; no new finite equation is being asserted. Finally [def-fd-coefficient-comparison-datum] asks, at common stage, for the field-preserving conjugation functor, its linearity, exactness in both directions and its induced shift comparisons, all proved in steps 1–8. [def-fd-pullback-comparison-datum] asks for the common-stage transformation of the two actual composites, with its prescribed finite components and mixed square, proved in steps 9–11. Under the stipulated normalized integral and finite rational data these supply exactly those common-stage fields; this does not construct the integral lifts.

Cited statements: lem-sbc-coherent-pair-functor-descent, def-fd-coefficient-comparison-datum, def-fd-pullback-comparison-datum


## Validation repairs

The first complete dry run returned a citation-evidence-length failure: the Hom quote was under 40 characters. I replaced all five evidence snippets with the entire cited statements, preserving verbatim evidence for every clause the assembly takes. No mathematical change was needed.
