# Q58 repair report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-coordinate-ring-euler-polynomial.json: existing statement; repaired split; unchanged mathematical statement; three assembly steps, 1623 characters in total.
- dag/nodes/sec-six-functors-basics/lem-sfb-coordinate-quotient-section-polynomial-tail.json: new statement, status unsplit; no Mathlib match; no proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-twist-euler-section-uniqueness.json: new statement, status unsplit; no Mathlib match; no proof steps.
- citations.json: one verbatim statement quotation for each citation of each parent step.
- searches.jsonl: actual msearch output records, retained without editing.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and coordinate/Euler terminology. The current stage-2 realization in lean/Sheaf/AlgebraicGeometry/ProjectiveCoordinateRingEulerPolynomial.lean has sorry at the two numerical theorems (lines 88 and 107 declarations). It is not a finished attachment.

## WANTED

None. All mathematical sources used are in the repository's literature/stacks-project directory. No SGA source is used.

## Returned point and repair

The return asks for at least two statement-only nodes of comparable size, a parent assembly of at most 3000 characters, and preservation of all six original arguments. The sandbox initially contained only dispatcher marker files, without a node, report, or search log. I copied the current repository node, which retains the returned six-step proof and the later stage-2 correction identifying the ambient absolute Proj twist. The existing statement, source and maintainer metadata are retained. There is no statement dispute or change to target meaning.

The allocation is balanced by mathematical argument, not by chopping the conclusion into clauses:

- The coordinate section/polynomial node carries old steps 1, 2, 5 (853 + 764 + 429 = 2046 characters): the chart identification for the actual quotient, verification of the section-tail hypotheses and scalar action, monomial finiteness, and the standard-graded polynomial theorem. Its statement includes the canonical maps and chart formulas, not an Euler characteristic.
- The projective cohomology/uniqueness node carries old steps 3, 4, 6 (649 + 487 + 708 = 1844 characters): uniform Serre vanishing, the Euler sum and empty-space calculation, and uniqueness from infinitely many rational roots. It is stated for any quasi-coherent finitely presented module on a projective closed subscheme. It neither mentions a coordinate quotient nor asserts existence of its coordinate polynomial.

The first and third original arguments already use general theorems present in the DAG. Those theorems remain reusable prerequisites for future workers; their proofs are not duplicated in the parent or the new nodes. The explicit human re-split instruction requires exposing these two argument blocks even though some of the final numerical consequences are elementary after those general theorems. No new standalone node is made for root counting or for a tensor unit identity.

The parent now (1) obtains the section/polynomial data, (2) applies projective cohomology to the structure sheaf and takes the maximum bound, and (3) applies uniqueness on the same embedded closed subscheme, including the empty case. No step is longer than 2000 characters. Both new nodes have empty proof and proof_deps and null proof_origin. The complete original proof is preserved below as handoff material, outside those statements.

## Review by Q58

I read the worker brief, the three-level route in SETUP.md, GOAL.md, the stage-1 contract, the whole delivery-errors sections B through E, and the chapter and unit records. This remains the small projective-coordinate prerequisite on the existing alteration/Isom-graph route; it changes no chapter or unit. blueprint_refs ancestor reports a null blueprint ancestor for this existing created chain. I retained that result and inherited its full via chain, adding this item at the front for the two new nodes. Whole-blueprint searches for homogeneous coordinate, graded twist, global sections, Euler characteristic, vanishing and Hilbert polynomial did not find the combined statements of either extracted task.

For the item and the first new node I opened coherent.tex, lemma-recover-tail-graded-module (0AG7), constructions.tex, lemma-apply-modules (01MT) and lemma-surjective-graded-rings-generated-degree-1-map-proj (01N1), and algebra.tex, proposition-graded-hilbert-polynomial (00K1) with its finite-piece context. I checked the actual finite graded module statement in lem-sfb-finite-graded-module-section-tail and the finite-dimensional/polynomial statement in lem-trf-standard-graded-hilbert-function, not merely their names. For S=M=A, A_0 is either k or the zero ring, hence Noetherian; the finitely many images of the variables generate in degree one. Restricting an A_0-linear map along k to A_0 gives precisely the required k-linear map even for A=0. For the algebraic polynomial use S=B and M=A, not A_0 as a field: A is generated over B by 1, including when 1=0. This keeps the unit-ideal edge case valid. The chart basis u_j^m is invertible after localization; on overlaps its ratio is (u_i/u_j)^m. Thus theta uses exactly the absolute Proj twist specified in the current item, and sigma(h) is (h/u_j^m)e_j. Empty charts are zero modules.

For the second new node I opened coherent.tex, lemma-coherent-projective (01YS), including its finite-cohomology and vanishing assertions, and varieties.tex, lemma-hilbert-polynomial-H0 (08AE) and proof. I also read the full statement of lem-weil-pbc-closed-immersion-serre-vanishing: it supplies a single natural bound for all positive cohomology degrees for a quasi-coherent finitely presented module. That is stronger than just a fixed-q bound and is the bound the original proof uses. In the extracted statement, the additional finite-dimensionality for all twists follows the finite-cohomology part of the same projective theorem in its closed-immersion form. The root argument is the explicitly agent-written elementary part already present in the return; it makes no claim that 08AE itself states polynomial uniqueness.

Parent step 1 cites only the first new node. Its statement provides the exact L_m, canonical section map, k-linearity, eventual isomorphism, finite-dimensionality and P_J. Parent step 2 cites only the second new node: its general F is specialized to O_Z, whose local finite presentation is displayed in the step, and whose tensor product with any sheaf is the unit identification. The statement supplies both uniform positive-degree vanishing and the Euler/H0 equality. Combining the two bounds uses only arithmetic. Parent step 3 cites the second new node's conditional polynomial uniqueness and empty-scheme clauses. The two presentations of the same embedded closed subscheme have the same pullback of the fixed ambient twist; step 1 for each presentation supplies the two eventual section-dimension equalities. Thus uniqueness is applied to a single section function. No independence under changing the projective embedding or polarization is asserted. Every parent citation has its actual statement copied verbatim in citations.json, and the union of uses is exactly proof_deps.

I checked small cases against both new statements: J=0 on projective space (usual monomial dimensions); N=0; J=B, where A_0=0 and every piece and chart is zero; J=(z_0^r) for N=0, where Proj is empty but some initial pieces survive; and J=(x^2,xy) in k[x,y], whose saturation is (x) and whose first pieces differ but agree in degree at least two. The comparison is eventual, so none of these counterexamples to an all-degree assertion invalidates it. In the second task F=0 and X empty give zero groups, zero Euler characteristic and zero eventual polynomial; arbitrary fields, nilpotents and disconnected schemes require no extra hypotheses. Rational roots are evaluated at natural integers inside Q, which are distinct in every characteristic of k because they are roots in Q, not in k.

The search log contains two semantic phrasings for each new task, Loogle queries and direct Mathlib grep queries run only through msearch.py. LeanSearch was rate limited and is recorded unavailable. LeanFinder returned affine Proj chart statements for the first task and categorical projective-dimension lemmas for the second. Loogle's first AlgebraicGeometry/eulerChar pattern reported an unknown identifier; I retained that diagnostic and then used the valid quoted eulerChar search, which returns the general Euler-characteristic-of-complexes API. I opened Mathlib/Algebra/Homology/EulerCharacteristic.lean: it does not provide coherent sheaf cohomology or Serre vanishing. I also opened Mathlib/RingTheory/Polynomial/HilbertPoly.lean: its theorem is about coefficients of p/(1-X)^d; the file explicitly lists Hilbert polynomials of finite graded modules as TODO. None is an exact match or one-line specialization of either new task. All queries and results in the new nodes are drawn from searches.jsonl; no search is invented.

I checked C1/C4 at the parent interface, all hypotheses above, and each old argument against its new task interface. The new nodes contain only self-contained mathematical assertions, no hidden proof sketches. There is no dependency back to the parent, no claim that an unsplit child is proved, and no reliance on a definition node for a theorem. The two extracted blocks are distinct from the parent's coordinate/Euler comparison: its proof genuinely combines them. Existing broader flat-family nodes depend on this comparison and cannot be used to prove it without a cycle.

## Not duplicates

- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-trf-standard-graded-hilbert-function: states finite graded dimensions and eventual polynomial, but has no Proj sheaf, canonical sigma map or quotient pullback chart comparison; it is a reusable prerequisite for the extracted section argument.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-sfb-projective-coordinate-ring-euler-polynomial: the parent compares coordinate dimensions with Euler characteristics and proves presentation independence; this new task omits one side of that comparison and the parent must combine both tasks.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-sfb-finite-graded-module-section-tail: states the abstract shifted-module section isomorphism; it does not identify quotient twists with a pulled-back ambient twist or give their eventual polynomial and chartwise canonical section map.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs def-sfb-coordinate-quotient-grading: constructs the quotient grading only, with no sheaf comparison, cohomology, or eventual section/polynomial assertion.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-sfb-standard-proj-twist-tensor: identifies tensor twists and shifted-module sheaves, but gives neither eventual global sections nor finite dimensions or a coordinate polynomial.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-sfb-graded-proj-quotient-twist-comparison: gives the canonical quotient pullback comparison and its local formulas, but neither recovers high graded pieces from global sections nor supplies their polynomial; it is reused as a prerequisite, not re-created as a separate chart lemma.
- lem-sfb-coordinate-quotient-section-polynomial-tail vs lem-weil-pbc-projective-space-twisting-sheaf-charts: concerns the absolute integral O(1) charts; it does not identify arbitrary quotient twists, recover graded sections, or give their polynomial.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-proj-serre-h1-vanishing: is only H1 vanishing on P1, whereas the extracted task treats arbitrary projective dimension and closed subschemes and includes Euler/uniqueness data.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-j4-closed-immersion-twist-cohomology-bound: bounds cohomological degree q>N, with no uniform high-twist vanishing for the remaining positive degrees or Euler/uniqueness conclusion.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-j4-closed-immersion-twist-vanishing-step: is a conditional descent step in cohomological degree, not the complete uniform cohomology/Euler/uniqueness interface.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-twisted-section-finite-coordinates: gives finite coordinates for sections on P1; it has no general projective higher vanishing, Euler sum or polynomial uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-d2-nonnegative-projective-twist-vanishing: concerns only O(m) on projective space itself, not coherent modules on arbitrary projective closed subschemes and their Euler/uniqueness interface.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-section-module-construction: constructs a graded section module on P1 without coherence or finiteness; it asserts no Serre vanishing or Euler/uniqueness theorem.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-section-coordinate-surjective: is a multiplication-surjectivity assertion for high P1 sections, not cohomology concentration, Euler reduction or uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-section-module-component-finite: concerns a single homogeneous component of a given P1 section module; it supplies none of the arbitrary-projective Euler/vanishing/uniqueness conclusions.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-section-action-laws: constructs the action on a P1 section module, not a cohomology vanishing or Euler/uniqueness theorem.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-c2-closed-immersion-fixed-degree-vanishing: allows the bound to depend on q; the extracted block gives one bound for every q>0 and the Euler and polynomial uniqueness consequences.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-d2-closed-immersion-twist-acyclic-presentation: constructs an acyclic source presentation for a fixed cohomological degree, not the full cohomology/Euler/uniqueness assertion on X.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-twisted-sections-finite-dimensional: gives only finite-dimensional H0 on P1, with no arbitrary-projective vanishing, Euler equality or conditional polynomial uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-twisted-sections-constant-action: identifies scalar actions for P1 sections; it does not assert vanishing, finite-dimensional cohomology, or an Euler/polynomial result.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-u3-projective-finite-cohomology-presentation: constructs one finite-cohomology presentation source, not finiteness and vanishing of all the actual twisted cohomology groups plus Euler/uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sc-p1-section-module-tail-finite: concerns finite generation of a P1 section-module tail; it has no general projective cohomology/Euler/uniqueness interface.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-p2-projective-finite-source-cohomology-segment: gives an exact segment with a finite source; it does not conclude cohomological concentration, Euler reduction or polynomial uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-pc-m1-projective-affine-finite-cohomology-independent: supplies finite cohomology over an affine Noetherian base, but no uniform twist vanishing, Euler reduction or polynomial uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sfb-standard-proj-coherent-section-finiteness: states Noetherianity and finite generation of the entire section tail, not high-twist cohomology concentration with Euler and conditional polynomial uniqueness.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sfb-flat-graded-tail-proj: is a relative flatness and base-change assertion with a field coordinate/Euler corollary, not the canonical section/polynomial interface or the general-F vanishing/Euler uniqueness interface; it depends on the parent.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sfb-projective-coordinate-ring-euler-polynomial: the parent compares coordinate dimensions with Euler characteristics and proves presentation independence; this new task omits one side of that comparison and the parent must combine both tasks.
- lem-sfb-projective-twist-euler-section-uniqueness vs def-sfb-projective-coordinate-hilbert-polynomial: defines a coordinate Hilbert polynomial predicate using kernels of restricted homogeneous polynomials, not the actual quotient section map or the cohomology and uniqueness theorem.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-sfb-flat-projective-hilbert-polynomial-locality: concerns local constancy and base change in flat projective families; it does not state the extracted canonical section maps or general-F cohomology/conditional uniqueness task, and depends on the parent.
- lem-sfb-projective-twist-euler-section-uniqueness vs lem-weil-pbc-closed-immersion-serre-vanishing: supplies uniform higher vanishing but not finite-dimensionality, the Euler reduction or the conditional uniqueness/empty-polynomial assertions; it remains the generic prerequisite for this human-requested argument block.

## Original argument retained for the next workers

These are the six returned steps verbatim, as handoff context. They are not proof steps in either new unsplit node. All their arguments are allocated above; the existing general theorem nodes they cite remain prerequisites for later splitting.

### Old step 1

Write $u_j$ for the image of $z_j$ in $A$. The opens $V_j=D_+(u_j)$ cover $Z$. For $m\ge0$, the associated sheaf $\widetilde{A(m)}$ has on $V_j$ the module $(A_{u_j})_m$, free of rank one over $(A_{u_j})_0$ with basis $u_j^m$. Indeed division by the invertible homogeneous element $u_j^m$ identifies degrees $m$ and zero, with inverse multiplication by it. On $V_i\cap V_j$ the bases satisfy $u_i^m=(u_i/u_j)^m u_j^m$. By the gluing definition of the projective twist and its pullback, these are exactly the bases and transition functions of $i^*\mathcal O_{\mathbf P^N_k}(m)$. Sending $u_j^m$ to its pulled-back local basis therefore gives a sheaf isomorphism $\widetilde{A(m)}\cong\mathcal O_Z(m)$; the formulas agree on overlaps. Empty charts contribute the zero module. This uses the actual quotient algebra, without replacing $J$ by its saturation.

Cited nodes: def-pc-proj, def-weil-pbc-proj-twisting-sheaf, def-pc-projective-space-twist, def-pc-module-pullback.

### Old step 2

The degree-zero ring $A_0=k/(J\cap k)$ is either $k$ or the zero ring, hence Noetherian: an ideal of a field is zero or generated by one. The images $u_0,\ldots,u_N$ generate $A$ over $A_0$ in degree one. As a graded module over itself, $A$ is generated by $1$ in degree zero (the zero module is allowed). Apply the finite graded-module section-tail theorem with $S=M=A$, then step 1, to get an $A_0$-linear isomorphism $A_m\cong H^0(Z,\mathcal O_Z(m))$ for $m\ge a$, with $a\ge0$. Restriction along $k\to A_0$ makes this $k$-linear. Every $A_m$ is finite-dimensional: the images of the finitely many total-degree-$m$ monomials in $N+1$ variables span it. Consequently $H^0(Z,\mathcal O_Z(m))$ is finite-dimensional and has dimension $\dim_k A_m$ in these degrees.

Cited nodes: lem-sfb-finite-graded-module-section-tail.

### Old step 3

Apply closed-immersion Serre vanishing to the given $i:Z\hookrightarrow\mathbf P^N_k$ and $\mathcal F=\mathcal O_Z$. Its coefficient ring $k$ is Noetherian as checked in step 2. The structure sheaf is quasi-coherent and of finite presentation: on every open it is the free module of rank one, presented by $\mathcal O^{\oplus0}\to\mathcal O\xrightarrow{\mathrm{id}}\mathcal O\to0$. Tensoring this unit module with $i^*\mathcal O(m)$ gives $\mathcal O_Z(m)$. The cited theorem supplies a single $b\ge0$ such that $H^q(Z,\mathcal O_Z(m))=0$ for every $q>0$ and every $m\ge b$. No smoothness, reducedness, saturation or nonemptiness hypothesis is used.

Cited nodes: lem-weil-pbc-closed-immersion-serre-vanishing.

### Old step 4

For $m\ge m_0=\max(a,b)$, all positive-degree cohomology groups vanish and the degree-zero group is finite-dimensional. In the defining alternating sum for $\chi(Z,\mathcal O_Z(m))$, only degree zero remains. Thus $\chi(Z,\mathcal O_Z(m))=\dim_k H^0(Z,\mathcal O_Z(m))=\dim_k A_m$, as required. If $Z=\varnothing$, all sections and cohomology groups are zero, so the section-tail isomorphism also gives $A_m=0$ for $m\gg0$, including unsaturated ideals supported at the irrelevant ideal.

Cited nodes: def-pc-euler-characteristic.

### Old step 5

For existence of the eventual polynomial, apply the standard-graded Hilbert-function theorem with $S=B$ and $M=A$, viewed as a graded $B$-module. Here $B_0=k$, the variables form a finite degree-one generating set, and $A$ is generated as a $B$-module by $1$; this works even if $J=B$, when $A=0$. It yields $P\in\mathbf Q[t]$ with $P(m)=\dim_k A_m$ eventually. Step 4 identifies those same values with $\chi(Z,\mathcal O_Z(m))$.

Cited nodes: lem-trf-standard-graded-hilbert-function.

### Old step 6

If $J_1,J_2\subseteq B$ define the same closed subscheme of this fixed projective space, then the induced $i:Z\hookrightarrow\mathbf P^N_k$ and its pulled-back twists are the same. By step 4 their coordinate Hilbert functions agree with the same Euler function above the maximum of the two bounds. Hence their eventual polynomials agree at infinitely many nonnegative integers and are equal: a nonzero polynomial over $\mathbf Q$ has at most its degree many roots, by induction using division by $t-r$ at a root $r$. For the empty closed subscheme these polynomials agree with zero eventually and are zero by the same argument. Independence is for the closed subscheme with its indicated embedding and twist.

Cited nodes: (elementary polynomial root argument).

## Outstanding work

The two new statement-only tasks require their own future splits and Lean proofs, as explicitly requested by the return. This delivery repairs stage 1 only. No Lean file was changed, and no compiler or build tool was run.
