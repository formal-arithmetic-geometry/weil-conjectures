# Worker report — Q76

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-finite-evaluation-rectangle-replacement.json: existing statement, repaired split; five-step assembly, 2034 characters (previously fourteen steps, 9461 characters).
- lem-sfb-ordered-coset-finite-chain-projection: new statement, unsplit; Mathlib searches found no exact/generalizing declaration.
- lem-sfb-equivariant-prefix-finite-chain-homotopy: new statement, unsplit; Mathlib searches found no exact/generalizing declaration.
- lem-sfb-coset-averaged-homogeneous-residual: new statement, unsplit; Mathlib searches found no exact/generalizing declaration.
- lem-sfb-nonarchimedean-finite-evaluation-calculus: new statement, unsplit; Mathlib searches found no exact/generalizing declaration.

The four new JSON files are under the same dag/nodes/sec-six-functors-basics/ directory. Also written: citations.json, the actual searches.jsonl produced by msearch.py, this report, and sandbox-only baseline.json / repair.py / small_cases.py / write_report.py. No repository or launcher file was written; no Git command, Lean edit, compilation, Lake invocation or agent delegation was performed.

## Attachments

None. Searching the source by the item tag, its name, rectangle/replacement and the four extracted concepts found no exact finished declaration in WeilConjectures/. The named Sheaf.RepresentationTheory.BoundedFiniteEvaluationRectangleReplacement theorem exists but its proof is `sorry`; its docstring reproduces the fourteen-step baseline. It is not an attachment. The node statement is preserved exactly, including its statement dependencies; the stage-2 representation uses positive degree n+1, which agrees with the mathematical n>=1 convention.

## WANTED

WANTED: an exact reference for the ordered-coset partial resolution comparison, its continuous finite-evaluation homotopy and normalized transfer, for lem-sfb-ordered-coset-finite-chain-projection, lem-sfb-equivariant-prefix-finite-chain-homotopy, lem-sfb-coset-averaged-homogeneous-residual, and lem-sfb-bounded-finite-evaluation-rectangle-replacement. The main-20261015 direct-images proof paragraph (3) was read: it gives the open-direct-image coefficient-comparison route but does not assert these auxiliary cochain lemmas. These are honestly agent-formulated obligations, not attributed to a nonexistent Stacks theorem. The finite-evaluation calculus lem-sfb-nonarchimedean-finite-evaluation-calculus is also agent-formulated at that auxiliary place. No SGA source is used.

## What was wrong and what changed

This is the requested work-spreading repair. The baseline delivered argument had 9461 proof characters, so it was too large for one worker. The sandbox initially held only dispatcher .brief markers, no earlier node/report/search log. I copied the live node without changing any maintained metadata and retained it as baseline.json. The repaired node has four new unsplit dependencies of comparable statement size (2157, 1975, 2331 and 2027 characters); none is a copy of the whole item. Their proofs are empty, proof_deps empty and proof_origin null. They introduce their own data and hypotheses, allowing their proof work to start independently.

The allocation is exact: original steps 2–6 (including the free tuple conventions of step 3) belong to lem-sfb-ordered-coset-finite-chain-projection; original steps 3 and 7–9 belong to lem-sfb-equivariant-prefix-finite-chain-homotopy; steps 10–11 and the denominator clause of 12 belong to lem-sfb-coset-averaged-homogeneous-residual; the evaluation-composition part of 12 and steps 13–14 belong to lem-sfb-nonarchimedean-finite-evaluation-calculus. The existing homogeneous-coordinate node still handles original step 1 and the coordinate conversion in step 12. The assembly still spells out the cumulative-product and consecutive-ratio substitutions. The full original texts below preserve every argument for the workers taking the new nodes; they are report material, not hidden proof steps in unsplit nodes.

No statement dispute or mathematical weakening was necessary. In particular, do not replace the open subgroup by a normal one, add completeness or closedness of subspaces, weaken cochain equalities to cohomology equalities, or drop the degree-one case.

## What could not be finished

No outstanding repair point. The four extracted obligations are deliberately statement-only as the return requires; this delivery proves their assembly in words, not the four new nodes themselves. Exact external references remain WANTED as above.

## Not duplicates

lem-sfb-ordered-coset-finite-chain-projection vs lem-sfb-ordered-join-partial-contraction: the latter contracts the colored join with specified anchors; the new node constructs an input-anchored H-equivariant chain map from uncolored tuples into that join, including the continuous coset retraction and fixed tuple expansion. It cites the existing contraction as a statement dependency rather than duplicating it.
lem-sfb-equivariant-prefix-finite-chain-homotopy vs lem-weil-pbc-site-cech-free-complex-exact-fibrewise: the latter supplies a contracting identity for a particular site Cech complex and asserts no naturality; the new node compares an arbitrary finite-evaluation H-equivariant tuple-chain endomorphism with identity, with its specified prefix recursion and continuous integral formulas.
lem-sfb-coset-averaged-homogeneous-residual vs lem-sfb-continuous-cochain-finite-index-transfer: transfer gives a cochain map between group cochain complexes and an index homotopy, but no residual from supplied A,Q, prescribed support set, or fixed evaluation coefficients k/m.
lem-sfb-coset-averaged-homogeneous-residual vs lem-sfb-homogeneous-cocycle-rectangle-detection: rectangle detection gives an existential primitive after restriction to H, not the G-invariant averaged residual for an arbitrary supplied chain comparison and support set.
lem-sfb-nonarchimedean-finite-evaluation-calculus vs lem-sfb-bounded-finite-evaluation-rectangle-replacement: the new node assumes arbitrary finite evaluation lists on compact spaces and proves their analytic/parameter calculus; it neither constructs a cochain homotopy nor imposes a rectangle. It is a tool for the assembly and cannot imply the item alone.
lem-sfb-ordered-coset-finite-chain-projection vs lem-sfb-finite-index-rectangle-primitive-operator: the existing node provides a primitive for already rectangle-vanishing cocycles, not an integral chain projection on all tuples.
lem-sfb-equivariant-prefix-finite-chain-homotopy vs lem-sfb-finite-index-rectangle-primitive-operator: the existing node gives no chain homotopy for an arbitrary supplied augmented endomorphism.
lem-sfb-coset-averaged-homogeneous-residual vs lem-sfb-finite-index-rectangle-primitive-operator: that node has no residual on nonvanishing cocycles or generic supported chain comparison input.

The whole DAG was searched for ordered joins, prefix homotopies, coset averaging and finite evaluations, then the potentially relevant statements above were opened. The whole imported blueprint was searched with tools/blueprint_refs.py for chain homotopy, rectangle, finite evaluation, ordered join, coset and norm; no blueprint node states these four lemmas. The ancestor command reports None for this item's inherited created.item chain ending in a module. Accordingly the existing null from.node is retained; each new node prepends the item to via and fills the precise auxiliary source place. No unrelated ancestor was invented. No new source uses a Stacks tag, so there are no same-tag pairs requiring further differentiation.

## Mathlib search review

Each new node has five actual logged searches: LeanFinder, LeanSearch with a different wording, grep, and two Loogle queries. All queries/results in the node are copied from searches.jsonl. The first four Loogle requests reported overload; their verdict is unavailable, even though the wrapper marks the transport ok. The subsequent requests ran and returned results or an actual empty result. Both semantic searches ran for all four nodes. No search was invented or copied from another group's log.

For the projection, the hits are Haar integrals, generic homotopy objects and Rep.barResolution; none states the colored-coset comparison. For the prefix lemma, Homotopy.mkInductive and Dold–Kan normalization homotopies do not supply the required components, their equivariance or finite continuous formulas. I read Algebra/Homology/Homotopy.lean around the inductive constructor's input requirements and RepresentationTheory/Homological/Resolution.lean's standard/bar resolution description. For averaging, low-degree group cochain identities, Haar integration and homology corestriction are not the supplied-A,Q residual statement; I read GroupCohomology/Basic.lean and GroupHomology/Functoriality.lean's corestriction definition. For the calculus, Mahler series concern a complete target and an infinite series on Z_l; generic operator norm lemmas assume the bounded map is already constructed. ContinuousMap/Compact.lean gives normed-space instances, not the whole finite-evaluation and parameter claim. No hit makes any of the four nodes a one-line specialization. All four therefore remain unsplit; there are zero new Mathlib leaves.

## Review by Q76

I read main-20261015's direct-images proof paragraph (3), the unit and chapter records, the full live fourteen-step item proof and its Sheaf Lean declaration/docstring. For each extracted node its source is this same auxiliary place, with the exact old step range recorded; I checked its new statement against those actual old steps, rather than treating a source label as evidence for an unstated theorem. I also read the actual statements of topological-homogeneous-cochain-coordinates, ordered-join-partial-contraction, free-module and l-adic-numbers, and the neighboring primitive/transfer/rectangle-detection statements used in the duplicate audit.

Assembly step 1 uses the coordinate node's two displayed inverse formulas and its explicit cochain identities, including degree zero. Its topological-vector-space hypotheses hold for the stipulated norm topology; no completeness is needed. Step 2 uses exactly the new projection node's chain identity, H-equivariance, augmentation, continuous integral expansions and top-degree rectangle support; these meet every input of the new prefix lemma. The prefix lemma then supplies precisely the identity 1-A=boundary Q+Q boundary and the finite expansions. This is not a citation to an existential comparison theorem without continuity data.

Step 3 uses the new residual node's displayed cochain equalities, cocycle assertion, vanishing clause and k/m evaluation formulas. Its E is the actual ordered rectangle; its coefficient action is trivial as required. Step 4 uses the coordinate node's cochain-map formulas and the residual node's invariant outputs. I checked domains: Q_(n-1) maps degree n-1 chains to degree n chains; A_n stays in degree n. Thus after Phi the evaluation maps have domains G^(n-1) and G^n respectively, and both land, after consecutive ratios, in G^n. These are the claimed maps, not an implicit appeal to naturality. Step 5 uses the new calculus node's precise integral-denominator bound, subspace and parameter clauses, with the nonempty compact powers of G (including the one-point G^0). The coefficient m is positive and prime to ell. Pointwise identities apply to every parameter slice, including the empty-parameter case. citations.json contains an actual verbatim statement passage for every cited node in every step.

I checked the extraction itself on edge cases. In the projection n=1 uses only S_0, within the original contraction range -1<=q<=n-1; the augmentation makes the q=1 cycle check valid. Coincident cosets or repeated a_i do not identify colors: the join retains labels, so the rectangle assertion is still valid. In the prefix lemma the q=0 error chain has augmentation zero, Q_(-1)=0, and the cone equation includes the augmented degree -1. Its recursion is performed on basis tuples before linear extension, so it never asserts a varying anchor is linear. In the averaging lemma sg=hu permutes right cosets Hs; it does not require H normal or that left multiplication permutes those cosets. The supplied homotopy is available through degree n, so applying F to boundary Q_n legitimately uses the degree-n cocycle equation. The residual's cocycle identity follows from delta squared zero on all tuple functions, not from a nonexistent A_(n+1).

The calculus node allows incomplete or zero V, nonclosed W, an empty sum and an empty parameter space. Its norm estimate is the finite ultrametric maximum bound, not an Archimedean sum-of-coefficients bound. Compactness ensures finite suprema and no convergence in V is used. For a positive degree-one cochain the averaged homogeneous primitive has one coordinate, hence G-invariance makes it constant; Phi_0 has the stipulated zero differential. These checks preserve every clause of the baseline statement.

As an additional finite-model check, sandbox small_cases.py implements the stated colored-join S, P and prefix Q over S3 with the nonnormal order-two subgroup (index 3). It checked chain-map and homotopy identities, H-equivariance, top rectangle support, and the averaged cocycle assembly in degrees 1,2,3. The chain checks covered 42,258,376 tuples respectively (all tuples through degree 2, sampled degree 3); invariant coboundaries in degrees 2 and 3 were verified nonzero. All assertions passed. This is a finite edge-case check, not a substitute for proving the unsplit obligations. Direct expansion at q=0 also gives Q_0[x]=[x,x]-[x,rho(x)a_0] as in the retained proof.

Against delivery-errors B–E: each new node introduces every object and uses inline definitions or genuine statement dependencies; none contains proof steps or a proof sketch. The original statement and metadata are retained. All non-elementary assembly inputs are stated in cited nodes, and the quotes were checked literally (C1/C4). No new dependency points to the item, so there is no self-reference; all four proof jobs can be started from their supplied hypotheses independently. No whole item or item clause was merely renamed: the first two outputs are integral chain data, the third is a generic cochain consequence with supplied chain data, and the fourth is evaluation calculus on arbitrary compact spaces. No unit-route departure, off-unit proof tool or new SGA reference was introduced. Every assembly step is below 2000 characters; the sum is below 3000. The four new statements have comparable sizes and preserve all old arguments as the following allocation appendix shows.

## Repair of landing return (2026-10-22)

L returned branch head c6185f7e1e6 at 06:35 UTC after the mathematical reader approved it: the side-project completion had not been promoted to the live DAG read by the queue. This is a rebase repair of that landing refusal, continuing the same four-node extraction and preserving its full argument, search log and citations. The released stage-1 repair note still requires at least three new independent statement-only nodes and a short assembly; the four retained nodes satisfy that order.

I compared every field of baseline.json with the current read-clone item: they agree exactly. The sandbox differs only in proof, proof_deps, proof_origin and split_report. Its statement, statement dependencies, source and blueprint provenance are unchanged. None of the four extracted node ids exists in the current read-clone DAG. The required deliver.py dry run reconstructs the delivery on current origin/sheaf-dag, preserving maintained metadata, rather than reusing the returned branch base; it exited successfully with preflight passed at d2602a21cd9 before this report update. This report and the split_report now explicitly record the landing repair, so the new delivery is reviewable against the current base.

I re-read the current statements of every existing dependency used by the assembly or extracted statements: topological-homogeneous-cochain-coordinates, ordered-join-partial-contraction, free-module, l-adic-numbers and size-convention. The current coordinate statement includes the derived isomorphism and, explicitly, the actual inverse cochain maps and degree-zero formulas needed here. Thus steps 1 and 4 use its statement directly. The contraction still supplies its identity through degree r-2, naturality and equality-test-free integral expansion; with r=n+1 the projection uses S only through n-1. The free-module and coefficient definitions still supply precisely the basis and scalar conventions used by the extracted statements. I also re-read all four retained new statements and checked the seven assembly citations literally against citations.json. None requires a changed hypothesis or formula on the current DAG. No unsupported inference, mathematical statement change or new search question was introduced by this rebase, so the logged searches were retained without repetition.

The return is a landing-state mismatch, not a mathematical counterexample. The proof retains nonnormal H, incomplete V, arbitrary linear subspaces, degree one and empty parameters. The source remains explicitly agent-formulated at the blueprint's direct-images paragraph (3); no new literature attribution or SGA route was introduced. The report's original review and complete fourteen-step allocation remain below. Final validation and push are performed after this update; their command output is authoritative.

## Current landing-return repair audit (2026-10-22, renewed retry)

The required initial dry run of the retained delivery completed successfully at 99f199ce20a (preflight passed, not pushed). It reconstructed the delivery against the current server DAG. This retry preserves the earlier mathematical approval as history and supplies a newly checked delivery; it is not an unchanged re-push. The current read-clone item still equals baseline.json in every JSON field. The four extracted node ids are still absent from that DAG, and the released stage-1 re-split note still requires at least three statement-only nodes and assembly at most 3000 characters. The existing four-node extraction meets that order without dropping any argument.

I re-read the five current dependency statements, the four extracted statements, the full recorded search results, the blueprint source paragraph (3), and the unit/chapter route. The homogeneous-coordinate statement still explicitly gives actual cochain maps (in addition to its derived isomorphism), so steps 1 and 4 need no replacement citation. The ordered-join contraction still gives its degree range, naturality and fixed finite expansion needed by the projection. The free-module definition supplies the specified bases, the l-adic definition fixes the scalar field and valuation, and size-convention retains the universe convention. None of these changes the mathematical input compared with the retained citations. The seven citation entries remain literal statement passages; all proof uses are covered (C1/C4). In step 2 the augmented chain identities and H-equivariance match the homotopy inputs; in step 3 the rectangle is exactly E and the action is trivial; step 5 uses nonempty compact powers and the prime-to-ell positive index. Nonnormal H, incomplete V and nonclosed coefficient subspaces remain allowed.

One wording correction arose on rereading step 5: Phi_0 is an operator from homogeneous degree-zero cochains to V, not a function with domain G^0. I changed the sentence to say that Tc is a function on G^0, whose differential is d^0=0. This is the degree-one edge case already proved by the cited coordinate formulas, and changes no statement or search question. The assembly now has 2034 characters; every individual step is below 2000. The original fourteen-step proof and its allocation below are retained verbatim. No new node, source attribution, definition, or hypothesis was introduced; existing logged searches are reused without claiming to rerun them.

For a reproducible current comparison, the SHA-256 hashes of the re-read statement strings (UTF-8, after JSON decoding) are:

- lem-sfb-topological-homogeneous-cochain-coordinates: `2520d1b9177e98fe446ad707fc42770e16a3305213be22d171deab60e8cb2de8`.
- lem-sfb-ordered-join-partial-contraction: `3de5f074adf422e28294947e89b398cda12ef14cd8016a94238fde3bbf710b89`.
- def-weil-pbc-free-module: `d044e53c011c88987bfe0d8065edfcd8a8432286fef324506c1d49d3a71f1b20`.
- def-weil-l-adic-numbers: `2940d8e2936f99fb180374baaea6ec9fd97bdfd32ea9899099ab5b3b09967bd0`.
- def-weil-size-convention: `ae70e9588534895e24d390692173670d382f84fc7444b8a6d171cd35cbef2d7c`.

The final dry run and push follow this update; their process outputs determine delivery status. Earlier receipts above are historical validation, not claims that this renewed retry has already been pushed.

## Checks

- Sandbox small_cases.py: PASS, exact rational/integer finite model.
- Server srvcheck check_dag: OK, no finding introduced by the sandbox or on its nodes.
- Server srvcheck review_split: PASS.
- Required delivery dry run and push: pending at report generation; their tool output is authoritative.

## Retained argument and allocation for the four unsplit jobs

This is the full original proof, copied verbatim from baseline.json. It is retained as handoff material so that work is spread without shortening or blurring any argument. The statements of the four new nodes express the obligations; the proofs below remain unclaimed by those unsplit nodes.

### Original step 1 → existing homogeneous-coordinate node and assembly step 1

Use [lem-sfb-topological-homogeneous-cochain-coordinates] for $E=\mathbf Q_\ell$, $J=G$ and the trivial action. The norm axioms give continuous addition and scalar multiplication on $V$, so its topological-vector-space hypotheses hold without completeness. Write $\Psi c=f_c$ and $\Phi F(g_1,\ldots,g_q)=F(1,g_1,g_1g_2,\ldots,g_1\cdots g_q)$. The cited statement gives inverse linear cochain maps, including degree zero, and $\delta\Psi=\Psi d$, $\Phi\delta=d\Phi$. In particular $c$ is a cocycle exactly when $F=\Psi c$ satisfies $\delta F=0$. We will construct finite-evaluation operators on the diagonally $G$-invariant homogeneous functions and then conjugate them by these explicit maps.

### Original step 2 → lem-sfb-ordered-coset-finite-chain-projection

Choose a transversal $D\subset G$ for the finitely many right cosets $H\backslash G$, including $1$. Write $x=\rho(x)s(x)$ uniquely with $\rho(x)\in H$ and $s(x)\in D$. Each coset $Hs$ is clopen: it is open by translation, and its complement is a union of other open cosets. On $Hs$, $\rho(x)=xs^{-1}$ is continuous into $H$ with its subspace topology; these open pieces show that $\rho:G\to H$ is continuous. Uniqueness gives $\rho(hx)=h\rho(x)$ for $h\in H$. The transversal is fixed once, independently of $V$. No normality of $H$ is assumed.

### Original step 3 → lem-sfb-ordered-coset-finite-chain-projection and lem-sfb-equivariant-prefix-finite-chain-homotopy

For a set $Y$ let $B_q(Y)$ be the free abelian group with specified basis $[y_0,\ldots,y_q]$ (repetitions allowed), and put $B_{-1}(Y)=\mathbf Z[\varnothing]$. This is the basis convention of [def-weil-pbc-free-module]. Define $\partial$ by alternating deletion, including $\partial[y]=[\varnothing]$ and $\partial[\varnothing]=0$. Deleting two distinct positions in opposite orders gives opposite signs, hence $\partial^2=0$. A homogeneous function $F$ extends uniquely by finite sums to $\widehat F:B_n(G)\to V$; then $\delta F=0$ means $\widehat F\partial=0$ on $B_{n+1}(G)$. Left translation acts coordinatewise on all these chains.

### Original step 4 → lem-sfb-ordered-coset-finite-chain-projection

Apply [lem-sfb-ordered-join-partial-contraction] with $r=n+1$ and the separately labelled sets $X_i=Ha_i$. Write $J_q$ for its ordered-color chains and $e_q:J_q\to B_q(G)$ for erasing colors; $\partial e=e\partial$ follows from deletion. For $h\in H$, choose anchors $v_i=ha_i$ and denote the cited operator by $S^h$. Its statement gives $\partial S^h_q+S^h_{q-1}\partial=1$ for $-1\leq q\leq n-1$, its naturality under simultaneous left translation, and a fixed finite integer expansion using only vertex insertions and replacements. In degree $n$, every basis of $J_n$ has exactly one vertex in each color, in order $0,\ldots,n$; thus every tuple in $e_n(J_n)$ is an integer combination of tuples in the specified rectangle.

### Original step 5 → lem-sfb-ordered-coset-finite-chain-projection

Construct $P_q:B_q(G)\to J_q$ through degree $n$. Put $P_{-1}=1$ and $P_0[x]=[(0,\rho(x)a_0)]$, so $\partial P_0=P_{-1}\partial$. For $1\leq q\leq n$, assuming the chain identities below degree $q$, define on each basis tuple $x=[x_0,\ldots,x_q]$
$$z=P_{q-1}(\partial x),\qquad P_q(x)=S^{\rho(x_0)}_{q-1}(z),$$
and extend linearly. The induction hypothesis gives $\partial z=P_{q-2}\partial^2x=0$, using the augmentation identity when $q=1$. Since $q-1\leq n-1$, [lem-sfb-ordered-join-partial-contraction] gives $\partial P_q(x)=z$. Hence $\partial P_q=P_{q-1}\partial$ in all required degrees. The input-dependent anchor is chosen on basis tuples before linear extension; it is not asserted to be a linear function of a general chain.

### Original step 6 → lem-sfb-ordered-coset-finite-chain-projection

Naturality in [lem-sfb-ordered-join-partial-contraction], applied to left translation by $h\in H$, gives $hS^{\rho(x_0)}z=S^{h\rho(x_0)}(hz)$. Together with $\rho(hx_0)=h\rho(x_0)$ this proves inductively $P_q(hx)=hP_q(x)$; the base case is the displayed $P_0$. The finite-expansion clause of that node also proves inductively that $P_q[x_0,\ldots,x_q]$ is a fixed finite integer sum of colored tuples with vertices of the form $\rho(x_j)a_i$. Boundary merely selects subtuples, and the next $S$ inserts or replaces by $\rho(x_0)a_i$. Coefficient lists and coordinate selections depend on the degree and color lists alone. Keep repeated terms rather than combining them, so no equality test on input values enters this expansion.

### Original step 7 → lem-sfb-equivariant-prefix-finite-chain-homotopy

Set $A_q=e_qP_q$ for $-1\leq q\leq n$. These are $H$-equivariant augmented chain maps and $A_{-1}=1$. For $b\in G$, let $C_b$ prefix $b$ to a tuple, with $C_b[\varnothing]=[b]$. Direct deletion gives
$$\partial[b,y_0,\ldots,y_q]=[y_0,\ldots,y_q]-C_b\partial[y_0,\ldots,y_q],$$
so $\partial C_b+C_b\partial=1$, also in degree $-1$ since $\partial[b]=[\varnothing]$. Coordinatewise translation gives $hC_bz=C_{hb}(hz)$.

### Original step 8 → lem-sfb-equivariant-prefix-finite-chain-homotopy

Define $Q_{-1}=0$ and, on basis tuples $x=[x_0,\ldots,x_q]$, recursively for $0\leq q\leq n$ put
$$Z_q(x)=x-A_qx-Q_{q-1}\partial x,\qquad Q_q(x)=C_{x_0}Z_q(x),$$
extending linearly. The augmentation of $Z_0$ is $1-1=0$. For $q\geq1$, the previous-degree identity and the chain identity for $A$ give
$$\partial Z_q=(1-A_{q-1})\partial x-(1-A_{q-1}-Q_{q-2}\partial)\partial x=0.$$
The prefix identity therefore gives $\partial Q_q(x)=Z_q(x)$. This proves by induction
$$1-A_q=\partial Q_q+Q_{q-1}\partial\qquad(0\leq q\leq n).$$
Both the base and the step have been verified, rather than invoking an unspecified resolution-comparison theorem.

### Original step 9 → lem-sfb-equivariant-prefix-finite-chain-homotopy

Induction in this same recursion proves $H$-equivariance of $Q$: $Z_q(hx)=hZ_q(x)$ and $C_{hx_0}(hZ_q(x))=hQ_q(x)$. Its base is $Q_{-1}=0$. Likewise the finite expansion for $A$, together with deletion, subtraction and prefixing, proves that each $Q_q[x_0,\ldots,x_q]$ has a fixed finite integer expansion with every vertex either $x_j$ or $\rho(x_j)a_i$. These vertex maps are continuous by step 2 and multiplication in $G$. Thus evaluation of any continuous $F$ on $Q_q$ or $A_q$ is continuous. All the recursions are integral and independent of coefficients.

### Original step 10 → lem-sfb-coset-averaged-homogeneous-residual

For any degree-$n$ homogeneous $G$-invariant function $F$, define $H$-invariant functions
$$UF(x_0,\ldots,x_{n-1})=\widehat F(Q_{n-1}[x_0,\ldots,x_{n-1}]),\quad WF(y_0,\ldots,y_n)=\widehat F(A_n[y_0,\ldots,y_n]).$$
They are linear in $F$ and continuous by step 9. If $\delta F=0$, applying $\widehat F$ to step 8 in degree $n$ gives $F=\delta(UF)+WF$, because $\widehat F\partial Q_n=0$. Applying $\delta$ gives $\delta(WF)=0$, since $\delta^2=0$ by the same deletion cancellation as for $\partial^2$. If $F$ vanishes on $Ha_0\times\cdots\times Ha_n$, then $WF=0$ by the degree-$n$ description of $eJ_n$ in step 4. These are identities on $G$-tuples, before passing to cohomology.

### Original step 11 → lem-sfb-coset-averaged-homogeneous-residual

For an $H$-invariant degree-$q$ homogeneous function $L$ on $G^{q+1}$ define
$$(\mathcal M_qL)(x)=m^{-1}\sum_{s\in D}L(sx_0,\ldots,sx_q).$$
For $g\in G$, write $sg=h u$ with $h\in H$ and $u\in D$. Right multiplication permutes $H\backslash G$, so $s\mapsto u$ is a permutation, and $L(sgx)=L(hux)=L(ux)$. Thus $\mathcal M_qL$ is $G$-invariant, without normality of $H$. Deletion commutes with each simultaneous translation, so $\delta\mathcal M=\mathcal M\delta$. On $G$-invariant functions $\mathcal M F=F$. Therefore for cocycles step 10 gives
$$F=\delta(\mathcal M_{n-1}UF)+\mathcal M_nWF,\qquad\delta(\mathcal M_nWF)=0.$$
The residual is zero whenever $F$ vanishes on the rectangle. The finite sum also preserves continuity and linearity.

### Original step 12 → assembly step 4; lem-sfb-coset-averaged-homogeneous-residual (denominators) and lem-sfb-nonarchimedean-finite-evaluation-calculus (evaluation composition)

Define on all of $C^n(G,V)$
$$T=\Phi_{n-1}\mathcal M_{n-1}U\Psi_n,\qquad R=\Phi_n\mathcal M_nW\Psi_n.$$
The cochain identities of [lem-sfb-topological-homogeneous-cochain-coordinates] and step 11 give $c=d(Tc)+Rc$ and $d(Rc)=0$ for every cocycle. Its inverse formula is exactly $\Psi_nc=f_c$ for the trivial action, so rectangle vanishing gives $Rc=0$. To obtain the finite evaluation formulas on the full cochain spaces, expand $Q_{n-1},A_n$ as in steps 6 and 9, translate each tuple by each $s\in D$, insert the cumulative-product tuple from $\Phi$, and replace each final homogeneous tuple $(b_0,\ldots,b_n)$ by $(b_0^{-1}b_1,\ldots,b_{n-1}^{-1}b_n)$ from $\Psi$. These are continuous maps of exactly the domains and codomains in the item, also when $n-1=0$. All coefficients are integers divided by $m$, and every choice was independent of $V$.

### Original step 13 → lem-sfb-nonarchimedean-finite-evaluation-calculus

Every integer $k$ has $|k|_\ell\leq1$, while $|m|_\ell=1$ because $m$ is prime to $\ell$, by [def-weil-l-adic-numbers]. Hence every coefficient $k/m$ in the expansions has absolute value at most one. The ultrametric inequality now gives pointwise $\|(Tc)(x)\|\leq\sup_z\|c(z)\|$ and $\|(Rc)(y)\|\leq\sup_z\|c(z)\|$. These suprema are finite: the continuous real function $\|c(-)\|$ has compact image on the compact domain $G^n$. Taking suprema proves both operator bounds. Each value of each operator is a finite $\mathbf Q_\ell$-linear combination of values of $c$, so every linear coefficient subspace is preserved, whether or not it is closed. In particular the formulas never require a limit in $V$.

### Original step 14 → lem-sfb-nonarchimedean-finite-evaluation-calculus and assembly step 5 (bottom degree)

Let $S$ be any profinite parameter space and $c:S\times G^n\to V$ continuous. Apply the same fixed formulas to the group variables only: for example $(Tc)(s,x)=\sum_j\alpha_j c(s,\psi_j(x))$. Each map $(s,x)\mapsto(s,\psi_j(x))$ is continuous, and finite addition and fixed scalar multiplication are continuous in $V$. This proves continuity of the resulting families, and the cochain and rectangle identities hold separately at every parameter. If $S$ is empty there is the unique family. For $n=1$, $Q_0[x]=[x,x]-[x,\rho(x)a_0]$ and the degree-$1$ homotopy identity still applies; after averaging $UF$ is a $G$-invariant function of one variable and hence constant, so its inhomogeneous differential is the stipulated $d^0=0$. Thus the bottom degree and incomplete or zero coefficient spaces are included.
