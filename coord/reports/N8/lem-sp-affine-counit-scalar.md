# Repair: lem-sp-affine-counit-scalar

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-affine-counit-scalar.json — unchanged statement; four-step, 2037-character assembly replacing the returned 7517-character proof.
- dag/nodes/sec-smooth-purity/lem-sp-affine-line-scalar-mates.json — statement, unsplit; no Mathlib match. Standard affine-line composite square, with actual open evaluation and normalized projective-line counits.
- dag/nodes/sec-smooth-purity/lem-sp-ordered-tate-scalar-normalization.json — statement, unsplit; no Mathlib match. Equality of the iterated and direct right comparison under the specified normal forms, in the derived category.
- dag/nodes/sec-smooth-purity/lem-sp-finite-tower-scalar-mates.json — statement, unsplit; no Mathlib match. Finite ordered induction for mates and actual composite counits, with explicit recursions and identity base case.
- dag/nodes/sec-smooth-purity/lem-sp-ordered-compactification-scalar-square.json — statement, unsplit; no Mathlib match. Ordered left coefficient square for an arbitrary specified compactification.
- citations.json — all seven step/node citations have verbatim statement extracts.

All four new nodes have empty proof and proof_deps, null proof_origin, complete blueprint provenance through this item, and recorded leanfinder, loogle, grep and leansearch queries. Their statements range from 1548 to 2651 characters and isolate distinct arguments. There are no new Mathlib leaves.

## Attachments

None. I searched WeilConjectures both for the blueprint tag and for affine/scalar/counit notions. The local Sheaf.Paper.AffineCounitScalar declaration AlgebraicGeometry.Etale.affine_counit_scalar ends in sorry; its auxiliary definition only constructs the transported counit. Neither is a completed proof of the item. The field extension, affine scheme and ordinary module counit search hits do not state the result.

## WANTED

None. The current blueprint source and the supporting DAG statements are present locally. No SGA source was used.

## What was wrong and what changed

The return's single numbered requirement is a re-split to spread 7517 characters across at least two independent tasks, leaving at most 3000 characters in the item. I added four tasks, with the original detailed argument assigned below to the corresponding future worker. No clause or hypothesis of the item changed. In particular, I retained arbitrary finite coefficient maps, derived tensor, the actual normalized ordered counit, the specified compactification arrow, and d=0.

On entry this sandbox contained only dispatcher marker files: no node, report, citations or search log was retained. The prescribed initial dry run exited with “no node files”. I copied the current read-only repository item, whose eight proof steps and lengths are precisely those in the return. baseline-item.json retains that entire file. The delivery tool rebases these split-owned edits against the current meeting-point branch. There was no older sandbox report or logged search result to discard or redo.

The original proof's domain check and final cancellation remain in the item. Original steps 2–3, 4, 5–6 and 7 become four separately stated results. Thus no new node restates the parent, and no single node holds the whole old proof. The induction node assumes the line mate identities and does not identify either normal form or any fixed compactification; the two normalization nodes prove no counit identity. The line node treats just one open/projective composition. Every original proof step is reproduced verbatim below for a future worker; the new nodes themselves contain no proof sketch or steps.

## Unfinished work

The four new nodes are deliberately unsplit tasks for later workers. No Lean was written and no compiler, Lake or local check_dag/review_split/preflight was run. The only requested remaining action is the server-side dry-run/preflight followed by delivery.

## Review by N8

I read the source at literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, especially Charts, together with dag/units/sk-lem-sp-reduction.json and the smooth-purity chapter record. Charts explicitly builds the counit from open summation and iterated normalized projective-line integration and says its coefficient comparison is the canonical twisted pullback. The four new nodes separate those computations without changing this route. For the line node I reread the actual statements of lem-sp-etale-sum-counit-scalar and lem-sp-p1-counit-scalar; both give mates of the inverse left coefficient map on finite-Tor inputs, with the actual specified counits. I checked that the open chart sum extension equals j_! by the definition of etale sum extension. I read clause 2 of lem-weil-pbc-mate-pasting and the transpose characterization in def-weil-pbc-adjunction-mate: the orientation is a^u = mate((b^u)^-1), and the counit is w composed with Q(v V). This is the source of old steps 2–3 assigned to the first new task.

For the right-normalization node I read lem-asd-etale-finite-twist-pullback and lem-asd-finite-etale-twist-line, not just their titles. They give pullback compatibility with tensor/composition and flatness of each finite Tate line. I read the K-flat and flat-term computation and simultaneous naturality asserted by lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The statement of the new task is the derived morphism equation I_B A_d = a_d T(I_A). The exact balanced-tensor computation and even-shift check of old step 4 are preserved in its assigned argument below; they are not presumed from the mere existence of an endpoint isomorphism. The line comparisons used in this equation are defined explicitly; the new statement makes no reference to the proof of the parent.

For the finite-tower node I checked the full statement of def-weil-pbc-composite-adjunction, including its identity case and its actual composite counit, against Stacks Tag 0DV0, categories.tex lemma-compose-counits, lines 3576 onward. I read Mathlib CategoryTheory.Adjunction.Mates.mateEquiv_hcomp at line 209, mateEquiv_counit at line 123, and Adjunction.comp_counit_app in Basic.lean line 580. These are binary pasting and counit formulas; none states the finite dependent tower with recursively pinned A_r, B_r and E_r. The new task retains the explicit induction starting at the identity and the successor formulas of old steps 5–6. It can be undertaken independently using the already existing binary mate-pasting node. It asserts no geometric or compactification normalization.

For the compactification node I read the full final paragraphs of lem-sp-et-proet-coefficient-compatibility, not just its site-comparison clause. Its statement explicitly supplies both refinement and composition equations, their common-refinement version, identity normalization and associativity. I read lem-amb-etale-compact-comparisons for the actual coherent left comparison C. The new node asks for their ordered finite iteration, for the specified c itself. Old step 7's argument and its domain qualifications are retained below, so an arbitrary isomorphism between left endpoints cannot substitute for C.

I then checked every parent step against its cited statements. Step 1 cites def-amb-affine-trace-tower for the actual tower, compactifications and invertibility at every stage, and lem-sp-etale-ctf-chart-domain for coefficient extension, compact support and right pullback/twist/shift preservation. Thus all uses of bounded-below comparisons are on the bounded constructible finite-Tor inputs actually allowed; no preservation of all D+ under a nonflat scalar map is invoked. Step 2 takes the precise inverse-mate assertion of the line node and applies the finite-tower node with categories C_(r,R)=D^b_ctf(X_r,R); its counit equation is exactly the one required. Step 3 uses the exact equations in the two normalization statements; their statements name the actual right comparison and fixed compactification arrow. Step 4 cites lem-amb-affine-space-top-trace only for the prescribed ordered adjunction and canonical left identification: the transported counit is E_R followed after C_R^-1. Its remaining calculation is naturality of C_B, substitution, and cancellation of an isomorphism, written explicitly. citations.json quotes the relevant statement content for all seven uses. All proof dependencies are precisely the union of these uses, with no appeal to the internal proof of a cited node.

I tested the new statements with d=0 and d=1, K=0, the empty base, the identity coefficient map, N=1 (zero coefficients), and the nonflat map Z/ell^2 -> Z/ell. The tower recursions are identity maps at zero length, and a nonidentity compactification of 1_S uses its canonical comparison rather than an unjustified literal identity. At length one the generic tower gives the line mate equation. At length two the recurrence has F_(r+1)=F_r L_r and G_(r+1)=W_r G_r, hence E_(r+1)=E_r F_r(e_r G_r) with the directions shown. All Tate reassociations preserve the coordinate order; the degree-zero tensor maps and even shifts introduce no extra sign. Finite Tor amplitude, rather than finite projective dimension of B/A, keeps coefficient extension bounded. These checks exposed no statement dispute. I corrected no source statement, and retained all maintainer-owned fields of the parent unchanged.

I checked B–E of delivery-errors.md: self-contained TeX statements with all objects introduced; explicit notion dependencies; no proofs in unsplit nodes; real logged searches with second semantic phrasings and exact tool/query strings; no duplicate or circular use; correct coefficient categories and input domains; and no hidden non-elementary step in the remaining cancellation. The parent has no step longer than 2000 characters. The new arguments are separately scoped and sized, not clauses relabelled as the whole assertion. The current source does not require a change to the unit or chapter record.

## Not duplicates

lem-sp-affine-line-scalar-mates vs lem-sp-etale-sum-counit-scalar: the existing statement is the etale sum counit alone; the new one composes it with the normalized projective-line adjunction and fixes the affine-line coefficient arrow.
lem-sp-affine-line-scalar-mates vs lem-sp-p1-counit-scalar: the existing statement is the proper projective-line counit alone; the new one includes the open chart and its composite counit.
lem-sp-affine-line-scalar-mates vs lem-amb-affine-trace-line-counit-base-change: the existing assertion changes the scheme base with fixed coefficient ring; the new assertion changes finite coefficient rings with fixed scheme base.
lem-sp-ordered-tate-scalar-normalization vs def-pur-affine-space-comparison: the existing node defines a pro-etale purity comparison with exceptional inverse image; the new one states equality of ordinary-etale scalar maps for the ordered right adjunction, without exceptional inverse image.
lem-sp-ordered-tate-scalar-normalization vs lem-asd-etale-finite-twist-pullback: the existing statement gives Tate pullback with a single coefficient ring, not the finite coefficient-change square for the iterated shifted right functor.
lem-sp-ordered-tate-scalar-normalization vs lem-sp-signed-tate-coefficient-exponent-normalization: the existing statement concerns pro-etale Tate lines, signed exponents and exponent change, not the ordinary-etale derived right functor, pullback tower and even shifts.
lem-sp-ordered-tate-scalar-normalization vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node gives structural monoidality and binary pullback compositors for arbitrary ringed topoi; the new equation compares two explicitly named finite scalar maps through the full ordered shifted Tate tower.
lem-sp-ordered-tate-scalar-normalization vs lem-trf-pullback-coefficient-iterate-coherence: the existing statement iterates endomorphisms with a fixed coefficient ring on the pro-etale site; the new statement concerns a chain of affine-line projections and a coefficient ring change on the ordinary-etale site.
lem-sp-finite-tower-scalar-mates vs lem-weil-pbc-mate-pasting: binary mate pasting is the existing result; the new task proves its finite dependent-tower recursion with pinned composite counits and the zero-length normalization.
lem-sp-finite-tower-scalar-mates vs lem-amb-affine-trace-tower-counit-base-change: the existing node concerns geometric base-change exchanges; the new node is a categorical finite sequence of scalar functors and inverse-mate squares.
lem-sp-ordered-compactification-scalar-square vs lem-sp-et-proet-coefficient-compatibility: the existing statement gives binary composition/refinement laws; the new task carries out their finite ordered affine-tower iteration, including the actual arbitrary c and zero-length comparison.
lem-sp-ordered-compactification-scalar-square vs lem-sp-chart-left-scalar-normalization: the existing statement pastes an etale chart e with an already formed affine-space functor; the new one compares the coordinate tower itself with an arbitrary compactification of p_d. It cannot be obtained by e=identity since the existing node already starts with F_d, not the ordered composite.
lem-sp-ordered-compactification-scalar-square vs lem-amb-etale-compact-comparisons: the existing statement is single-ring compactification coherence; the new one is the two-ring coefficient square for its ordered iteration.

Searches of the whole DAG and tools/blueprint_refs.py search for affine counit, mate pasting, coefficient comparison, ordered coefficient, Tate tensor, affine line, and compactification refinement found these nearby nodes but no existing statement of the new tasks. No new source carries a Stacks tag shared with another node: the geometric source is the current blueprint Charts paragraph. The categorical formulas were also checked directly against Tag 0DV0 as supporting literature, not claimed as a new copy of its binary theorem.

## Original argument preserved, with its new owners

The following are the returned proof's eight steps, verbatim. The source for each is its source field in baseline-item.json; all are the current main-20261015 exceptional-reduction Charts paragraph with the more precise original place recorded there. This is retained work for each new task's future worker, outside the statement-only node files.

### Original step 1 — Parent assembly step 1 (domain check)

Use the coordinate tower $X_0=S$, $X_{r+1}=\mathbf A^1_{X_r}$, $u_r:X_{r+1}\to X_r$, $p_{r+1}=p_ru_r$, and its standard compactifications $j_r:X_{r+1}\hookrightarrow P_r=\mathbf P^1_{X_r}$, $q_r:P_r\to X_r$ of [def-amb-affine-trace-tower]. All these schemes and maps are in the standing setting: affine and projective spaces and their standard open charts over a separated finite-type $k$-scheme remain separated and finite type. The integer $N$ is invertible since $\ell\ne p$. By [lem-sp-etale-ctf-chart-domain], every coefficient extension and every pullback followed by a finite positive Tate twist and shift used below preserves $D^b_{ctf}$; the compact-support functors also preserve it. Consequently each successive right-adjoint input, not just the original $K$, lies in the domains of the two scalar-counit lemmas below. In particular all inputs to bounded-below compact-support comparisons and their coefficient extensions are bounded below. No assertion that tensoring with $B$ preserves all of $D^+$ is needed.

Existing cited statements: def-amb-affine-trace-tower, lem-sp-etale-ctf-chart-domain.

### Original step 2 — lem-sp-affine-line-scalar-mates

Fix one stage with base $T=X_r$. Write $J_R=Dj_!$, $H_R=j^*$, $Q_R=Rq_{*,R}$, $V_R=q^*(-)(1)[2]$, with counits $v_R:J_RH_R\to1$ and $w_R:Q_RV_R\to1$. For an open immersion the sum extension is the usual extension by zero, by [def-weil-pbc-etale-sum-extension]. Apply [lem-sp-etale-sum-counit-scalar] to $j$ and [lem-sp-p1-counit-scalar] to $q$. If $s:T_PJ_A\xrightarrow{\sim}J_BT_{\mathbf A^1_T}$ and $b:T_TQ_A\xrightarrow{\sim}Q_BT_P$ are their specified coefficient maps, the canonical right comparisons $h:T_{\mathbf A^1_T}H_A\xrightarrow{\sim}H_BT_P$ and $a:T_PV_A\xrightarrow{\sim}V_BT_T$ are respectively the mates of $s^{-1}$ and $b^{-1}$. These statements concern the actual evaluation and normalized projective-line counits, at every finite-Tor input; no replacement of either adjunction by an arbitrary isomorphic one is made.

Existing cited statements: def-weil-pbc-etale-sum-extension, lem-sp-etale-sum-counit-scalar, lem-sp-p1-counit-scalar.

### Original step 3 — lem-sp-affine-line-scalar-mates

Compose $J_R\dashv H_R$ with $Q_R\dashv V_R$. Its left functor is $L_R=Q_RJ_R$, its right functor is $W_R=H_RV_R$, and its counit is $e_R=w_R\circ Q_R(v_RV_R)$ by [def-weil-pbc-composite-adjunction]. Put $b^u=Q_B(s)\circ bJ_A$ and $a^u=H_B(a)\circ hV_A$. Apply clause 2 of [lem-weil-pbc-mate-pasting] to the inverse squares $s^{-1}$ and $b^{-1}$. Their pasted square is $(b^u)^{-1}$, and its mate is exactly $a^u$. The transpose characterization in [def-weil-pbc-adjunction-mate] therefore gives
$$e_{B,T_TK}\circ L_B(a^u_K)\circ b^u(W_AK)=T_T(e_{A,K}).$$
This is the scalar-counit equation for the standard affine-line compactification. The left map here is the proper coefficient comparison followed by open extension's tensor comparison, exactly the chosen-compactification definition of the coefficient map in [lem-sp-et-proet-coefficient-compatibility].

Existing cited statements: def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting, def-weil-pbc-adjunction-mate, lem-sp-et-proet-coefficient-compatibility.

### Original step 4 — lem-sp-ordered-tate-scalar-normalization

Under the ordered right-functor normal forms of [lem-amb-affine-space-top-trace], the pasted right comparisons are the canonical pullback/tensor, Tate and shift comparisons in the question. Here is the normalization check. Inverse image takes each Tate factor to the same factor upstairs, compatibly with tensor and composition, by [lem-asd-etale-finite-twist-pullback]. Use the K-flat, flat-term representatives and the natural tensor/pullback isomorphism of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Tate factors are flat by [lem-asd-finite-etale-twist-line], so they require no further derived replacements. On each local generator of the Tate factors every order of the displayed coefficient reassociations sends $((x\otimes z_1\otimes\cdots\otimes z_r)\otimes b)$ to $(x\otimes b)\otimes\bar z_1\otimes\cdots\otimes\bar z_r$, where $\bar z_i=z_i\otimes1$. Both parenthesizations multiply coefficients by the same balanced rule $(x\otimes a)\otimes b\mapsto x\otimes\varphi(a)b$. Thus the maps agree termwise and hence after descent to the derived category. Shifts commute with this degree-zero map; all accumulated shifts are even, so their reassociations introduce no extra sign. For one coordinate this identifies $a^u$ with the named affine-line comparison.

Existing cited statements: lem-amb-affine-space-top-trace, lem-asd-etale-finite-twist-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-asd-finite-etale-twist-line.

### Original step 5 — lem-sp-finite-tower-scalar-mates

Induct on $r$ before identifying the left functor with a compactification. Let $\mathcal F_{r,R}$ be the ordered composite of the line functors above and $\mathcal G_{r,R}$ its reverse ordered right composite. Let $B_r:T_S\mathcal F_{r,A}\to\mathcal F_{r,B}T_{X_r}$ be the ordered composite of the $b^u$ and $A_r:T_{X_r}\mathcal G_{r,A}\to\mathcal G_{r,B}T_S$ the ordered composite of the $a^u$. The induction claim is that $A_r$ is the mate of $B_r^{-1}$ and
$$\mathcal E_{r,B}\,\mathcal F_{r,B}(A_r)\,B_r\mathcal G_{r,A}=T_S(\mathcal E_{r,A}),$$
where $\mathcal E_r$ is the actual composite counit. For $r=0$, both functors, both comparisons, and the counit are identities. The identity-adjunction formula of [def-weil-pbc-composite-adjunction] proves the claim, and it includes $K=0$ and the empty base.

Existing cited statements: def-weil-pbc-composite-adjunction.

### Original step 6 — lem-sp-finite-tower-scalar-mates

For the successor, $\mathcal F_{r+1,R}=\mathcal F_{r,R}L_{u_r,R}$ and $\mathcal G_{r+1,R}=W_{u_r,R}\mathcal G_{r,R}$. The ordered comparisons are
$$B_{r+1}=\mathcal F_{r,B}(b^{u_r})\circ B_rL_{u_r,A},\qquad A_{r+1}=W_{u_r,B}(A_r)\circ a^{u_r}\mathcal G_{r,A}.$$
By the induction hypothesis and the affine-line calculation in step 3, clause 2 of [lem-weil-pbc-mate-pasting] says exactly that $A_{r+1}$ is the mate of $B_{r+1}^{-1}$. Its transpose equation [def-weil-pbc-adjunction-mate] is the induction claim in degree $r+1$. The actual counit used here is $\mathcal E_{r+1,R}=\mathcal E_{r,R}\circ\mathcal F_{r,R}(e_{u_r,R}\mathcal G_{r,R})$, as prescribed by [def-weil-pbc-composite-adjunction]. Hence the calculation tracks the specified counit at every step. Step 4 identifies $A_{r+1}$ with the canonical $a_{r+1}$ after the right normal form, not merely with some isomorphism of its endpoints. Induction proves the equation in every dimension.

Existing cited statements: lem-weil-pbc-mate-pasting, def-weil-pbc-adjunction-mate, def-weil-pbc-composite-adjunction.

### Original step 7 — lem-sp-ordered-compactification-scalar-square

Fix the compactification $c$ specified in the question and write $C_{d,R}:\mathcal F_{d,R}\xrightarrow{\sim}F^c_{d,R}$ for its comparison with the ordered composite. These are the canonical coherent composition/refinement maps of [lem-amb-etale-compact-comparisons]. The composition and refinement equalities of [lem-sp-et-proet-coefficient-compatibility], applied successively, give on our input class
$$\beta_d\circ T_S(C_{d,A})=(C_{d,B}T_{X_d})\circ B_d.$$
The identity/composition normalization gives this also for $d=0$. This step uses the refinement equality as well as the composition equality: if $c$ differs from the compactification used to form a composition map, the common-refinement comparison contributes precisely $C_{d,R}$ on both sides. Thus $\beta_d$ is the coefficient map for $c$ itself. Domain preservation in step 1 ensures that every equality is applied to the bounded finite-Tor inputs stipulated in its statement.

Existing cited statements: lem-amb-etale-compact-comparisons, lem-sp-et-proet-coefficient-compatibility.

### Original step 8 — Parent assembly step 4 (cancellation)

After the right normal-form identification, the counit on $F^c_{d,R}$ is $\epsilon_{d,R}=\mathcal E_{d,R}\circ C_{d,R}(G_{d,R})^{-1}$, by the prescribed identification in [lem-amb-affine-space-top-trace]. Precompose the desired equation with the isomorphism $T_S(C_{d,A}(G_{d,A}K))$. Substitute the equality in step 7 and then naturality of $C_{d,B}$ at $a_{d,K}$; its left side becomes
$$\mathcal E_{d,B,T_SK}\,\mathcal F_{d,B}(a_{d,K})\,B_d(G_{d,A}K).$$
By steps 5--6 this equals $T_S(\mathcal E_{d,A,K})$, which is also the right side after that precomposition. Cancel the isomorphism. This proves exactly the stated equality for $\beta_d^c$, including the identity adjunction in dimension zero. The proof never assumes flatness or finite projective dimension of $B$ over $A$; coefficient tensor products throughout are derived.

Existing cited statements: lem-amb-affine-space-top-trace.
