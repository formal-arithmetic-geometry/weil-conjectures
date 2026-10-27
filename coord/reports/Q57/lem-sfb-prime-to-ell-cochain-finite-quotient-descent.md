# Stage-1 re-split repair: Q57

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-cochain-finite-quotient-descent.json`: unchanged statement, seven-step assembly, 2885 proof-text characters.
- `lem-sfb-scalar-cochain-averaging-primitives.json`: statement, unsplit; finite-sum and complete-scalar averaging primitives with signs, parameters and bounds; no Mathlib match.
- `lem-sfb-metrizable-cocycle-finite-field-components.json`: statement, unsplit; metric quotient descent and pointwise finite scalar decomposition; no Mathlib match.
- `lem-sfb-metrizable-rectangle-certificate-selectors.json`: statement, unsplit; countable closed certificate cover and eventually stable selectors; no Mathlib match.
- `lem-sfb-rectangle-corrected-pointwise-finite-primitives.json`: statement, unsplit; explicit correction under independent operator hypotheses, with uniform bounds and pointwise finiteness; no Mathlib match.
- `lem-sfb-pointwise-finite-ultrametric-cochain-series.json`: statement, unsplit; uniform summation with values in the original incomplete field and compatibility with the cochain differential; no Mathlib match.
- `citations.json`: full verbatim statements for every cited node in every parent step. Search queries and results are retained in `searches.jsonl` and `search-*.txt` in the sandbox.

All five new node files are in the item's chapter directory. Each has empty proof and proof_deps, null proof_origin and mathlib_match, status unsplit, and the item's chapter/unit. No Lean file, repository file, launcher file or compiler output was written. No agents were started.

## Attachments

None. I searched the live project's WeilConjectures tree by the exact blueprint tag and by cochain/finite-quotient/prime-to-ell terminology, and also read the corresponding Sheaf module. Its theorem `Profinite.ContinuousScalarCochains.prime_to_ell_cochain_finite_quotient_descent` at line 165 has `sorry` at line 173. The existing concrete definitions do not prove the comparison. I also searched both project roots for the new statements' concepts; the rectangle replacement module supplies an existing input, not any new conclusion here.

## WANTED

WANTED: an exact norm-topological reference for parametrized scalar cochain averaging with nonarchimedean norm bound, for lem-sfb-scalar-cochain-averaging-primitives.

WANTED: an exact reference for metrizable cocycle quotient descent together with contractive finite-field components in an algebraic ell-adic closure, for lem-sfb-metrizable-cocycle-finite-field-components.

WANTED: an exact reference for closed rectangle certificates and pointwise eventually stable locally constant selectors, for lem-sfb-metrizable-rectangle-certificate-selectors.

WANTED: an exact reference for the pointwise-finite primitive correction from coefficient-independent finite-evaluation operators, for lem-sfb-rectangle-corrected-pointwise-finite-primitives.

WANTED: an exact reference for uniform ultrametric cochain summation with pointwise finite values in an incomplete coefficient field, for lem-sfb-pointwise-finite-ultrametric-cochain-series.

These are agent-formulated auxiliary results. The source paragraph is geometric motivation, not a claimed analytic reference. Existing Baire and completion results remain available and are distinguished below; no SGA source is used.

## What was wrong and the repair

The 2026-10-21 human re-split decision returned the 9075-character, twelve-step proof as too much work for one node. The repair requests at least three comparable independent statement-only nodes, a parent assembly of at most 3000 characters, an unchanged parent statement, and retention of every previous argument. This delivery has five new nodes, each carrying a distinct argument; the longest new statement is 2532 characters, the other statements are 1531–1800 characters. None states a quasi-isomorphism or the whole algebraic-closure acyclicity conclusion.

The sandbox initially contained only dispatcher marker files, not the reported earlier split or report. I copied the current repository item without a git command, read its accepted O4 report, and preserved both as `returned-parent.json` and `returned-report-O4.md` in the sandbox. The repository item contains exactly the twelve proof lengths named by the return. There was therefore no existing sandbox split/report to dry-run before this repair. Existing item searches and mathematical metadata are retained; I did not invent a replacement search history. The delivery tool applies only split-owned fields to the current server baseline, preserving subsequent Lean and review metadata.

The work allocation is explicit:

| Old steps | Owner after repair | Argument retained |
| --- | --- | --- |
| 1 | Parent step 1, unchanged | coface cancellation, common finite quotient, scalar linearity, degree zero |
| 2–3 | scalar-cochain-averaging-primitives | signed finite averaging, degree-one case, complete-field integration, unrestricted parameter continuity and norm bounds |
| 4–5 | metrizable-cocycle-finite-field-components | quotient descent, cocycle detection by surjectivity, finite-field projections, finite epsilon-net argument, telescoping and pointwise eventual zero |
| 6–7 | metrizable-rectangle-certificate-selectors | fibrewise Baire, countability of rectangles, closed parameter certificates, clopen partition approximations and stabilization of the least valid certificate |
| 8–9 | rectangle-corrected-pointwise-finite-primitives | finite clopen gluing of the correction, residual equation, bound one, entire-cochain residual vanishing, finitely many fixed evaluations |
| 10 | pointwise-finite-ultrametric-cochain-series | completion, ultrametric tail estimate, uniform limit and continuity, original-field values and passage of the finite differential through the limit |
| 11–12 | Parent steps 6–7 | exact sheafification, inherited module actions, identity in degree zero, localization and edge cases |

The complete old proof is copied verbatim in the takeover appendix below. The five statements expose all hypotheses and conclusions needed to reproduce those arguments, rather than omitting details to shorten the parent. The parent retains the first, eleventh and twelfth arguments, with only step-number references updated. The analytic lemmas are delivered unsplit so five workers can start independently. The correction node assumes the averaging and replacement operators explicitly, rather than moving their existence into itself; the series node assumes the pointwise-finite primitives rather than asserting their existence. The certificate node does not assume a cocycle and the components node does not assert a primitive. This repairs the work-distribution problem without reviving the older whole-clause descent child.

## Landing refusal repair and current-DAG review (2026-10-22)

The return asks to rebase onto the current DAG, re-read changed citations, adjust the split and push again; the reader had approved the mathematics. I resumed the retained sandbox rather than recreating the split or rerunning its recorded searches. No delivery process was still running. The required first dry run completed with `OK (not pushed)` at `1645d5878c0`; it rebuilt this delivery on the current server baseline and passed server preflight.

I compared the complete current repository item with `returned-parent.json`: they are identical, including the statement, all twelve old proof steps, dependencies and Lean metadata. The released stage-1 repair note still expressly requires this re-split despite the old passing review. The retained sandbox changes only proof, proof dependencies, proof origin and split report on the parent; its five new ids are absent from the current repository. Thus the five-node repair remains applicable. The delivery tool overlays split-owned fields onto current origin/sheaf-dag and preserves current maintainer and Lean fields.

I re-opened all ten cited statements against the current DAG/overlay and checked every verbatim quote in citations.json. Step 2 still obtains finite averaging and complete-scalar contractions from the averaging statement; the two finite-extension statements supply exactly completeness and the extended nonarchimedean norm for each F_i. Step 3 obtains surjective metrizable quotient maps, cocycle components and their norm decay from the components statement, and the same increasing fields satisfy the certificate statement's closed finite-field cover hypothesis. Step 4 uses the replacement statement with H_j open normal and [G:H_j] prime to ell; its finite evaluation formulas, residual identity, parameter continuity and bound one give precisely the correction statement's operator hypotheses. Step 2 provides its F_i-linear contractions. Step 5 uses the correction statement's pointwise eventual zero and norm decay with the components statement's telescoping identity in the series statement, so the sum is continuous into the original Omega. The correction still kills the entire residual before using finitely many evaluations; no completeness of Omega was added. Step 6 uses the current exact-sheafification statement with constant ring Z on underlying abelian presheaves, then retains the sectionwise module actions. Step 7 uses the derived-category statement's localization at quasi-isomorphisms. No cited conclusion became unavailable, so no mathematical change or citation replacement was needed.

I also re-read the main-20261015 direct-images proof paragraph (3): it supplies geometric motivation only, consistent with the retained agent proof origin and WANTED analytic references. The project source search still finds the comparison only in the Sheaf module, whose proof remains sorry; it supplies no attachment. I retained the previous small-case checks and full takeover appendix. This repair adds this explicit current-DAG review and records the rebase audit in split_report; it does not submit the old report unchanged. The final dry run and push below must complete before a DELIVERED answer.

### Current retry: baseline and citation audit

The required initial dry run in this retry exited successfully with `OK (not pushed)` at `e93c8c0062f`. I compared every JSON field of the present read-clone item with the saved returned parent: no field differs. The retained parent differs from that baseline only in proof, proof_deps, proof_origin and split_report. All five child ids are still absent from the present DAG. I opened the complete statement of every current cited node; all ten step/quote pairs in citations.json were verbatim matches. The five-node decomposition and the unchanged parent statement therefore still apply to the current baseline. The delivery command performs the actual rebase onto the current server branch in its temporary worktree.

In this retry I clarified the correction child's existing word “contractions” by writing its norm inequality explicitly: $\|h_i c\|_\infty\leq\|c\|_\infty$. This is the bound used in step 4, already provided by the averaging child in step 2. Together with the bounds on T and R and the ultrametric inequality it gives the claimed bound on b_i. This clarification introduces no new search question; the retained logged searches already concern uniformly small corrected primitives. I refreshed the child's full verbatim citation. No current citation required replacement, no hypothesis on the parent changed, and no former proof argument was dropped. I re-read the corresponding project declaration: it still ends in sorry, so there is no attachment. The final dry run and direct push follow these sandbox edits.

## Not duplicates

lem-sfb-scalar-cochain-averaging-primitives vs lem-sfb-prime-to-ell-complete-scalar-integral: the existing result constructs a bounded invariant functional and its parameter operation; the new statement proves the signed cochain primitive equation, covers finite quotient cochains without complete scalars, and records the degree-one endpoint. It is not the same functional assertion.

lem-sfb-scalar-cochain-averaging-primitives vs lem-sfb-prime-to-ell-cochain-finite-quotient-descent: the new result concerns finite averaging and complete coefficient fields; it does not prove incomplete scalar acyclicity or a sheaf/derived comparison.

lem-sfb-metrizable-cocycle-finite-field-components vs lem-sfb-profinite-metric-function-quotients: the existing node factors a single continuous metric-valued function; it gives neither cocycle descent under nerve faces nor a field filtration, telescoping scalar components, pointwise eventual zero or uniform norm decay.

lem-sfb-metrizable-cocycle-finite-field-components vs lem-sfb-algcl-countable-closed-finite-cover: the cover node constructs increasing fields; the new node concerns a cocycle family, metrizable descent and uniformly small scalar components.

lem-sfb-metrizable-cocycle-finite-field-components vs lem-sfb-norm-one-finite-subfield-projection: a single norm-one projection is input to the new assertion, not the assertion about sequences of compact-parameter cochains.

lem-sfb-metrizable-rectangle-certificate-selectors vs lem-sfb-baire-closed-cover-interior: Baire supplies interior in one group fibre, not a countable cover of the parameter space by rectangle certificates or eventually stable locally constant selectors.

lem-sfb-metrizable-rectangle-certificate-selectors vs lem-sfb-parameter-cochain-completion-boundary-descent: the latter asserts local descent of an already given completed primitive. It contains a related certificate argument inside its proof, but its statement gives no certificate sets or selectors. We do not cite the proof of that node as if it were its statement.

lem-sfb-rectangle-corrected-pointwise-finite-primitives vs lem-sfb-bounded-finite-evaluation-rectangle-replacement: the existing node constructs T and R for one rectangle and arbitrary coefficients; the new node assumes these operators and combines them with scalar components, complete-field primitive maps and an eventually stable parameter selector to prove eventual zero for the corrected primitives.

lem-sfb-rectangle-corrected-pointwise-finite-primitives vs lem-sfb-homogeneous-cocycle-rectangle-detection: the existing result detects a coboundary on one open subgroup; the new statement needs fixed finite evaluation formulas and proves pointwise eventual zero of a sequence of global parameterized primitives.

lem-sfb-pointwise-finite-ultrametric-cochain-series vs lem-wf-dominated-continuous-function-series: the latter assumes a complete coefficient field and a summable real majorant. The new statement allows incomplete coefficients and assumes only norm decay plus pointwise eventual zero; a norm-null real sequence need not be real-summable.

lem-sfb-pointwise-finite-ultrametric-cochain-series vs lem-sfb-normed-field-completion: the completion result constructs the complete field and its isometry; it says nothing about uniform function series or differential compatibility.

The five exact ids were checked for freshness. I searched the whole DAG by averaging/cocycle, finite-field components, pointwise finiteness, eventual zero, closed rectangle cover, least selector and uniform series, inspecting statements rather than just titles. I ran blueprint_refs searches for cochain, cocycle, averaging, rectangle, closed cover, finite subfield, uniform convergence, series and locally constant selector. None is an analytic match. Blueprint ancestry returns null for this inherited chain; each new node carries that exact ancestor, with the item prepended to its inherited via chain and the precise paragraph/argument named in from.place. No new node carries a Stacks tag; the existing tag-0CQN Baire leaf is reused through the future certificate split, not duplicated.

## Mathlib searches

Each new node has five real msearch queries: LeanFinder, Loogle, Mathlib grep, LeanSearch and a second LeanFinder phrasing. Exact queries and digests are recorded in the node and the sandbox log. I read the returned signatures and grep hits. LeanSearch was rate-limited for the correction and series nodes; those two entries are explicitly unavailable. Both have successful LeanFinder, Loogle and grep searches, with two semantic phrasings. Successful zero-hit Loogle queries are not labelled service failures.

Averaging searches found Representation.averageMap, which projects invariants of finite algebraic representations, and real-valued Haar integration requiring a real normed space; neither states these nonarchimedean parameterized cochain primitives. ContinuousCohomology.cocycles and homotopy constructors define cochains or assume supplied homotopy data. Component searches found padic character results, continuous-map norm instances, Hilbert-space orthogonal projections and clopen approximation; none provides the field-valued component sequence and quotient cocycle clauses. Selector searches found LocallyConstant.range_finite and locally finite eventual-equality theorems. The certificate changes are not assumed locally finite, and those results do not produce the least-valid-certificate approximations. Correction hits were Nobeling functions, complex-analytic rectangle primitives, and degree induction in HomComplex, with different objects and hypotheses.

For the series node I inspected Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean (especially the complete-space summability result at lines 94–97) and GroupCompletion.lean (completion range criteria at lines 28–43). They supply useful future inputs, but not a one-line specialization with uniform convergence of parameter families, original-field continuity, the quantitative uniform tail bound and compatibility with the cochain differential. The series node is therefore unsplit, not a false Mathlib leaf. No new Mathlib leaves are claimed.

## Review by Q57

I read the returned twelve-step node and the accepted O4 report, the current main-20261015 six-functors-basics chapter, the inherited unit record, the current unit _section.md and its direct-images.proof.md paragraph (3). The paragraph concerns preservation by proper and open direct images and compactification. It contains none of the five analytic assertions. Accordingly all five sources say that the assertion is agent-formulated, and the parent proof_origin remains agent. I also read the Stacks Baire statement and proof in topology.tex, tag 0CQN (lemma-baire-category-locally-compact, at line 2044), and the relevant Mathlib completion/summability sources described above. I read every node statement used in the parent, including the new five, both finite-extension norm/completeness statements, the rectangle-replacement operator statement, exact sheafification, and the derived-category definition. The full quotations in citations.json are copied from those statements.

Step 1 is retained verbatim and is elementary: each face is continuous and scalar-linear; coface pairs cancel, finite intersections give a common open normal quotient, and degree zero is C(S,F) with d zero. There is no new topological or cohomological black box hidden here.

Step 2 uses the new averaging statement for the actual finite-quotient primitive, not the integral definition alone. The finite-extension completeness node applies to every F_i as well as E because each is finite over Q_ell and carries the restricted extended norm; the absolute-value node supplies ultrametricity and uniqueness. Thus the complete-coefficient clause applies to each F_i but is never applied to Omega. I rechecked the sign: if A is the unsigned sum over the last coordinate, the summed cocycle relation gives dA=(-1)^n m c; multiplying by (-1)^n/m gives db=c. Translation g_n h permutes the finite quotient (or preserves the invariant integral). In degree one d^0=0 forces the cocycle to vanish. Norm one uses the prime-to-ell quotient order, and the parameter clause is part of the new averaging statement.

Step 3 uses exactly the component node's surjective p,q, cocycle z_0, increasing F_i, contractive p_i and components e_i. Surjectivity and q being a homomorphism preserve and detect every face identity; every finite quotient of G is one of K. The certificate statement is applied to the resulting metrizable spaces and the closed field filtration, not to an arbitrary nonmetrizable space. It does not claim A_j is open. Its fields really are closed, by the component statement. The scalar decomposition does not require commuting projections or one finite field containing the image of z. A finite epsilon-net for the compact image lies in one field, which makes approximation by all later projections uniform, while eventual zero is only asserted at each fixed input.

Step 4 uses the existing rectangle statement for its full coefficient-independent finite-evaluation operators, residual equation, cocycle residual, parameter continuity, bound one and rectangle vanishing. The H_j are open normal subgroups; G/H_j is a finite continuous quotient with order prime to ell. The averaging operators from step 2 act only in complete F_i. These are exactly the explicit hypotheses in the new correction statement, whose conclusion gives db_i=e_i, continuous F_i-valued cochains, a uniform norm bound and pointwise eventual zero. I checked finite clopen gluing: at a fixed i only finitely many j occur, all pieces are clopen and the formulas keep s fixed. At fixed s, k_i stabilizes to j(s); once i>N_j both projections fix F_Nj, so R_j e_i(s)=0 as an entire cochain. The remaining T_j uses finitely many fixed evaluations; each e_i value is eventually zero. This is the quantifier argument the parent's old steps 8–9 carried, now an independent task. Merely citing existential rectangle detection would not prove it.

Step 5 applies the series statement to the actual b_i and the identity sum_{i<=N} e_i=p_N z_0. Its original normed field is V=Omega, not the completion. Omega is ultrametric because any pair of its elements belongs to a common finite extension. Norm decay and pointwise eventual zero are both supplied by the correction node. The series result provides an Omega-continuous sum with db=z_0; continuity is not inferred from a completed primitive without checking its values. Pullback along p times q^(n-1) commutes with every face, yielding a primitive on the original S,K. This is elementary functorial substitution after the cited summation result.

Step 6 retains the old sheafification argument, with step references updated. The exact-sheafification node explicitly states objectwise homology of presheaf complexes and H(P#)=H(P)#, so it is applied with constant ring Z to underlying abelian presheaves. No assumption that the condensed ring object has constant sections is made. Objectwise exactness established above gives vanishing positive cohomology. Both degree-zero cohomology objects are A_F and the inclusion is the identity there. Kernels and stable pointwise images carry the module actions; sheafifying the image preserves those actions. Hence the same specified map induces module cohomology isomorphisms, not an arbitrary unrelated abstract isomorphism.

Step 7 retains the derived-category localization and edge cases. The cited derived definition explicitly localizes at quasi-isomorphisms. Extension by zero to negative degrees preserves the calculation. The chosen inclusion therefore becomes invertible, as required. We did not identify the complexes with derived invariants, change their topologies, or add a completeness hypothesis to Omega.

For the five new statements I checked self-contained objects and hypotheses (B2–B3): profinite spaces/groups, cocycle differential including d^0, scalar norms and finite fields are introduced inline with their relevant definition nodes. New nodes have no proof or proof sketch in the statement (B1); their formulas specify operations, hypotheses and conclusions. The new correction statement deliberately assumes the separate operator properties, rather than obtaining unexplained data from another node's proof (C3). The summation statement is a function/cochain assertion, not a degreewise replacement for a derived isomorphism. The parent alone makes the derived comparison, and no per-degree identification was substituted for it. The new definitions' sources are honest WANTED analytic lemmas, not fabricated Stacks citations (B5). No Mathlib match was claimed without a file and line (B6/B8), and every recorded search ran with the precise logged query (B7). The blueprint fields and freshness/duplicate searches are explained above (B9, C5). All parent's proof-dependency fields equal the union of step uses, and every citation is verbatim. The new nodes cite only existing definitions or the completion statement to specify notation and have no dependency on the parent, so there is no cycle (C6).

I tested the small cases for each new statement, not only the final theorem. Averaging: G=1 gives evaluation, finite G gives the finite formula, empty P gives zero, and n=1 gives c=0. Removing the prime-to-ell hypothesis would lose the norm-one bound; removing completeness is allowed only in the finite formula. Components: empty S, a point, finite G, constant z and z lying in a single F_N all work; a compact family with unbounded degrees still has pointwise eventual zero without a common field. Certificates: S empty permits empty partitions; a point has a certificate by Baire on nonempty G^(n+1); G=1 gives a field-membership cover, and even a nonopen A_j is approximated by decreasing unions of shrinking clopen partition atoms. Each smaller invalid index is eventually excluded, only finitely many being smaller than the least valid one; this proves pointwise stabilization without a uniform index. Correction: z=0 gives all zero, n=1 is compatible with d^0=0, a stabilized certificate with N_j=0 is killed once i>=1, and H=G or finite G is allowed when the stipulated operators exist. Fixed evaluations may need different vanishing indices, but their finite maximum suffices. Series: finite-support sequences, empty S, G=1 and n=1 work; the field may be incomplete because every limit value is a finite sum. The norm-null but nonsummable-real sequence 1/(i+1) illustrates why the existing complete-field real-majorant series node does not apply in general.

No parent step exceeds 2000 characters (the parent sum is 2885). I reviewed every long old step by its independent argument and allocated all old steps 2–10 to the five nodes; no single child carries the whole primitive-existence proof. The long new correction statement spells out input hypotheses, not a hidden proof step. The old arguments are reproduced below, including all formulas, bounds, signs, parameter quantifiers and empty-space conventions. Corrections made during self-review: I explicitly typed the H_j as open normal subgroups in the correction node, and used raw strings for TeX so pullback and limit formulas have no accidental tab/control escapes. The item statement is identical to its repository version; there is no statement dispute and no unit/chapter route change. The old null blueprint ancestor and all Lean metadata are retained. This is the requested direct-delivery self-review, not an invented second-reader review.

## What remains

The parent is split relative to five smaller independently actionable statements. Their proofs and exact analytic literature references remain subsequent workers' work, as the explicit re-split brief requires. No portion of the old argument was discarded; the appendix is takeover material for those workers. The required final server dry run and push will supply the delivery receipt.

## Takeover appendix: complete original arguments, without abridgment

The following is the complete returned proof text. It is retained as argument material for the new statement-only nodes, not placed in their proof fields. Original step numbers are preserved for the allocation table above.

### Original step 1

The differential is a finite alternating sum of pullbacks by continuous maps, so it is continuous and $A_F(S)$-linear. The coface relations $\delta_j\delta_i=\delta_i\delta_{j-1}$ for $i<j$ follow from associativity in $K$ (and deleting an endpoint); pairing these equal terms with opposite signs gives $d^2=0$. A function factoring through $(K/U)^n$ retains that property after each face. Intersecting finitely many open normal subgroups provides a common quotient for any finite list of representatives. Thus both complexes and the specified inclusion are defined, and in degree zero they both equal $A_F$ with zero outgoing differential.

Cited nodes: none (elementary).

### Original step 2

Let $L_0^\bullet$ denote the finite-quotient subpresheaf before sheafification. Fix $S$ and $n\geq1$. A cocycle $c\in L_0^n(S)$ factors through $Q=K/U$. Its cocycle equation holds on $Q^{n+1}$ since $K\to Q$ is surjective. Put $m=|Q|$ and
$$b(s;g_1,\ldots,g_{n-1})=(-1)^n m^{-1}\sum_{h\in Q}c(s;g_1,\ldots,g_{n-1},h).$$
This is a continuous finite-quotient cochain. Sum the cocycle equation $(dc)(s;g_1,\ldots,g_n,h)=0$ over $h\in Q$. In the last multiplication term replace $g_nh$ by $h$; the first $n$ terms give $d$ of the unsigned sum, and the endpoint term gives $(-1)^{n+1}m c$. Hence $db=c$. For $n=1$ this equality reads $0=c$, consistent with $d^0=0$. It follows that $H^n(L_0^\bullet(S))=0$ for $n>0$, for both coefficient fields; in degree zero it is $C(S,F)$. Only finite sums and $m^{-1}\in F$ occur.

Cited nodes: none (elementary).

### Original step 3

For finite $F=E$, completeness and the nonarchimedean inequality are supplied by [lem-weil-l-adic-extension-complete] and [lem-weil-l-adic-extension-absolute-value]. Apply [lem-sfb-prime-to-ell-complete-scalar-integral] and put $h_E c=(-1)^n I_K(c(-,h))$ for a degree-$n$ cocycle. Integrating its cocycle equation gives $d h_E c=c$: left translation by $g_n$ handles the penultimate term, and normalization handles the last term, with the sign computed in step 2. The integral's parameter clause proves continuity, and its bound gives $\|h_E c\|_\infty\leq\|c\|_\infty$. This works for every finite intermediate field, not just the originally fixed $E$.

Cited nodes: lem-weil-l-adic-extension-complete, lem-weil-l-adic-extension-absolute-value, lem-sfb-prime-to-ell-complete-scalar-integral.

### Original step 4

Now let $z\in C(S\times K^n,\Omega)$ be a cocycle, $n\geq1$. Apply [lem-sfb-profinite-metric-function-quotients] to its metric-valued function, obtaining $p:S\twoheadrightarrow S_0$, $q:K\twoheadrightarrow G$ and $z_0\in C(S_0\times G^n,\Omega)$. Surjectivity of $p\times q^{n+1}$ shows $dz_0=0$. Every finite quotient of $G$ is a finite quotient of $K$, so has order prime to $\ell$. It suffices to construct a primitive for $z_0$ and pull it back. Hence, for the next steps, write $S,G,z$ for the metrizable quotients and descended cocycle. If $S$ is empty take the unique zero cochain.

Cited nodes: lem-sfb-profinite-metric-function-quotients.

### Original step 5

By [lem-sfb-algcl-countable-closed-finite-cover], choose increasing finite fields $F_i\subseteq\Omega$ covering $\Omega$. For each $i$ choose $p_i:\Omega\to F_i$ by [lem-sfb-norm-one-finite-subfield-projection]. Put $p_{-1}=0$ and $e_i=(p_i-p_{i-1})z$ for $i\geq0$. Each $e_i$ is a continuous $F_i$-valued cocycle, since the projections are $\mathbf Q_\ell$-linear. For each fixed input, $e_i$ is eventually zero: both projections eventually fix its algebraic value. Also $p_i z\to z$ uniformly. Indeed a finite $\epsilon$-net for the compact image of $z$ lies in one $F_N$; for $i\geq N$ the norm-one bound gives $|p_i x-x|\leq\epsilon$ on that image. Consequently $\|e_i\|_\infty\to0$ and $\sum_{i=0}^N e_i=p_Nz$. The projections need not commute with one another.

Cited nodes: lem-sfb-algcl-countable-closed-finite-cover, lem-sfb-norm-one-finite-subfield-projection.

### Original step 6

Put $f(s;g_0,\ldots,g_n)=z(s;g_0^{-1}g_1,\ldots,g_{n-1}^{-1}g_n)$. For every $s$, the inverse images of the closed fields $F_N$ cover the nonempty compact Hausdorff space $G^{n+1}$. By [lem-sfb-baire-closed-cover-interior], one has nonempty interior. A product neighbourhood therein contains a rectangle $Ha_0\times\cdots\times Ha_n$ for an open normal $H$. Metrizability and compactness give a countable clopen basis for $G$ (take finite subcovers at each metric scale); every clopen is a finite union of basis elements. There are therefore only countably many such coset rectangles. Enumerate their pairs with field indices as $(B_j,N_j)_{j\geq1}$. Define
$$A_j=\{s\in S:f(s;B_j)\subseteq F_{N_j}\}.$$
Each $A_j$ is closed, being an intersection of inverse images of $F_{N_j}$ under evaluations, and the Baire argument proves $S=\bigcup_j A_j$. No open neighbourhood of $s$ is claimed to lie in $A_j$.

Cited nodes: lem-sfb-algcl-countable-closed-finite-cover, lem-sfb-baire-closed-cover-interior.

### Original step 7

Choose finite clopen partitions $\mathcal P_i$ of the metrizable profinite $S$, refining one another and with mesh tending to zero. They exist by taking finite clopen refinements of metric-ball covers. Let $U_{j,i}$ be the union of atoms of $\mathcal P_i$ meeting $A_j$. These clopen sets decrease to $A_j$: a point outside the closed $A_j$ is eventually in an atom disjoint from it. Let $k_i(s)$ be the least $j\leq i$ with $s\in U_{j,i}$, or $1$ if none exists; define $k_0=1$. Each $k_i$ is locally constant with finite range. For each $s$, let $j(s)$ be the least index with $s\in A_j$. All smaller indices are eventually excluded from $U_{j,i}$ and $s$ always belongs to $U_{j(s),i}$; hence $k_i(s)=j(s)$ for all sufficiently large $i$. This is eventual stabilization separately at each parameter, with no uniform index or field asserted.

Cited nodes: none (elementary).

### Original step 8

For each rectangle certificate $j$, apply [lem-sfb-bounded-finite-evaluation-rectangle-replacement] to $G,H_j,n,(a_{j,r})$, giving $T_j,R_j$. The index $[G:H_j]$ is prime to $\ell$ because $H_j$ is normal and $G/H_j$ is a finite quotient. Their choices are independent of coefficients. On each clopen piece on which $k_i=j$ is constant, form $r_i(s)=R_j e_i(s)$ and
$$b_i(s)=T_j e_i(s)+h_{F_i}r_i(s).$$
The residual is an $F_i$-valued cocycle, so step 3 supplies its continuous bounded primitive. The finitely many clopen pieces glue these formulas to a continuous $F_i$-valued cochain on $S\times G^{n-1}$. The replacement identity gives $db_i=e_i$, and all three operators have norm bound one; thus $\|b_i\|_\infty\leq\|e_i\|_\infty\to0$.

Cited nodes: lem-sfb-bounded-finite-evaluation-rectangle-replacement, lem-sfb-prime-to-ell-complete-scalar-integral.

### Original step 9

Fix $(s,x)\in S\times G^{n-1}$. Eventually $k_i(s)=j=j(s)$ and $i>N_j$. On $B_j$ one has $f(s,-)\in F_{N_j}$; therefore the homogeneous function of $e_i(s,-)$ vanishes there, since both $p_i,p_{i-1}$ fix that field. The rectangle clause of [lem-sfb-bounded-finite-evaluation-rectangle-replacement] gives $R_j e_i(s)=0$ as a whole cochain. Thus eventually
$$b_i(s,x)=(T_j e_i(s))(x)=\sum_{a=1}^{u_j}\alpha_{j,a}e_i(s,\psi_{j,a}(x)).$$
There are only finitely many evaluations in this formula. At each of their fixed inputs, $e_i$ is eventually zero by step 5. Hence $b_i(s,x)=0$ for all sufficiently large $i$. This proves pointwise finiteness of the primitive series, including the parameter points outside every finite initial union of certificates.

Cited nodes: lem-sfb-bounded-finite-evaluation-rectangle-replacement.

### Original step 10

Use [lem-sfb-normed-field-completion] to view $\Omega$ isometrically in its complete normed field $B$. Its nonarchimedean inequality follows by taking limits of the inequality on finite subextensions. Since $\|b_i\|_\infty\to0$, the ultrametric inequality makes the partial sums uniformly Cauchy on the compact domain: every tail has norm at most $\sup_{i>N}\|b_i\|_\infty$. Completeness gives a uniform limit $b:S\times G^{n-1}\to B$. To check continuity directly, fix a point and $\epsilon>0$, choose a uniformly $\epsilon$-close continuous partial sum, and use continuity of that sum and the ultrametric triangle inequality. Step 9 says each value of $b$ is actually a finite sum in $\Omega$. The subspace metric on $\Omega\subseteq B$ then makes $b$ norm-continuous into $\Omega$. Since $d$ is a finite sum of evaluations, $db=\lim_N d(\sum_{i\leq N}b_i)=\lim_N p_Nz=z$. Pullback as in step 4 proves objectwise positive-degree exactness for every original profinite $S$.

Cited nodes: lem-sfb-normed-field-completion, lem-weil-l-adic-extension-absolute-value.

### Original step 11

Apply [lem-weil-pbc-site-module-presheaf-sheafification-exact] with the constant ring $R=\mathbf Z$, to the underlying abelian presheaf complexes. By step 2 the sheafification of $L_0^\bullet$ has cohomology $A_F$ in degree zero and zero in positive degrees. The continuous-function complex is already a sheaf complex, and steps 3 and 10 say that every positive-degree kernel section lies in the image locally on a cover; its cohomology sheaves therefore vanish. Both complexes are zero in negative degrees. The inclusion is the identity in degree zero by step 1, so it induces isomorphisms on every underlying abelian cohomology sheaf. Kernels are stable submodules and images are the sheafifications of the stable pointwise images; these carry the inherited $A_F$-actions. Consequently the same inclusion induces isomorphisms on module cohomology and is a quasi-isomorphism of internal $A_F$-module complexes.

Cited nodes: lem-weil-pbc-site-module-presheaf-sheafification-exact.

### Original step 12

By [sk-def-sfb-derived-categories], localization at quasi-isomorphisms inverts this specified inclusion, giving the asserted isomorphism in $D(\operatorname{Mod}_{A_F})$. If $S$ is empty all positive-degree section groups are zero. If $K=1$, the alternating differential is zero in even degree and the identity in odd positive degree, giving the same positive-degree acyclicity. Finite $K$ is already covered by the finite formula in step 2. These checks do not require $\Omega$ to be complete.

Cited nodes: sk-def-sfb-derived-categories.

