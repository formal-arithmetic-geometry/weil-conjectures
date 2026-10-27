# Q30 stage-1 repair report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-surjective-two-term-determinant-calculus.json: repaired item, statement unchanged; five assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-two-term-kernel-normalization.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-two-term-normalization-locality-equivariance.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-local-homotopy-unit-determinant-lift.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-acyclic-two-term-flag-determinants.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every cited node in every item step.

## Attachments

None. Searched the live WeilConjectures library for the blueprint tag and determinant/surjection concepts. No project declaration there states all clauses. The Sheaf module Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus contains the exact statement, but its theorem ends with `sorry`; it is not an attachment. No Lean files were written and no compiler was run.

## WANTED

None. All sources used are present.

## Current return: repair of 18f4c3d6227

The current live return entry, dated 2026-10-22 15:24 UTC, identifies returned delivery head 18f4c3d6227. It approves the reader's mathematics and requests a rebase after the side-completion promotion refusal. I retained the delivered packet, all four statements, citations, twenty search records, and the eleven-step proof archive below. The required initial dry run completed successfully at 259d7ce55f8 before I changed this packet.

I compared every item field with the current read-only main DAG. Only proof, proof_deps and split_report differ; the live proof is still the 7106-character eleven-step version and the released keep_plan stage-1 repair note still requests at least two new obligations. All four new ids are still absent from the live DAG. I rebuilt the sandbox item from that current live JSON, overriding only these three repair fields. This retains every current maintainer field. The delivery tool then packages the actual commit on current origin/sheaf-dag. I ran no git commands and wrote only inside the sandbox.

I re-read every existing statement dependency of the five node files, as well as both existing proof citations (the projective lifting definition and the exact-sequence determinant theorem). Their meanings and every citation quote still agree with the retained packet; no changed proposition requires a new mathematical route. The Stacks construction 0FJI, homotopy proof 0FJK and composition hints 0FJL, with the exact-sequence and filtration formulas 0FJB/0FJC/0FJD, still give the same argument. The unchanged new statements retain their exact logged searches and verdicts, including the unavailable LeanSearch request.

This is a proof adjustment as well as a rebase. Assembly step 5 now checks the quotient generator rather than merely saying it agrees: for c:L/N → M induced by a, the chain equation carries the pair (e,d(e)) to (det(c^-1)e,det(d_M)det(c^-1)e). This proves D(c)δ_(L/N)=δ_M. It then evaluates the filtration identity on x as T_a^-1(T_b^-1(x))=T_ba^-1(x) before taking inverses. This makes both the quotient transport and the composition direction explicit without moving any argument out of the four independent obligations. The statement and dependency graph are unchanged.

## Previous return: repair of 35d97215446

The live return entry dated 2026-10-22 11:14 UTC names returned head 35d97215446 and again reports a promotion-related landing refusal, after approving the mathematics. The retained sandbox is the prior delivery packet: its five node files, four independent statements, twenty logged searches and eleven-step proof archive are preserved. The initial dry run in this repair exited successfully at f232e8dfb9e. It established that the current server preflight accepts this packet on its current base; it was not pushed. The final dry run below validates the actual repaired packet.

I compared every retained item field with the current read-only DAG: only proof, proof_deps and split_report differ. In particular the statement, stmt_deps, blueprint, Lean record and existing review metadata agree. The released stage-1 repair order is still present and the current live proof is the old eleven-step argument; all four new ids remain absent. I re-read all current external statement dependencies of the five files, including the exact-sequence construction, lifting characterization, complexes, finite-free cover, exterior algebra and both localization definitions. No statement-level dependency changed meaning relative to the retained packet; every original citation quote remains a verbatim substring of the current statement. I reused the recorded Mathlib searches, whose questions and statements are unchanged. The required delivery command builds on the current origin/sheaf-dag and preserves maintainer-owned fields; no git command was run in the shared read clone.

This repair also changes the assembly itself. Step 4 now writes the three quotient isomorphisms on representatives and checks that the induced quotient map is exactly b, using b(a(p)) in both descriptions. Step 5 cites the exact-sequence wedge formula explicitly to identify the three transported determinant maps, and checks the differential generators are unchanged. This closes the previously implicit comparison between the literal quotients in the flag lemma and the named complexes Q, M and S. I added the corresponding full verbatim quotation to citations.json. The statement and four new obligations remain fixed, and the complete assembly is still under 3000 characters.

## Earlier promotion return: rebase of cface68bcbd

The 2026-10-22 07:25 UTC return approved the mathematics but refused landing because the side completion had not been promoted to the live DAG. I retained the returned delivery's four node files, citations, twenty logged searches, full report and archived eleven-step proof. The initial required dry run completed at 57220cce14d with server preflight passing. This receipt was diagnostic only; the updated packet is dry-run again below before pushing.

Compared the retained item with the current read-only live item: only proof, proof_deps and split_report differed. Its statement, statement dependencies, source, blueprint fields, Lean record and all maintainer metadata agree. The live item still contains the eleven-step proof totaling 7106 characters and has a released stage-1 keep_plan repair note requiring at least two new statement-only nodes and an assembly under 3000 characters. None of this delivery's four new node ids exists in the live DAG. Consequently this is the still-open repair, rather than an attempt to overwrite a completed live split.

I re-read every existing statement dependency and proof citation in the live DAG. The full existing-statement quotations in citations.json still match verbatim: the exact-sequence determinant node includes its kernel-first formula and the empty-wedge case; the projective-module definition includes lifting along surjections. The other proof quotations refer to the retained new nodes. No cited proposition changed meaning and no citation was repointed. I also re-read the derived-complex, exterior-algebra, finite-projective free-cover, and ring/module localization definitions used in the new statements. The earlier logged searches retain their original results and verdicts because neither new statements nor search questions changed.

As a concrete assembly repair I now spell out the bijective quotient maps L/N to M, P/N to Q and P/L to S, and why they commute with the differentials. This removes any implicit quotient-complex identification before applying the filtration node. Each assembly source now gives the precise construction or lemma rather than the same generic list of three tags. The statement and four independent subclaims stay fixed; their arguments and edge-case review below are retained. The delivery command itself builds on the current origin/sheaf-dag and preserves current maintainer-owned fields; I ran no git command in the shared repository and edited only this sandbox.

## Earlier proof-length return and repair

The return required spreading the 7106-character proof into at least two comparably sized statement-only nodes, preserving the statement and all arguments, with at most 3000 characters in the parent assembly. This repair introduces four nodes: kernel construction (old 1/2), locality and equivariance (old 4/8), local homotopy lift (old 5/6/7), and acyclic filtration compatibility (old 9/10/11). Old step 3 stays in the parent. The elementary kernel exact-sequence check from old step 9 also remains explicitly in assembly step 4. The exact original text of all eleven steps is retained below for the next workers. The four nodes have empty proof and proof_deps, null proof_origin, and status unsplit. They have independent statements and do not assume or cite the parent theorem. The parent no longer hides the inverse, equivariance or filtration arguments inline.

The supplied sandbox initially contained only dispatcher .brief files, no prior node files, report or searches.jsonl. Therefore the current shared item, which has exactly the eleven lengths described in the return, was copied without git and used as the returned baseline. Existing metadata, citations and Mathlib searches in that item are preserved; the only item changes are proof, proof_deps, status and split_report. No claim about a git branch was inferred. A final byte comparison verifies its statement is unchanged.

## Literature and search review

Read more-algebra.tex lines 36283–36453 and 36920–37122: Tags 0FJB (lemma-det-ses), 0FJC (lemma-det-ses-functorial), 0FJD (lemma-det-filtration), 0FJF (lemma-det-switch), 0FJI (section-determinants-complexes), 0FJK (lemma-homotopic-surjections), and 0FJL (lemma-compose-surjections). Read the chapter/unit records and the current main-20261015 local-term-locality blueprint text. The inherited blueprint path locates this algebraic auxiliary through the semistable/dualizing branch; no unit or chapter route is changed. This uses no SGA source.

Before creation searched the entire DAG by the determinant, homotopy, localization and filtration concepts and by Tags 0FJI/0FJK/0FJL/0FJC/0FJD, and searched the whole imported blueprint with blueprint_refs search determinant, homotop, acyclic, filtration, surjection. The ancestor command confirms lem-trf-local-term-locality; each new via list prepends this item. No blueprint statement supplies these algebraic subclaims.

For every new node ran leanfinder with two phrasings, leansearch, loogle, and Mathlib grep through msearch.py; exact logged queries and digests are in searches.jsonl and the node records. The kernel-construction LeanSearch attempt was rate-limited and is honestly recorded unavailable; the two LeanFinder searches, Loogle and grep succeeded. Read the returned types: projective resolution quasi-isomorphisms, homotopies, localized kernels, exterior-power naturality, and scalar determinant multiplicativity lack the claimed determinant-line construction. Read Mathlib LinearAlgebra/Matrix/SchurComplement.lean:401 (rectangular switch), LinearAlgebra/Determinant.lean:392 (det_pi), and LinearAlgebra/SymplecticGroup.lean:386 (matrix determinant detected locally). None states a new node. The rectangular switch remains the existing Mathlib leaf, rather than a duplicate new leaf.

## Not duplicates

- lem-trf-acyclic-two-term-flag-determinants vs lem-trf-affine-two-term-determinant: the existing affine-system existence theorem is downstream of this parent and does not specify the two nested kernel-first wedge identities; the new node states only filtration associativity and the differential-generator formula for an explicit flag of module complexes.
- lem-trf-local-homotopy-unit-determinant-lift vs lem-trf-rectangular-determinant-switch: the existing Mathlib leaf supplies det(1+AB)=det(1+BA) for given matrices; the new node constructs a simultaneous complement, a homotopy lift and an invertible chain automorphism with explicit inverse. Its determinant equality will use that existing leaf, which does not construct any of these objects.
- lem-trf-two-term-kernel-normalization vs def-trf-projective-determinant-module: the existing node defines a module inside an exterior algebra but asserts no kernel projectivity, acyclicity, generator or normalized isomorphism. The new node asserts these properties for a surjective two-term quasi-isomorphism using that same determinant line.
- lem-trf-two-term-kernel-normalization vs lem-trf-projective-determinant-exact-sequence: the existing node constructs a determinant isomorphism for one short exact sequence of modules; the new node proves the two-term kernel is projective with invertible differential and that its differential trivializes the tensor determinant, defining an inverse map for the complex. It cites the existing exact-sequence construction and does not duplicate it.
- lem-trf-two-term-kernel-normalization vs lem-trf-affine-two-term-determinant: the existing affine system theorem assumes the whole surjective calculus downstream; this new node states only construction of the kernel-normalized determinant isomorphism and cannot cite the downstream theorem without a cycle.
- lem-trf-two-term-kernel-normalization vs lem-trf-surjective-two-term-determinant-calculus: the parent states the complete identity/homotopy/composition calculus; this new node isolates construction of the kernel-normalized determinant isomorphism and gives extra construction/compatibility data, not the complete calculus.
- lem-trf-two-term-kernel-normalization vs lem-trf-two-term-perfect-determinant: the existing theorem is a global derived determinant functor, downstream of the parent; this new node is the explicit module-level construction of the kernel-normalized determinant isomorphism.
- lem-trf-two-term-kernel-normalization vs def-trf-two-term-determinant-data: the existing node defines global sheaf comparison data and asserts no affine existence or normalized wedge identities; this node proves construction of the kernel-normalized determinant isomorphism.
- lem-trf-two-term-normalization-locality-equivariance vs lem-trf-affine-two-term-determinant: the existing affine system theorem assumes the whole surjective calculus downstream; this new node states only localization and equivariance of kernel-normalized determinant maps and cannot cite the downstream theorem without a cycle.
- lem-trf-two-term-normalization-locality-equivariance vs lem-trf-local-common-summand-surjections: the existing node supplies only a simultaneous complement for two finite free surjections; it does not assert localization and equivariance of kernel-normalized determinant maps.
- lem-trf-two-term-normalization-locality-equivariance vs lem-trf-surjective-two-term-determinant-calculus: the parent states the complete identity/homotopy/composition calculus; this new node isolates localization and equivariance of kernel-normalized determinant maps and gives extra construction/compatibility data, not the complete calculus.
- lem-trf-two-term-normalization-locality-equivariance vs lem-trf-two-term-perfect-determinant: the existing theorem is a global derived determinant functor, downstream of the parent; this new node is the explicit module-level localization and equivariance of kernel-normalized determinant maps.
- lem-trf-two-term-normalization-locality-equivariance vs def-trf-two-term-determinant-data: the existing node defines global sheaf comparison data and asserts no affine existence or normalized wedge identities; this node proves localization and equivariance of kernel-normalized determinant maps.
- lem-trf-local-homotopy-unit-determinant-lift vs lem-trf-local-common-summand-surjections: the existing node supplies only a simultaneous complement for two finite free surjections; it does not assert a determinant-trivial chain automorphism lifting a local homotopy.
- lem-trf-local-homotopy-unit-determinant-lift vs lem-trf-surjective-two-term-determinant-calculus: the parent states the complete identity/homotopy/composition calculus; this new node isolates a determinant-trivial chain automorphism lifting a local homotopy and gives extra construction/compatibility data, not the complete calculus.
- lem-trf-acyclic-two-term-flag-determinants vs lem-trf-surjective-two-term-determinant-calculus: the parent states the complete identity/homotopy/composition calculus; this new node isolates determinants and acyclic trivializations along a two-term filtration and gives extra construction/compatibility data, not the complete calculus.

Additional concept overlaps checked: lem-trf-projective-determinant-exact-sequence constructs the termwise wedge map only (no acyclic differential, inverse T, chain-isomorphism square or filtration coherence); lem-trf-rectangular-determinant-switch gives one scalar equality, not the existence of a lift; lem-sc-exterior-top-direct-sum treats only a single free direct sum; new-determinant-split-local treats sheaf charts and one exact sequence. lem-sfb-two-term-cofactor-naturality is downstream and concerns a different map out of H^0 for rank-difference-one complexes. lem-trf-k0-determinant-map concerns isomorphism classes in Pic, not specified line isomorphisms. None supplies one of the new statements or a more general statement specializing to it.

## Review by Q30

For the current return on 18f4c3d6227 I re-read all statements from the current live DAG, the retained new-node statements, and the Stacks sources named above. Step 1 takes the exact kernel construction from the normalization statement; step 2 uses the empty-wedge clause of the exact-sequence statement. Step 3 uses the locality/equivariance statement and the local homotopy lift with precisely finite free terms over the prime-local ring. Step 4 verifies surjectivity, finite projective kernels and the three quotient chain isomorphisms, with splitting justified by the projective lifting characterization. Step 5 uses both flag identities and the kernel-first wedge formula. The new quotient-generator calculation checks the commutative differential square on a wedge and its image, so it also applies to rank zero via the empty wedge. The resulting inverse-map identity has domain D(S) and codomain D(P), giving the stated forward composition after inversion. All eight step/node citation pairs still have full verbatim quotes. I checked the zero-ring, rank-zero, characteristic-two and varying-rank cases again against this assembly: no new hypotheses, sign or statement correction is introduced. All four new files remain statement-only; no new Mathlib question arose and no search was repeated or invented. All assembly steps are below 2000 characters, and their total remains below 3000.

For the 11:14 UTC return on 35d97215446 I repeated the live-field and citation comparisons described above. For composition I checked the canonical quotient maps on representatives: their kernels are exactly N or L, their differentials commute by the chain equations, and the induced Q to S map is b. The exact-sequence node explicitly supplies the ordered kernel-first wedge formula, so applying a quotient isomorphism changes neither its kernel basis nor its chosen quotient lifts. This is precisely the extra statement used in revised step 5, and its new full quote is verified verbatim. The flags have finite projective subquotients by the kernel construction and projectivity hypotheses already checked. No source route or statement changed.

I read the displayed Stacks construction before 0FJJ for the item and kernel-normalization node. It specifies the same determinant direction: inserting the differential generator maps D(Q) to D(P), and T is its inverse. The module lifting characterization supplies the degreewise sections; a direct summand of a finite free module is still finite projective. The H^-1 injectivity/H^0 injectivity/H^-1 surjectivity element chase in old step 1 proves the kernel differential is invertible without assuming either original differential injective. This entire argument is the first new obligation, together with old step 2's invertible-line generator construction.

For locality/equivariance I read the first and final paragraphs of 0FJK and the exact commuting determinant square of 0FJC. The new statement requires isomorphisms in both outer squares, so the kernel restriction really is an isomorphism and its differential commutes. It gives all three identities used by assembly step 3, including T_a D(u)=D(v) T_a'. Localization is restricted to the stated split exact sequences, so kernels and differentials really localize; all finite projectives are free at primes. Equality detection is asserted for arbitrary module maps, including the zero-ring case. The retained old argument gives its annihilator proof. A local ring here has one maximal ideal and excludes the zero ring, which causes no gap because the zero ring has no primes and all its modules are zero.

For the local-homotopy node I read the common-summand construction and the triangular-map argument in 0FJK and the switch of 0FJF. The statement uses finite free terms over a local ring, exactly after assembly step 3's localization. No quasi-isomorphism is needed for this smaller lift: a shared negative-degree complement gives the triangular inverse directly; 1-d_P w t is a two-sided inverse for 1+d_P t. The equal determinants force the action on D(P), not either individual determinant, to be one. This node retains old steps 5/6/7 including their explicit inverse formulas. It does not restate homotopy invariance of T. The already-existing common-summand lemma and rectangular-switch leaf remain available for the next worker, rather than being duplicated.

For the filtration node I read 0FJL's omitted proof together with the actual 0FJD diagram and 0FJC. All six complexes and both quotient identifications are introduced, all terms are finite projective, and acyclicity is explicitly the invertibility of N,M,L differentials. Both iterated wedges have the order N then M then S in each degree. Ordinary tensor symmetry, not a graded commutation convention, defines the displayed maps. The differential generator identity compares degree -1 bases and their degree 0 images. This retains the substantive content of old steps 9/10/11, including their local-to-global and empty-wedge checks, as the fourth new obligation. No assertion of determinant functoriality in the derived category is assumed.

I re-read each parent citation against its statement. Assembly step 1 uses the new kernel-normalization node for the split kernels, differential and actual inverse construction. Step 2 uses the existing exact-sequence node's displayed kernel-first formula, which expressly includes zero kernel rank; empty wedges give identity. Step 3 uses the new locality/equivariance statement for prime-local equality detection, finite free terms and the commuting square; the new local-homotopy statement supplies exactly ak=b and D(k)=1. Step 4 uses the construction node for finite projective kernels of a,b,ba and the projective definition's lifting characterization to split L→M. Its direct element lift verifies the exact sequence. In this rebase repair I made the induced quotient maps and their compatibility with differentials explicit; neither assertion is inferred from a definition alone. Step 5 uses the two displayed filtration identities and the already defined inverse maps; substituting the differential generators proves composition with the correct direction. citations.json records the full verbatim cited statements for every use, so both the localization and equivariance facts, the lift factorization and determinant identity, and both filtration formulas are visible. Every non-elementary assertion in assembly is now a cited statement. The new nodes' statements do not depend on the parent, so no cycle is introduced.

I checked rank-zero targets (U=0, h=0), zero complex, identity, contractible [R→R], zero ring, characteristic two and nonconstant local ranks. In the scalar contractible case the normalized map is the ratio of term determinants; composition and the equivariance formula have the stated orientation. The triangular inverse works even for non-Noetherian local rings and requires no surjective-endomorphism finiteness shortcut. No statement correction was necessary. I also checked B–E: every new node is statement-only and self-contained; sources name verified Stacks tags/labels; every recorded search was run; no duplicate node is created for a Mathlib scalar identity; the four new nodes divide separate arguments rather than move all work into one new theorem. No parent step exceeds 2000 characters and the total is under 3000.

## Coverage of the returned proof: preserved arguments

The following text is the returned proof, verbatim, retained as handoff material rather than inserted into the statement-only nodes. The old citations remain useful to the workers splitting those nodes. This archive ensures none of the former proof has been shortened or dropped.

### Old step 1 → lem-trf-two-term-kernel-normalization

The lifting characterization in [def-weil-pbc-projective-module] gives sections of each $a^i$; thus $P^i=N^i\oplus Q^i$. If $P^i\oplus E$ is finite free, then $N^i\oplus(Q^i\oplus E)$ is that same finite free module, so $N^i$ is finite projective. Check $d_N$ directly using the cohomology definition in [def-weil-abstract-derived-category]. A kernel element killed by $d_N$ is a cycle of $P^{-1}$ killed by $H^{-1}(a)$, hence zero (there are no degree $-2$ boundaries). For $y\in N^0$, injectivity of $H^0(a)$ implies $y=d_Px$. The element $a^{-1}x$ is a cycle of $Q^{-1}$. Surjectivity of $H^{-1}(a)$ gives a cycle $z\in P^{-1}$ with $a^{-1}z=a^{-1}x$. Then $x-z\in N^{-1}$ and $d_N(x-z)=y$. Thus $d_N$ is bijective.

Cited statements: def-weil-pbc-projective-module, def-weil-abstract-derived-category. Source: Tag 0FJI, construction for surjective quasi-isomorphisms: kernel projectivity and acyclicity.

### Old step 2 → lem-trf-two-term-kernel-normalization

Apply [lem-trf-projective-determinant-exact-sequence] to the two split exact sequences of Step 1. Its maps are exactly the prescribed $\gamma^i$, with kernel wedges first. Their tensor product, inverse dual in degree $-1$, and ordinary tensor symmetry give $\Gamma_a$. The same node makes the determinant modules invertible; the top exterior map of $d_N$ is an isomorphism of these lines. Under $\operatorname{Hom}(\det N^{-1},\det N^0)=\det N^0\otimes(\det N^{-1})^\vee$, this is a generator $\delta_N$ of $D(N)$. Indeed locally a basis wedge is taken to a basis wedge; its tensor with the dual source wedge is a generator. Inserting this generator in $\Gamma_a$ is an isomorphism $D(Q)\to D(P)$, whose inverse is the stated $T_a$.

Cited statements: lem-trf-projective-determinant-exact-sequence. Source: Tag 0FJI, defining triangle for det(a); Tag 0FJB (lemma-det-ses).

### Old step 3 → parent assembly step 2

For $a=\mathrm{id}_P$, its kernel is the zero complex, $D(N)=R$ and $\delta_N=1$. The wedge formula has empty kernel wedge and leaves each quotient wedge unchanged. Hence $\Gamma_a(x\otimes1)=x$ and $T_a=1$.

Cited statements: . Source: Tag 0FJI, zero-kernel case of the definition.

### Old step 4 → lem-trf-two-term-normalization-locality-equivariance

For homotopy invariance we may compute at every prime of $R$. The split sequences of Step 1 stay split after localization (apply the same projection and section), and their kernels and differentials are therefore the localized ones. Wedge products, duals of rank-one projectives, and their evaluation maps localize by their basis formulas. Thus $\Gamma_a$, $\delta_N$ and $T_a$ localize to the same construction. By [lem-weil-pbc-finite-projective-standard-free-cover], all the terms are finite free at each prime: choose a covering element outside that prime and then localize its free basis. Equality there detects equality globally: if an element $y$ in the image of the difference of two maps were nonzero, its proper annihilator would lie in a maximal ideal $\mathfrak m$; $y/1=0$ at $\mathfrak m$ would give $sy=0$ for $s\notin\mathfrak m$, a contradiction. For the zero ring all modules are zero and equality is immediate.

Cited statements: lem-weil-pbc-finite-projective-standard-free-cover. Source: Tag 0FJK (lemma-homotopic-surjections), final paragraph, localization reduction.

### Old step 5 → lem-trf-local-homotopy-unit-determinant-lift

Work over one such local ring. Apply [lem-trf-local-common-summand-surjections] to $a^{-1},b^{-1}:P^{-1}\to Q^{-1}$ in chosen finite bases. It gives $U\subseteq P^{-1}$ on which both maps are isomorphisms, including when the target has rank zero. Let $s:Q^{-1}\to U\subseteq P^{-1}$ be the inverse of $a^{-1}|_U$ and put $t=sh:P^0\to P^{-1}$. Then $a^{-1}t=h$.

Cited statements: lem-trf-local-common-summand-surjections. Source: Tag 0FJK, second and final paragraphs.

### Old step 6 → lem-trf-local-homotopy-unit-determinant-lift

Put $k^{-1}=1+td_P$ and $k^0=1+d_Pt$. The equations $k^0d_P=d_Pk^{-1}$, $a^{-1}k^{-1}=b^{-1}$, and $a^0k^0=b^0$ follow by expansion and the chain-map equation for $a$. The map $k^{-1}$ is invertible without a finiteness-of-ring assumption: in $P^{-1}=\ker a^{-1}\oplus U$ its matrix is $\left(\begin{smallmatrix}1&0\\ C&B\end{smallmatrix}\right)$, where $B=(a^{-1}|_U)^{-1}(b^{-1}|_U)$ is invertible. Its inverse is $\left(\begin{smallmatrix}1&0\\-B^{-1}C&B^{-1}\end{smallmatrix}\right)$. Write $v=(1+td_P)^{-1}$. An inverse for $k^0$ is $1-d_Pvt$: both products equal $1$, using $v+vtd_P=1=v+td_Pv$. Hence $k$ is a chain isomorphism and restricts to an isomorphism $c:N_b\to N_a$ because $ak=b$.

Cited statements: . Source: Tag 0FJK, first two paragraphs; explicit inverse calculation for the chosen lift.

### Old step 7 → lem-trf-local-homotopy-unit-determinant-lift

In local bases let $A$ be the matrix of $d_P$ and $B$ the matrix of $t$. By [lem-trf-rectangular-determinant-switch], $\det(k^0)=\det(1+AB)=\det(1+BA)=\det(k^{-1})$. Both scalars are units since $k$ is invertible. Consequently the map $D(k)=\det(k^0)\otimes\det(k^{-1})^{-\vee}$ on $D(P)$ is multiplication by their ratio, hence is the identity.

Cited statements: lem-trf-rectangular-determinant-switch. Source: Tag 0FJK, first paragraph, using Tag 0FJF (lemma-det-switch).

### Old step 8 → lem-trf-two-term-normalization-locality-equivariance

Use the wedge formula of [lem-trf-projective-determinant-exact-sequence] in the diagram with kernel map $c^i$, middle map $k^i$, and quotient map $1$. Applying $k^i$ to a kernel wedge followed by quotient lifts gives the wedge of $c^i$ applied to that kernel basis followed by the images of those lifts, still lifts of the same quotient basis. Thus $\det(k^i)\gamma_b^i=\gamma_a^i(\det(c^i)\otimes1)$. Also $c^0d_{N_b}=d_{N_a}c^{-1}$, so taking exterior powers gives $D(c)\delta_{N_b}=\delta_{N_a}$. Tensor the first equality in the two degrees, inverse-dualizing degree $-1$: $D(k)\Gamma_b(x\otimes\delta_{N_b})=\Gamma_a(x\otimes\delta_{N_a})$. Step 7 makes $D(k)=1$, so $T_b^{-1}=T_a^{-1}$. Step 4 gives $T_b=T_a$ over $R$.

Cited statements: lem-trf-projective-determinant-exact-sequence. Source: Tag 0FJK, first paragraph; the wedge naturality of Tag 0FJC (lemma-det-ses-functorial), verified here on generators.

### Old step 9 → lem-trf-acyclic-two-term-flag-determinants (with the kernel-sequence check also in parent assembly step 4)

For composition put $N=\ker a$, $M=\ker b$, $L=\ker(ba)$. The composite is degreewise surjective and a quasi-isomorphism, since its cohomology maps are compositions of isomorphisms. Thus Step 1 applies to all three kernels. In each degree, $a$ gives an exact sequence $0\to N^i\to L^i\to M^i\to0$: to lift $m\in M^i$ lift it along $a^i$; that lift belongs to $L^i$ since $b^im=0$. These sequences split by [def-weil-pbc-projective-module] since $M^i$ is projective. Let $\eta^i:\det N^i\otimes\det M^i\to\det L^i$ be their wedge maps. Let $\Xi:D(M)\otimes D(N)\to D(L)$ be obtained from $\eta^0$ and its inverse dual in degree $-1$, using ordinary tensor symmetry just as for $\Gamma$.

Cited statements: def-weil-pbc-projective-module, lem-trf-projective-determinant-exact-sequence. Source: Tag 0FJL (lemma-compose-surjections), kernel exact sequences implicit in its hints.

### Old step 10 → lem-trf-acyclic-two-term-flag-determinants

The three kernel differentials are isomorphisms and give an isomorphism between the exact sequences of Step 9. Choose bases $n$ of $N^{-1}$ and $m$ of $M^{-1}$ and lifts $\widetilde m$ in $L^{-1}$. Their degree-zero images $d_Nn,d_Mm,d_L\widetilde m$ are corresponding bases and lifts. The wedge of $d_Nn$ followed by $d_L\widetilde m$ is the image by $\det(d_L)$ of the wedge of $n$ followed by $\widetilde m$. Evaluating on these generators gives $\Xi(\delta_M\otimes\delta_N)=\delta_L$. This calculation holds on every simultaneous free localization and hence globally by Step 4's detection argument; the empty wedges give the same formula in rank zero.

Cited statements: lem-trf-projective-determinant-exact-sequence. Source: Tag 0FJL, compatibility of the acyclic-kernel trivializations; wedge naturality as in Tag 0FJC.

### Old step 11 → lem-trf-acyclic-two-term-flag-determinants

For each degree use the filtration $N^i\subset L^i\subset P^i$, with successive quotients $M^i,S^i$. Choose local bases $n,m,s$ and choose lifts of $m$ into $L^i$ and of $s$ into $P^i$. Their images in $Q^i$ are lifts of $s$ for $b^i$. Applying first the wedge map for $b^i$ then for $a^i$, or first $\eta^i$ then the map for $(ba)^i$, sends these tensors to the identical ordered wedge $n\wedge\widetilde m\wedge\widetilde s$. Thus these termwise maps agree. Tensoring the degree-zero equality with the inverse dual of the degree-minus-one equality, and using only ordinary tensor symmetry, yields
$$\Gamma_a\bigl(\Gamma_b(x\otimes z_M)\otimes z_N\bigr)=\Gamma_{ba}\bigl(x\otimes\Xi(z_M\otimes z_N)\bigr).$$
Put $z_M=\delta_M$, $z_N=\delta_N$ and use Step 10. The equality becomes $T_a^{-1}T_b^{-1}(x)=T_{ba}^{-1}(x)$, so $T_{ba}=T_bT_a$. The wedge computation also proves compatibility on overlaps, and Step 4 detects the displayed equality globally. All kernel orders are identical in both degrees; there is no graded tensor switch and no extra sign.

Cited statements: lem-trf-projective-determinant-exact-sequence. Source: Tag 0FJL (lemma-compose-surjections); explicit calculation of the omitted filtration step, Tag 0FJD (lemma-det-filtration).

## Unfinished work

The four new nodes are deliberately unsplit, for parallel assignment as the return requests. No mathematical gap in the parent assembly remains; their proofs are the explicit obligations preserved above. Delivery validation is recorded after the dry run.

## Validation repairs

The first dry run requested four additional explicit same-tag comparisons; these were added under Not duplicates after comparing the already-read statements. The next dry run rejected the short equivariance-only quote. Every citation entry now quotes the entire cited statement verbatim, displaying all claims used in that step. No mathematical statement or proof was changed by these documentation repairs.

## Previous validation

Initial diagnostic dry run for this repair: OK at f232e8dfb9e, process exited before any further invocation. After the explicit quotient and wedge-comparison repair, the final dry run and push are run sequentially; their terminal results are the delivery receipts.

## Latest validation

Initial diagnostic dry run for the 18f4c3d6227 return: OK at 259d7ce55f8; the process exited successfully before the repair was written. The updated packet is submitted to the final dry run and push sequentially; their terminal receipts identify the validated delivery.
